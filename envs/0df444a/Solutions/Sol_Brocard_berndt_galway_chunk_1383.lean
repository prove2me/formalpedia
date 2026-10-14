-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1383
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:41:59.338877+00:00
-- url     : https://prove2.me/submissions/4613988f-f597-4900-8f21-26629fda5a45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 248561151 ≤ n < 248741007 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 248562401 1250 248561151 248561167
    0x503060f010f05210103021801060c02011d18060108071106010504091a0702010b09060a0506090d060219080a0e0a05032226070e100506091207080f0d030501030b0a02 73
    0x244007503a0f0703e92000000700018041450f84c01002502c02c0c00706038899810306005251150202e2109030682d04155100b05a2284a40c010750f0b08030440740c03035000e0341d4003441029a0903072680000c00c0c58450071800c4d41c0d030443c20308000242428002803e00c40c100901c10303250901e9070b400082c512341114000d840000b04403d1a04000111900380e041c040c03030304a180000d00011030340c150460302603581c040302c85000380d0b200d0710304010b40341c061031207800e42065091107144514039109042c00005401450090b2800345590741402a609003017170b003000414040014807240303040610078040d900703180500500d1329600e140c864913070383c1c01440c00410001404c19441c403010150311b80c48000274101403000b90701402c10021252001c1c0038940b9443d49a1107029400102c076000e02500d580910740b10841039500605000a0103a0703607205046142c0c0041e680344000c208503a041040c0c10081403100d001d001e14804407010181403003104000441018280001031010540c080d042540083c0342c5040180e8070034032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 248563651 1250 248562401 248562407
    0x270102040801060806040302010c1d0d0f0204020a0314100b030c0c0a02060d06080d090f0909020a050a1202030d020105040305090906010c0c0e150301060b0703050f040e0c070b070503060f010f 84
    0x3681c0050003075508002c00040d03a00c0002813010301403881f03600244549400424100c2e0030100d080386170140600000311400440c103001014240c000d000c0c1d01010b8109000da0080381c26640000e00a800096440042c1c0711811030081c5029004050300d040844414a8070342c40d04003602001d272091003034000020300906812810000d0007256035014000b20703102c15410b1502c100a215512074001d545c081c070341003003510910680ea002e09444ea4604101c00c00b90070418024004d02403458100d821416400020406988540405006040761078a4400c502d400b8810306041038801004003041da030503c1d00b80000250440203840443c5020b07244102550b6540f4012203080d5181c3c940940340c00780002c00862813003150318040e841401030300b002214507108501414200d80c3daa00c80d60824410a000200009200300c0040c070070350940100c41802c081e140d0f107421165101c25241400349980c006001002c1040090b455603205c20181446070035441c1c000c010415a4003008030060410058070344026000780 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 248564901 1250 248563651 248563657
    0xe0703060e1f0c09090f14040615210b041a0411090105030304080318040605100f1709190305220806010906080d05070201120f091703270102 62
    0x60000d0003802961440d90a1940310340e03103201e02c030b07140ea075400d42c0c41002106603010360102c010969403003a03501880d01030301074001c02074000903421040d10b4680b610780f46104214402e0141d0b0084100260700524540100c07d52002035000d840300343c0c10741412102340c081014041c0065604000700b13843c4c44c0c0d1985040107000c2502001c0b010740c000e1a109001c14006404240144198161144941c5980344c808040c1d0340d0003688900d0205610412541e03002d000e040c104101d2000000c1d1002c501a0f84a10000d0700b010000f00e442c0000900003582c141e09031380e03c105866241d4859464034002d5040800c000c54950703a030300700360385c900101c640f01034070401d8403800880b4401c0240101000c00c9500c03181c07101b903a9080c00d11542d500e61217450001300340440c241c800d22040701c60030001012006e41080b4262001d4201d40c406074144800381d0038000802883d402100690941d064002a010f042c03460700c861a0180e0001710890708500b4000c000d04100b031141e81451f004092981e02c00380781804424240644 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 248566151 1250 248564901 248564903
    0x3120409060920130f1205070b09330f030f0105090415090201020703080c0a0c050603090304050108090c030703060e0d0908030906090621010302011412060909010207060c11071202060a030e0703 85
    0x405c0035400a07a01c2d580302040c02041b84a00c081e82c0740b2a544c1c55202100c0e004140ba103907400f028440030504003500c80503210f0b1401a0211610315000106200540103400075224030407605000010030001c030141c0c59145001d0304045441c0541400d05403150200c0c101280822000c40f96589510700a580c003c00c001da0007541c0c8a1603040e03482e84040240354840180c400200c030b10f80d0380300d0000b0a0520302070094038450300c0c3d1a001541401d07e820011103080b40044c0010606d8020400d07216a191801d0000c0d501841c040e030130100310540d0b00b6805514000090031040300f000056482400441408011944c030460100e0310f60b0380b5405c0c02000500c0c10700c00c42c0a10724070030042d0701080b10301e900c0410b03480b412030f4000d888510003601001d0300c0801c0f0340b06d40e0008030f5480056038001000380c50a9402250452121070005003044103c3e541d0200b04c91422181801241202107000c0e5540d80800440c2c01402c50844d86210750780540d40130981c4c03802500c81d800141078442c001c0d86661442000008021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 248567401 1250 248566151 248566169
    0x706020904051501031107080315060c010f0920090115111c0807210203070c050a050c0a171504020418121d09040201030507030b0312040906092013 65
    0x150a000f2101142820310301e10082c0864185a0600743e100c8001703044d120450313040000d8502d1640c545a950760b004080400c400d038018014000b080c175443c02445401241c4209101c001540b010b2401c02401e00040359050b0080410380f40780f054190344175142450304403541c10300780c1000180f840006031450002840381142ca842540140002d541010700d00c07128400c1a5210491181c45000044400c101c40340310f1054100711001101c050044140d005642c007160b9851b1010141105517503190800c20654000c3e0390a0740724400740d130740034179000c10303840b0081c90b0107448045581994142241c0341c8500403100844802000009420364559801c002e040c0c9004101040c2c82c00100e20744201d40c0920100c030300c00007401102c143c0b2040e5203e504044c0084400800142007965280e0044024160043c556002c260f01c030a844886a142001032400e6540240c5c0559107071400e0000e00710407206140c1c85602c12500b040c504040000c0104038980c018030303000303102d030f580c400041c060f461000d20158008800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 248568651 1250 248567401 248567411
    0x906030f0d08191503170f03090312152b290a02070c03080d09050105161707170c19030207110f010906031d03040303180815040204020706020904 64
    0x22a0351003110980310710f050443c0c43c890000c604030440121607495540e42041e00b1081c00c14030205075a0f081c0300f40c001c1c8200700c1c02031600c1800e96017002c554005a504d08810381c40469000303c2100c841060307580c0070f161555491300d120501d0001031f210114180301210804100e00e2605003a80b4256064404280c000680c420002d80406441c503600010f84805032000c1c26010100702600694000c540e0525003001c4002d03809030454543c2803007540402014a0a50741e0b82c450030000500070b008003442400c8610014041406010001c0c01004c032141501524003031100800c88104d4120141c40b0314000340410850003690364131401c049510450a1207106a205540d19480070343e80364004008503881298503600c46242c250500103500c100c1180540411050041808081d100e6030000d17141461144460311040200e01d80076046030702c150801e078005501c0c2601550100307602500040101403200003000328080203120303100c0c000000b9100038032454000803020300b40200b90701607034602c044c000c00801c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 248569901 1250 248568651 248568673
    0xf0a02030717130806061302030c090a0f14010915080718030f142d0c0a08060601082217120f0403030c0f09140301060e0406020c010f0204050f0906030f 67
    0x60a40c01480f0300e0035158004402c0440c4d40c00f008924903000352806049002480c03018100d80c0044e400c010003140c02c8060a10100312160b4a800c800d02c010701403280151602c0d4281102c139808242c00044d9541440200070742049210114442d0111001140c603241d13185440b680d8084480074540c9070b00c240c0f44140c0c03000120071300c4258018840b0040c807448007000d40083c68600c1640303503030071079404981a07038122fa00803e2004504051845e00e20402d0143c501d0050904000340c01ea440030b8002030300591001c1c0400001c0e50304848400d41210f141502c5e4100f11900007035802810706410030003414041c82d680c5104200d4000c106072455107503c45404646442c190191a0b4808030444041c0c00190504c00e1204250780290b100c00d401c400700c0e90381e2a900a050869806030701054180c010b800d0341d642c00c000940c10010354901400365100341000340e941c40804507a9401c2d60340805e138003a03805104010800283da034031480240c40c9902601d03401d2055131102c1c0085d0800010070441d51071800f0307041e0218 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 248571151 1250 248569901 248569943
    0x609110405130b09090d1b020f01030c0210060b030f0105010e0904030c020a030c060206041a090d1103041a0d0b0a0f0303030b130e0309041a01020d1d10090602011406060f0a020307 79
    0x46044281070380d44004c0c4200140d0003e95a0450b187c02a4204884114504295209410514000d20341d4011118484484804442214599402403907403040100900c00c0526030459082c1c0100070034a000c0f0406d03d4910001008030901a00060511610101540454031030b0b013400d1004542207040c02c0c54481d601d24002e0340724003044030b040347d900c480d405aa080030034442d01d00c0c6000300c0300b40000700b048203907405050740d00c00345c45405075144d84014400010011500c17040c00403480308036162161a80ea9603a4a001958141d040035442201444030610042ea40d0251b440c0441c3e4040c80c02140404e503050100e0400011240150070442c1042000030407030000000510003940180d0341003140d1a88800b501c2c1c0784200444485005800c100c054000300c621545c85518450340360b441703001c0818145400201a103081c140c6200100d080b4020400240390207201c2d910ac0e2401c43c0c101c580d000d140000016000d88900c05004c07003403500116078500100c0c0b080081c0d80100c0c0e8002041042d6220310000c02c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 248572401 1250 248571151 248571163
    0xb0c070f1401031d0c13020c0a050f0f01060e07050706020c0a08041802030108030a0e032e11031b0d0b03010f0b04110c0604060207030c0210090305010609110405130b0909 75
    0x50781c086420b040182c280d45032900302845102079050050100c03000c0c400104103004400d80f040b0701d06a602805401c4801e281400003201c4940f040004207035000040809906040c20002d60103140e03450304404201242d040840300c1c2d80070b88a07107411641e48245142940c0280140c00b42440103104808101c1c0402011a00401c1680d031300c041d00c41600e184000c100c8060344801d0003890015007041c011441a03900509142036051001011356010445064800d0100348910581e080310034688070310300c0c0c2d04070140c0c41500e154144205860745146008849409904101208404000b030f0004401e05900030702c0d400031450542c0200217114540d01001041c0150900c1d80320507200720300d0860950705124850049600c540505005400142c3d00e0340c54100007508042c00980901807580000307030040ea80d44100b020f102a1a0700c52529003811401c005084608503081003000072729046a9100c0c81c942542502c0c22594100ea000d00d0182c0c1a48482010300003210149400200b06428022100c02c04680 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 248573651 1250 248572401 248572439
    0x2010917160902070f02060a0c020306040f060b0904020315060307090204121106040e191407020109031e120207050102190908120406080a0506030c09100602060c030c040b0c070f 78
    0x54039482d02c802400e0100e101d085002041029510542e0005080080c06840c03484c0903070a00c07407840520b64010074140401150115000a1401030714420060f5030701ca00561800306840345400b91506a020035921044508402d41c00c1007100001006a42c00308101005045030010940d02c4560342c11003400c64028030f1350201c4114505c0410700407035042c40c0054a0032210901900b903603030b481c0c528041d5a80d0b1040c4900700768261719480e000901400100701240240f030507500020300e40c00c850a00810400c915920003d10f4028425554240c91740500540c40c0100506401a40c9203418541a03009100700e40015291101a00074080c496411516200c116000501550409041e800d00c451322445180194804500401c011441c401425800300d40d00200142c00c0321002880d820025004110440e0300c5000d407100d02c0400d2048950500c0303200c4d001019000701c04d046040c10b1030102428002c50050000ba810045403410340003104220701300041548400d410075083e10760030b03005c1070038281d101c0d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 248574901 1250 248573651 248573683
    0x140d061d0705031b090907030b01030c060e090402030309060c030903010504080703110d0804030e060c06190b12030a08131205030403090b1903050a0f0e03040312080f070c02010917 79
    0x90002620f05010810400d0f1103d021000544003020600700200682c0103402c0c0310092040d4038021002941c6091424040d601420f0310890300c0d03241c400010089800c200401e80110350390003d00c001610300200b076400d24042114441e172500510030144e45135004e1010015410342c00c0109000034059610003e00780c0034003d07622001480d1a00a0340e41c1d0f1205040c1d000300000d4202800240820300c134403000004004003c0000d03140c00000100145032500c241e031068404541c00050400940309480313264900740069070406a0080d0021400da26030140c017104506110424002900c030410781c440c0c154545500c070308070051010020400a1140c4c00c119011004100e1212000ca4a100d080d0180d613540c0c0c0c0d0072031000728501c0c902c220890140001624041030340d6207407100b1a1610300c00c0d015501401401c04010f6031a05d00e1407e1201510349403144a10501c01108244100c41c4140c984040c0c2c04842d074100000407080a1004a070543c0c0254003800d014210180310920382ca00100301c024104103000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 248576151 1250 248574901 248574913
    0xd0218010504110a020c1309081206010e010212030109050c13080f060618130c050a0914010603090b0114060f030702030a0807080709140a0308190305070c020901140d061d 75
    0x35400d000391310450080c0e40c0940d100070441c0c1004d00d05076502d00d144104003000456040d0083d40d80700d006401102c96803480700c5010341001517550703101c41c0c40342c01554248001c0404550328646490785100c18090006030315110310001e245224502c00301c6020044034107507000c400d42d88280c1203454020482120505016400c0840c92524254800901c1c800c440c601c01d0045443d07210440104109e001d00c1180c6845c2d04034000116030741c6040c008801051200d401094002400c0c28a54418005801140515181ca84034001213605800f91605440e1441c40d072180080d41440041c016004045103000704000000801102030b40c048043c10301c00f045070f00c03080c160751030303821054031400000c403031144c0040c0c5913a0040140303000c21041d100c0d9070803000e002d01c01036580302e8039040710a40c462940700400c0100c500312002000d03172510503164051480c1c5090710100405030b0020303480c164107100f840c441c0750341e081c0d6101965886000351880c00f90f01200c10419900402c4a03250f07152488160780da001d010324 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 248577401 1250 248576151 248576171
    0x60c0c0305121e041d07031d07080111030f0103121b06020415020a080d0207110315091507020a030302030a0b130c030612080304020d0309080d05130b07200d0218010504 74
    0xf480c02d484c181c40c0c1d00b8059034801d181e86200b1141d29080240b0074020162259091203c6848040c80c1828401c010300c0a00152400c0191441c2580c203920103c2c0016a010007c1000b40c04070041d403507040d41d0744402c0001901100c48070807540c480c4d0701d48442891014070914071080050940c014411a044840100f611025100d0140d0f25084102c801070071300319041000c1c91a03400203078000c0000174030481d0708114184120300400c0c54001308441c0722400c0b0074070b8014415000000c0201681c0c6042c100c2c0c15000500e4001002900d4090b0b401e0018240364000c408201646119003180c1c00c409405024920a01a0303449030070050246004003201203842d02c140450020351948088076203c0e0001c04035482e540f140d40c28400c40b19100d41c000c1d41040001400031844e00d20a108030f054040d07055660b0358071038044007184951805a940a4049180104100400200c6480c42a964881440048000f144110000c10802580b0000c0254403008071280803c0030f03181d0b451440e0680d403003a40c0800c400c1c085 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 248578651 1250 248577401 248577457
    0xa140721020f151602150a11040f090902030f0703120804140d02070f0b04030308180f121210121b05030304231c0605070509060304051b040213060c0c030512 69
    0x5180000c901c03556800007d8400d00e000d4111400c2182c0c0c1140e2a454159504500c0e03641c03001540121030010313150100803065213010000d240c10303880d106000c2c1052600e16030b141c03113010031084641d8042c0304952002506200400c00c62100e02500041600d60480d544176000352a02068040e01250400d070a4010524081d40d5055806882d410b40311920307540c55030b4681c5014564200841c82e118860055000c0700b0000a02600c59503c1c079100c02603450b403c5c41141c00d00c100303d00828070300404060700070410202241b0020030290307a81001c52010500c00d0201c410052152a81102d81c062000040004810840030700c981e401c20a14605084081d01040030440013850100185006509071107015000c102144e1149810a059040051074143d070f02020840541044030240c80a42190000904d0341c0f006104800380080112011440d040b09901002400303c100d004200030400c1042d44034082142c45506500a55000411240f4004001e441c03c08039034400500044008056102017001c880 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 248579901 1250 248578651 248578663
    0x403030e0f0a110d021c140307031b0204111902060c0a02120a0302070f0c08210322060207060e10140708070c06060603020a140721020f151602 63
    0x3040e000e440b403008a6212110240f94024030541c0c07041400510000580e01e1078190000000400c04100e8003040d1030500c40b002640308100f080080d001008040d00180d03002004003203085403a42c020101c9842400410000c001072440040b40c0300000840349061103a100b06000c0001c203950071102290741d01f014902407400340d10400d4015a1242c003501c1d070980b80c600d002d80b1041d00b080c40c1c0141490b1041d21038580f00c10040c241a140700c1074003103061202e242c05000340c41c45021003115048230b100009504003614803008040c0500100100050784050b8a03070700d00500c1190300301c4015501d42c40c4504102d0010824001c02d012248110040013169000d58000c00d4100700601c141000ca9640e0400240c5107804018190000c0050074840c240004103c0c6c4907500141c0031965005882b140c20840140407460004003017254840d007071021000160028001d12000746103804c400f526a0b172682e01c142d140c4409520029014011080901c0e20500741d4858144120801440714021881802007039813295 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 248581151 1250 248579901 248579923
    0xd0816090f090509030c03130609060f1e0e1201060501201b040e0102070f110a08030711060f04120b060604031505061201020d06090605041e0c0504120305030403030e 73
    0x11003400802c002d419503400158000c1e41030094a02c1c3c90281702040341154001c4404207005010b03d076052145a0b80b022492010703040c0c50a085208034980e8001404000f10917071700086540d560340c075103c3e1003445403102203107108000c4c214400d80f0b40e48042d001e001e071a5a00500740011240044040c004641c0781100180c03001000c040c00c8038070762640001c203040151040d501c0c0c001e515040d056003c08c000340700411072140200880c50303401c2420b103007100c4144080907005210b145164000e03c84404040308680f24140d01c40340002c2c84020b00c1d00400c0043c0100104003514400c0410002a50016140003059081c400c0440c50426a030350002c01089028500000d0301e030360b585010038200040719a200359000324004000d002c08040c02c0040b00c1c26030344070b40c50420b1911307100d407008c0001244a0083d1805800c0442e41800100342a404010358050b20304000e060864649140c0f070030484c0500304860141034801c001d180c0306005802e001c3d02c0c0754015a4200c1c0003d113040e4400490900c0030549107020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 248582401 1250 248581151 248581169
    0xc0f030f03040b070c020a091506030608030f03100302180a060506070809011b0822080a1e0309030f08090909010603120c0303020d02031008100605030c210d081609 72
    0x1a2900d440f60158040014114800e108a80d10b003000036030780d0701c00c040c401000118400301d0342c0459a5a0049680c20b160310010905060900a000900010050350310a004040c0d000741c0785d03520810940702a60081d8006904440595000726184900c1c1108600c50b40000e4400c0c0203081d0f80344140311a40c81f5091000e080c611040c00313400c25561003a003403017000c1038400035240c5074415161180c1c443c0c5da00c860102d10440259010310000c8a180000c144001d00000e00030380807842080e02d4000c01c4500301180e500110300014aa1004c250003801d2400c040e540120084035695220b1511141c507510460a0700c1c410301301040021080507050180000350303640a10400d201e420750850940300300a0320301c011001e0540034050402410014406107101349549848805a245030150f61410003d00c5600d802030039082410031321058074002a08540c460003500e0b0039a030344e104480c510443c41c0410343e5a00107405a062040503043d4000d50b044c2c012240f01c08143c00c80c82e02500280c5132950320f40300d89a14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 248583651 1250 248582401 248582407
    0x14070503040e01150c060c050c010e0105010512060903071205132c041505090a2a06020a26040905070f0816080f0c120403081006030204050f04110d0f020c0f030f 71
    0x80da5a030081c1c03a03e03030314905040e03027080c3c0707244500c03829a20f42800e0480541c3d035400040084c0d20b4146035180300342154178080c152a040c84411640c0324860440090700050f14000d0701c1041c18800c40448500c850082412529aa101c00d00324000d50030b07900c000a5940c4680e2070f144601d890b0481c206006130f502c2659900c1d20300021140c400600070080980009008a40c4104041406c1d000c000540036100817401042841422210b50124081c0c0c01c880308552091a0720400034840700d41180c420310018214030f00030310401050504912540d001900810b0514061040c20307a0402ca004c80d410246403280701140ea6074500154000580b00c032080c000034000d0002c502c23080040301e004c40d004210302301c805150009160140708000400d54003180080c8403034080144203040021020064580c0785025440d05191034001051103601c08445446160307948154850343c0c0e8800b04a07030040d00180418080280d801c0011b2001750404990092580070f1070000c8510120044104e4100480800220b82 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 248584901 1250 248583651 248583653
    0xf060c0a060605270613020c060105100503060603150307030f050f070603150303121506020706030c05031b03091c050a021b010903080c2406040b01022b14070503040e01150c 76
    0x42c4c010261513540c00c8131640f0105030b50030305280020015074401c00f0040c455540f40c0003d200c00c9007000150f00040200500a00580366194000c40e034209503010101c2900c00c9a1100080c2001d90360340c802040c400343c081043c401c2160100f02207880003c444181c50310765903100000e071f00362003560008039140040070501b400001e000b20301c800c0112040ca100040e1150b104900b982c90002d46410040240e40240000c001c1c00c2c2e0302d40940112000d0900e4190708505006000e280b844809807618413f40b140440020220032041200b0300a5032140004000c0040c24284d0240c066441401882c006000d1400061a12590782004955540301a5916520140b81d9252000d03250060400d000071030103022800c1404180b6120340b42d11211804594001605210003084102c88030b2103810380c15500007503848140d018002100400050075042c4840004100a90880e2440c82108008003180b00c0411303400107224001010b80240c81d00180c0c200320302d0340ca641035000442c0d94145288000b42c40070500304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 248586151 1250 248584901 248584969
    0x50f0901030201120c0c0f050c0306180703021e030114090705030a1119030609050705011220030712050903120106020708030a2001091a060402070506060409020f060c0a060605 77
    0x145007007443c2400d81c2c0c0700300d507480501d1601000d4042e41c23540e0010106020506d82400050f401c49000d1042890314181d400c001604e5a481c0d00c00030f4880c1a07101c200b491070721841c1b209402d800c00001c00030807001200c59081c081c44102507592134564400c030000440d0740e0a00203039041e03c00d90002d800ca003001c5220360401030750315039840340c0c404103240c8010700200140c803a010b10003c41e84104080c258407414080014120030001c0c00091540d424602d640d501e481c61520f007030744d241d13001203405035507039a03040402d0380d400d107407a0507040c0b1491078042044091130000c8041c0c00480c050180c03c00c2180d07030b250002c81e079501d2a8000c3c041c4a400800c401d15415005281c0020216054189034549409a02c400b608481d0412000d441c01d4000d01c0b0740c0c010840441141c1580510201e5046042100c591121581d9480040c0458001d41e51103003070200350360b6104d60700503409000070200c0d6030342c00381041d446450b0010400116446403e12030085003030310305500c0300c1c000955240045050610b40c02d03840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 248587401 1250 248586151 248586161
    0x6070b04110117100504050a020a120906020408030c01140601170f10090612020103140127060509090d080108070e040b1e130201091409040b041a10050f090103020112 73
    0x407a0521a00c641c1c000241d03d5082d481c58454042c41a021200324030b010103201c19600000c0c0302c101440d1040006000303040c0c218102c15144c400b0a00001100112840d100000b88100c2e008841103200115140c40f0360101500b0100c0b201e0f9104a6800c1c50742c68401c01035420070782c116038180c003201050300000d0701e07101400f00c1a03600010080c001c90b42c050742c4031144004c640250700320440340c00b00c600e850420b651b0507000d03412089823003104901d41d66242004d01440c0d1ba80d480d5401000d0b9403c2008055282d620340c114001800d002071820090f030421f511101da581500c0c0000001043c01d000c00003910000100d000310854903030031035600080c1e81d1036440040c0f46d0f4000b4003100000701038060740c0d0a001070200310710b4880d034070301102d1640102003400007604940340c07584201200c0080c1c41c0f070303c0326a80700c1604c029000390388200400c103151610318003682103452085d449000c0031201c070200000c031464003a682c01100c600351a500040c41d81e4400f030112404090101030b0100d50144440c3e0400c001543c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 248588651 1250 248587401 248587433
    0x90b040b030c1c0f0c0e09010609051207170703031808070e040203030d06060906021608070b0a090b0310031401020304050d081509040b090f0a050d0c08091801031106070b04 76
    0x20034048481140b8022044644c02c040143c90256240700c107030350540d000001c164109804699000d80c56140440c0248188002d00400703000b1b501c82120803400700000c1000301c015062180030311404a040c40d504560f9514284030980004500c030039240c140b407100c0040c68003500c01074809090308034100300c1140c2c81c3c1d039400f40003207030075100401c03030f03c0320194951141c1405050706959240c0041d29028000b4507050f140c4140c0b180710701c81502d040206c0c1c480000d4142c100d0340007490355074883c0d0392003009039001c81865000c46641c0c94008100031510440020b42000c0d01e1080c1c1018044004a01b4581e00701e000444001303209a1041180305071690045012720350008120341c45004041855011469294050790100c949480c11404d200108c1004d00000c104091034600400c8258065224075a48880004c40e12003400b007e0750080007449103020403686000d2010b030640301d07540d6006040c03c000381024070040d1080d90420ac0d00c50b081789021070481e5800c6801c15240c5696440701d444402c4143c180980c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 248589901 1250 248588651 248588677
    0x3070f110705090c0c010c0306050f121c0207180608011d19020f030703150e160905070314071d01081009150504090b040b1b180d0507080706090b040b030c 68
    0x4541100c1401f40551000042141d4020402900d003805012602d2001020244645540341820000308000920f0030ba540c40c41080800da10015000180c1c00d2003050b0f044044203951504406601e12125001841161460402003100707004000842c196200101c50707801c6a078000b46181303524030f050001d0300d5446500040c09160003c25100c00603140000944c030494000a032030100e103641c0c1c1094070501e00610781031001340480105190b07242c846900c00303014518501ea590004560b40903c40e9200107056012070300c1c5400c132428a074202920080002e8023034104c426003003100000a510900c4264020f840300c500c400d246500b80901203010b00309002510070254901040000e056486000d0086040d001d007040b52400d041600f800c03403040200420170810a200440d80c400a49560380c22a0400d6080a95403038200080b5000212100c00341c50000c0c1152144103008202c6045c0440e01c0c0b41101d100391142c000040d171b01c0c03500030100d000d54402c40503074100c244005580c0c000b58400900e40754110038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 248591151 1250 248589901 248589907
    0xd0804081623010b0405010803041d07020f010c0507260901030b0103110d0209030d0309030c0201030b12060108011a0d02060706050417190e010519030c020a0b010b03070f110705090c 80
    0x80c81050307401c01e00b81e907044510b80d161801d854450500d841024050403018010f0b41c5460300700401e60100c409600c0c1e041102050140014100c14828003040307000c610000020f01c184100100d0080c103d4001c00000c2c0c541400301e00e1a225807031130080480700c1403900e800342a8202401d01c0d005400604440c88828145a01c030900061039059110041110b0707a655180140c0382c4245100b803601d0301c1030f00300500c0d080c07520780840c00c00440d40042d400b007001c40d82468049860803250000c501c0303100d80e068090300940300303180c000718090b0300640040001104c0c5001500e07840240c04100800030031001e9000e50031070001c204500200345960016940940180814201a6000c03501810580d01103801c80108002117903170f4114aa43c805010b185c0340009180141c1015034040c11100824201d05507042032503954800c01c80d4440c003e2052045143d04419010030a40c0c0d584411a5941d0089074403800103140b134400c1c140b000303004280c8120003000e414001c2040314140020700ca010302d009031446015400034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 248592401 1250 248591151 248591183
    0xf09030c0111030703140403020303360105160e011e091206060504050c030f1302010e0301020f090a0509101502031603020a060501050108130312090803010e0403020d08040816 77
    0x34001e00a401407840b800035a03900e08541c1c001c045448420040700c400107085e0521000c20303400000c4e41c1d0444520505621802d041c3c1c602c2c1c1c04071001107030322000c500e4600c055107064402d040d03000d40d03c2089500345203403240e449804101d440113001e1600d04d0228a00034801c2c0741c1c40d0240d0142705094242e60408989082d100c00c80e0b8501d0400d6034408441c0240c403464107000d241494050550032146100301d41e4110305100301c658102e400300601e10302ca07010300c01141200350783c841e5114600314500a0021582c481e0140192404c03a0f001000c100e010304038254000807103040c95048640301c4d8140c880d40030182c9090100040300030024144000440c48140110309403085044403104400c0d103e83c0090090810602d81081a00c005900042c140038200c8100714030301420071541b58026a02d40790255000710714001d060000d040301d107409450000080000325200c50b01800d11406140a03030216050540070801c02c482c0d4000c2101c00601c41c00301408020b41e0005040101c038034061090f91381042201c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 248593651 1250 248592401 248592403
    0xa081303061107031e09050d1703100302031501050d08130315050a0c031a0105070f1403071e050a0f11090a1508011a0d0f081914030603060f09030c 65
    0x10441800710320b40c4002504004140d00004040103400700e04a10b03000d03010031258043d001040501c1224091000c4502d11010000001e22803520b12862041c0706e6201c0c00c0880032201c080501d400100d00a20030b0084001d6100c1d9007031492812104002d1000b0100003a664039541d26400c001c421030038040340c800700400001d80c2c00c42030b504010300c2004006030301e283c540c0300700041e141500014010b1501d0030881c44486011616601c620701002c0c24071a41c0c0b078983c1d00e0001d240548840000d0030141144204402040012000f009034500481042840e00040b4292054243c000840140190303c01903031140011055041c52004500070390141105480e4440402c6e0315620483d02c030f48007596520109075007000854054405011008000c11640c1054141d1503c031070490221588180710302c1441004004840c2450b8152a6010000e151961000e008114056104a00610100700c40306442d0210101c0f83c0700740d80c402c1c030004004024544540d083c60701c2146000c0e05411107404104001a140070b4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 248594901 1250 248593651 248593661
    0x603182f0103050402010c0204052806050127030204051510020f0111040608150f060423090c0702010c08090a0608090f071d130606120b15030a08130306 67
    0x8000e103000c400d0314400a00a0080400c0c10040c18145080240070160340d000c490036000d941c0c1520001102d40b2a000303154840b04440c00c0c2d04901c11540e0104140c194601e1300028203c070000c2e25011901d54150828488001031550002400625200204094038007500309076007046002011f008507500280126006c540c900c0c854601507442885c071001202000d100d0007070b41035001c04a0500301360401c08014150034024007609415403060f21180d4850b901c20041000b0300d440102841d540e19034a0318422803501e484280010480b4841b2100020307414080d0009100d219020700c80f5180682542c010340701a00344050555404006211401c5691501060711000c3c040c80c2c1c480144a140820721649000104200031300107400c425010040715000107115145d45a4030084480f09070307503c480c40b107da081c0b1036601400705400d0400014903000b0741c0743d000000d540200d2103000c05559060f00815411403080500f505030b400030000f078002c500020090040321108200031200a6625140c09040d64 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 248596151 1250 248594901 248594933
    0xa06050c1218101707020c130f11120a0501050904080a030c02160f0305071e05120c040911120a020306010504020d0e060c040501020f0613080d141009061e060318 71
    0x544604c1d485842c02c110041050307031005852004000d803602240c0800c03c082d14042c1d01c80361080d02ca06130040d0f600c4480d0003011616080c070403519113640c40052011940801600d09035141c1e442c1c6400410307941010700d100c0d40308a03044400707145010740e102412001084811303255030460040001e007001c0c0b8922091407200a00c045000c4500c8039003107041060910030b09a115004440d00500080106c500791042c48080310000c0311602d064511a01d05907040004a02c0481e80c0613140c00000004c00c14090f9641642c40700035030b204600e140d000d4810654407051b80c0c001940c544d01200040010749010340040510761101c035400314200e00c00e2081c151604006403114070103070001290a00c500d5a040041040780d01c1d50300f00500b000d040890001c0304031064400094210800000c641c0d41c03030784040d00701580708094102614000e207004d80740004000d005002d210032003814224001202d00c0805187c00c003507072502001c14601403421a0035401030801e60450b9800c03845251910022554131926000d480e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 248597401 1250 248596151 248596157
    0x240f05070504150203090f1210050726060901030605180304033c02010c020607051b0a0611031801140c0c0f040207031d0111070f03020a06050c121810 66
    0x500d04110030100d040050f06200030440d070040c000e186540c0c5d50340345080c407101d500f40c3d041c4541840c241c10745418290360714041148a8200403e000001f503101024a81d808910554600d0f462401562086400b4040d1049580b080d00301c0014030200710103501a0360004000f800741c8070500180360080342141c00139801907410140380070b41c41301c1c500c0e180c080c0c582c80030701882c1c86503800d80302807000c4e5440c14666520290400c02d1280581d01191200c4086805543c1c1000489103101c50704002d04031000ca016156074081e07001c0b80c00004081e030151441d0070303950081101650030310b02c0304841c900b0306407581006541040f5050f030141d03265608a80003445e088800d10050041c1c07203141c40038042d0303031824804114000d82c070400c10701c00840d0744159200d42c0014102240000c26034100f0040380c844510105c0303100280656a400504001d1a81d110000c882c800d0f203a001005a4851090300c0900507400540c40d540c00042c40144100e407058020407e50f01200c4481d030080c07801d180451034481014282c0004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 248598651 1250 248597401 248597407
    0x7030e01270e0106030c1202030a0b0405040f021003050903090d0203120a0513050d031e03140a0606030b0402040e070c05010e010c0908150108120f12040b0412020703240f050705 78
    0x24494004050b030703025003607a0034144019440c19800422400c0302c001c2ca2800c0c40e601101292488455420400e5184c00003801800340781050700341071130400c0c0c00c1c10b4103d21588c224a20040c0d02406402590b1084101402640c103203814841032100e40f2180c084100da00d0b0090084c00a0780071a0760014000080035942c4054450b6002c421003401c014403504490f00c1400701040c4000040e41c00007004001c0520600e04280c0001000425009445280604080d48411004114002005e80d2054080300c0b15a581404500014000d1008034465409014185d40715000099820b0b4002c1c10181c000741c0c46100000b81400c08600d0f09400c6078440c50085c8000390441c8004c110041080000c64004901b00200d03800e194502081d159542c003042c20040203004003c80c0c480c103400300c1f9200740e40c003a01101ca1141040d140c1071400700409001203078103c500c827000745001e07070307155100140b80d0702520790001c1c071907e10060040b004842002c1300d0424000554a07101d036000b4258040c0a4680202c0c22038a6481d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 248599901 1250 248598651 248598659
    0xc03030c0903070f0305031e0702121b060715020a02100216020f100905100309080d051e0903030a110702030a0b09010e0c030c1903120c0b06041107030e0127 69
    0x30600e00103134050318490201c5801400480d41c040300b1101d0030584881410701480d040310100c00d050182d644003079485090100c0709901403001044188031500c8010510300600198000c000c02401818070150009080203400c0003036074250350040c541120280103c44062250b00c0c0240166444a0102d0315001d02403c0d00c039085003411005000c001200319600301540c0340d8400c00606035041c5110345031043d01d003d01000b1400d070180c3c0c0f00020440e08420301503614510740009a0150a081d00c00e50b220b03141d0411a003101172100c01240380600341810165144d5103a4280c000054020318031031204420b000c112050060340e0800560b583d00e4402c0c01e0002c2c20b403070f14a01e90750071143c00e11003540240e04039038003184c2c0994020604074034a4004459000307020041d800007120381981d60700003c00309840550903020664101751600b80c0b0034030481c1c0c406030b0343e9a000180410303617800306140300741c107a018080c1e40700081c0504460ba04541c03040c50b01d2082a404002c0c05000302c0582a02d00c0c80117440403900384 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 248601151 1250 248599901 248599903
    0x504030c1d2508040215070803010f0f1a030601091203021e0601120305280c1b050603010e090a060c050a0908010603081204050f0304060e04050a0b150a03020c03030c0903 75
    0x15480326034041080e101955031402d00c0d61440e0802d14120410044000040031541c030705203400d4182480070300351901c0f0246464040440d900070f004d1f0071203001c07007214000f41c0d503000c3c0001c0c0d505481c00c9071881d01828540d0036807140c9541000d0545814000c84580205910240c190300c2e2038054013035130042801d001d8500001071510600080700d540380d0445001400101c2090129a015603418548242e4600b4125600516200b9914200103441054100070b00084d41c41109245100d020700b402400030303548407400c081001514818590030480c00c2c401008040f035019070940c4e1050160050712003110890386c4130001c541c20700f40f07848003203400400e580d0300c180da109090901404a1034020025141141c6031601c05000d004d00c600e107010407500000b41000b009000c59042c160a40003184e440b40d0b00d85002038803120103498401c8c000ca2030302000402c07402807801002c80d00600a070241010001c0c00440c21040d90040d1401402e150302000f02c401c094008000079441154547c942503100c00d103a400301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 248602401 1250 248601151 248601209
    0x1090f020f12030421020901030308061c120507060902030a061d031305121005070801051e150c03090a03080706050610081303090312030603050106171b010504030c 72
    0x103180150080281d0b071180100000456041c0c85002034420890107907907610061040741100000e40054031070000008240d000844140210401c8412000c940c100d4840d002c1050618100644810403c1024900302d600800003880b2560082102052000359900400c2c6010786410084419980c0e84245480008544800d0030028240c10040d42c0707044a114940b81e5050401c1c007806110340d0303c0c14100010b450f0b0810014950030003020080c0400d2500041c050140d103801d00c21603000c2c805500c1800b503480320400d03000c0c42401d001401404060320004180e03a850b0040c1c9103401842c4400c100d2005241d54942e82c0e00f0082d4460b0582d20342e03071290303494030109031000070341100d019140c5d185d0180c0b00c03280c100350010f5202401e0310000350000c110f030604079240c4001780e1000e4500d201c1920300303c104551540000c03013a039010388001d0007880d50352a01d0038862001e0030b0a4007203035004100000800c41c481c0c003800004040c1403501c9400c0c40e449440301058408203511030400c401b0f11100440811000340c0355 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 248603651 1250 248602401 248602429
    0x1b05010c0f0806060a12111606060311090601081611010e0c04110306010203030a0504020409020a08060f070f2010050c0c010609050103021e01090e0a0603031b020303120c0c01090f02 80
    0x9917400d011004401600080b1a50640c0030346540342d800700c0311050303041c9003698001e10560221151a001ca414002c00406442c001555050101070722280c1d2410070440d194050b84069640c1511a42c070300800700740c5c1003040501e440c00c10100b006e446000f84002d024031646030080c00043c00542e001c0030104411140013118000b0b41500c24020806541e80102c19030760322241480003c2610f6540b0720000f00103103000d100082d4020f44180c00403404c58400100d961152002d911811280d403a5044140c1c0c404022410f400c0c00503542d41c8842003541c25994640002c12004800c40d03000c5144001d01c902518000c40b45201000c0022501400c100c0c401d000b44c0d802051100d904009650454000c0f8007580c81310300b444030f0305800d1000c5900d8980d1040440b68010042c0030f0b030b17a039881d06181b02902d001d05607a12095001032840001005084400400c4c422402d40c01002913107064850640343c0c2c0c01580080545034840d00c2442070300c074031345030a008070800940f05404120500c4641d2041085c54084412 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 248604901 1250 248603651 248603659
    0x1501030503041707080610062006060d02031c020607020d0f0801090209030f120309280f1b0617010e0403090603050a020723011107080403031b05010c0f0806 69
    0x4002064000c030403101611428481c000300a01c8103860289418400d42c003144031885070004203e01c880424070307032905a0307440e60340c0c12200522450603040324410445420489411200c00b081852501c0113118210340e10203419070350b88842c80c1030341d21160f0285501040250308403004200401c1c2d81800007244000903410008010809820024140e4905000b50001da40d40003401d4003495604100e00808031716100b0440d581d000030300b10002c0182e001503e0680a074031400108002c04100a5200030503040d0036040281ca581c01615400c0c1407040ea10030540b481100f01111a0361006d03028142d501400721501c4220100700109801c0b010705205038000e046103050003040c4400070340d00c041d1990441d04585008540d54403084000c00082c8a900c1c0028044064040100c941d0000100303130045c1680494020090750802240c0c2c588244200c07900104511010042800001d000c0c05c0d8140c1070107440c8124040c1d4000c560740f80c608640800c40908041803501440b004240d510038846c80c0e0000040d2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 248606151 1250 248604901 248604943
    0x16092007050105060910033807020f0d02070503100504021206010e0601090501080c070311100f090507050114042903070210060f0f14040b040207030f02060a02030c0d021c020417 78
    0x92915a44413001d101e003510081ca255680b86014502c48c02400c1d10761550900d08881810903040181d43c40a1040e0310003503a014030002c007500703503002150000c00c5950203000b90a02d46c42419602c00140310040040b43c7c0040f40f030402c4030000d4810000580030f401302c03500e0f1802e00e04140002401c003101c80d85c861410090104100110b0444080c15912803562601705602096420582d880c00c141461061a0100745011480075040340c0c1034100070340f041e003d01d041d6083c03980c030b400045898401150441e18a00030402c02005000985030036103000c06e45000c000c2000c91040b10680501c0d034016038080f40140e200420301c444000721440b40c8402003a07258a0314400c20b19254040850003528410512250b081440e07482e80c41e02e40382c00c40510310b48000c1c0119505c103201d00e409069034410302102c600500c2500001a1010030900c00c0b40e02800c03d81c0e40c013a003400312141c0020081c0d88200c4442ca2201c407901010420700f103850000c1c002622140d00e500c8008444000c00c070380b5004003182071500c0083d00d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 248607401 1250 248606151 248606153
    0x1020901050a050307030f1b090e130f030311041403010b030c01081609051203070309060206150f01120f0c0e01030b0a051903210e031609200705010506091003 70
    0x2241c9100b44642005926982d0310001035000b469414802180903041c10a1401c0c104040c644072220f2540a84940d04940d031666000d00001004582c0c00100c81c8101c80d507003020405544528007554070918012880c1140350301801c0864005600003060700058059111043c60b0a005020303000c10190010006201c210000174a1910007030901007800000c051a045220b101d0b950090203002e0180c00c81d030801c00c074200700d1580e0368080c0d54190300003284502d0200e106031000c2405405000c01e200052030040c003800c10000360000124010b8180003480400e2040e440c0d19010784042c2d03000720000041c00d0010108050094000c22280300e04041c900420420b00307075139a0010409840c0140e81e0f110040341280e80c0303180100000c0c0c101034448002c81030300c1c0348040356038034801f0381c6610b440d984c4404151100e414155180c0c40d400030709149903805801806000c034641c0c4412410759081c15000d0740b221000c0c0740011590306c095400d0760140d4503801001400c2c103046130302540218104008011941c61 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 248608651 1250 248607401 248607407
    0x2090d0204020306040b0d0812130b040b22030f02010b010f090306020f0702060d05010f060f08041205040b040e010509010f0302032806021b160b041215050103032001020901 76
    0x14000207200310703408004100c040d101c6074003190505401811000701e445050418100b9600309003104d1308800024000500c40c00c441c80c0380108025402030b04d02c0d00680f155a202400041c0041003d04520f0462492350010030301a0002003900340652a8023189822010f8001d081d540703400d8040341806000311120a070350342c1c4052001d04072070304800300507103840040d89800154032800d50003070b501070008a088100c4015640c800341c102c90141c9260b03954280c1d1004190340f410b08404601010803ca03400040c00301c1d90921868149030b0240c07074194640340c0c8400219045802a030071039038507140e0720741c014030017400d01201c071a000d000c5d24200e52101030326540c0081d5070342c20203031a500c0720b064000e54280000040600c0c0303446250350203181992501c4440070050001c0d504042d20b1045807060368880201003840a8244090f9101110301c2c51507c1d040c03680c6941002c202040031103040803a5030482d020700c445481a540a1340c881c0c0d482c50040852011217514042c60781002c44083c1c1d10401455040e40e070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 248609901 1250 248608651 248608669
    0x1140c03101403030d0f020c03030708100609030f11210d03151208070602093c0307060318020406030c0512030a09090c03020909010306230609011202150c0106050f040209 75
    0x5d89904040303013840c0d07400300720310280c0613803c600720303140c0f0000c000d108640e6000341002e4490386046401da00c481d550f400303003110082c010344005455240d54400d10408078a00b07000009011a010302640c1c94540c000e403840c01f0740321404462030303c9278020301a51000a641401000d01c0140201c9100180078180803000d011880c2d45c400003020020000b8100040000369010b40c0c001010082009890300900040740641040e02207141c840383c0c2d246103200c2c022a000c10b0400f40101000f6000b818420f007825030550050602e8480c1200382c0c1c000040e402d0050742c441c000c000c0070714030030881c0d2170800380382205000e4940c041500041058100740942290580d114410000300c400c2140c01286420082200b54020b00c03601c1c0c2c440340c04c010080700203c1401000d41203414011854a00c0030117007d51400c80e0b0013400700c00e4555070f6006003024010407a1003090910001c940b40010402c40703854003201040300d201c0d40000d07518407a5944440d401c2106240020020b00601016601545000d22020000d08848 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 248611151 1250 248609901 248609917
    0x50c1b0f10091802040609090c090509060d02120c0a0e0f0c03150301020c010507020d030204180f0b0d050705030d050c06070c06020c0a060605090a02190c0501140c0310140303 77
    0x61540101c1151a01c00c5002000420482d840c45181d4200a003080b0b02a40c018011035003c03c0268100088a0101d03214031460442a0ba81e002015410700e0204100000003400f402d42c4500d41c1c030a082e01680d10040e4401720b515540005085000c8040c0510041001da58000c809010f002000c010490300715a00d6668800c070000b82c280e07034a61350350f0010541051000c5240380c2543c40403e04000040c01548228041d0095400300c0d00794030204007084080e44604c0c055902d004140e88441c040350b0849800c10004d41006450203c3c01c038503290085600b00e200300b6000c0c1d6650744201707810045400c0a000c82c0035501140d04d0071a1800300100d0600c0e5440c0e41c041c040030700b00801594a0414003d103903060714040b12441c07064456001e41401d00c007024241500882e07124402410201c0c401c0e04452081b42c10964000d00406002c4030540b0f010f6810201e02d403001e5441d0354807580e420900340c003483c440c64468414542c0e02c036100d00380f060340603128400359007050942c084d00fa0703260304060f40c0c00010740c1c10304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 248612401 1250 248611151 248611159
    0xd020408150f043c031124060d0812070305071b03081806010f0504050c04051014040504090f0b0907230310020c0105011d0c0304032d050c1b0f 63
    0x3a1040400140f000d14140031000344070344484e9100f860b1000a880c200c90100c2c0680c0c0ca015070040019000b5480f0f800c07080900301e5607814154020640001c101009501003402001080280645d45400d00180d004640280003024142c04004400d83c1500c10030390012240d150a615a050400c0071054055103400c001d02400301020004071901c05100e403440c8140e071020151030341940e46502c00b028400e618000e01d13100750f044c81c00081400028405890880d44014840c40000c4c040040076981412503902c542d00e0161700b0807021441e42c440b4010b2010603413080fa000c2da0a4103d900f0821109180500822181d4109040402000160014407181c1c121b5000c000e40c0c80755180c81c002480d02e004c2034039003c040c600116071a05c1d5100c040d0301140c100c0f04104840541f0006050310b9a0741c3c1d01080324a08160b402c24404100424459000c4440640100ca629000004209520654402941702d50400102d0024242801800501180e050250140d80162258442c580000c80f10103c00c1209801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 248613651 1250 248612401 248612423
    0x3080f0702030a060f05010f06020316110126010e010b090a060f0c02030a1a0f09060708040206091c030e0f060d0b0f090709030204060e150f0f060d020408150f04 71
    0x10741d6018003000d50f405901090030400000c181d200c10001d480d09100d50b049000d5034100c00a80107001008490a01b484040c000b01c2c0e121090740c800100c0c542d031054050420400381401c070b40101c4003400d40101c0c90340180540c1041c1d0b140540840d80c2000580110031760b0340041c070440107152140108007044e91441c1c1400c3d40610001c000440d08080440406989071040502c00f10620803000e051800c0034031a81c40c0403400e82d81e0504800c2040b00c0580710022a5882480060001d5120b0000d940e009440200040c0c81d0215100019500c00003c0b0300c81c8800d09d10203040b1008041d0424408411200290340c0041c03029503010008546028040e2450403541d207408054100b40c1c0c03400c500c040c10b14070042170207840e070415410040c045815408128003851405401190400741d038050a8071074422001006988246101406011039000c824103800020340c0c424082d46544240181400c02c250000061305d441c0b400b01140c1c502184e12001100050703010061240e94606c0406040d8055004018070031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 248614901 1250 248613651 248613653
    0x3050a020d09080d0501050405040308071d04110c1605100c020d0209010803182e030e030301080c0a050402040605030f152706010206010509060111010209090916080703080f07 77
    0x3034400d400c600c0d028140340410040811041e5000b4040140d40c02500304110ba8a40050004441d01a1806000b0851541c002400e1501c2081003000b42c01e50702074240c013400c541c040410141d4030305248000304c0920114000d51200010050411801c00700184070071030524200125860b0300984180c24100000841c103082551690142c8007422507000c0d2090443d9a035071000d0391303101e4001c40c40004401c1d0807403200420a14015840c01c1410000b00c0c41009090840c04116410a1100e81d000c8245501ea402d400000c4e07030103101542c02071038401d0192000c460080d0800c10031003110341210f44120b10503c0180702040d40f010503242e0000c040a2080c0310b945441d4019000f0200b0b032103e0f0f5a2108440d24072184500d10f4011100036002985a1708809031503501c0166140c98090044030740000010300010402d40c8030b003c9580400d03d000000610300a00003011500c041d400b00c82c50200c5500018800b0000c0091204000017000303440701815080342140e4549034a84074405403401d4120303000c42c00c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 248616151 1250 248614901 248614921
    0xf0204050a03030503060a060e0a0b0c19030906021203100603020a02030408010603050d1e0e1e04060308210c03010920030f04020a09021e0327010504150902100305 72
    0xa0090840280250501c0d65680b8008000380c1c0100d070894002c40990100140c8207024180c03401d030100c03006086462130b90a118040007160424803003003480f8850040c10508001786180c0c4c801d00c550203a50b60201c0395080190292030640d4899807141c10940820421626402c00c0640e0700603101c843c0f40160340c0c3c811001d0304a01d58051900941c1040d4a02400041004400140308039400c0c11625044c0385a0b4581c0001000e04039001186d201080315140c0f090b1151038000c0e402088450110b0300100606000c401060403a42e25800440e81c0c80400601402200c003207802604000002000d04543c61506000380521070206100750783c181502c13500c3d6108220207003078070610b03001d4503c5041070b1030780303400301d41c180650000b41c50030313400380154540c0030420a429008480420b45045400300c5c088000502482c000e80c0000c0901d04100640d0351051003840c05818802040d9400f01c0000c601c60400b0304140300103609080880a00c1c600e0012100d0041e1542c815040c03e070703012402c00086c0c07a6200b070192 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 248617401 1250 248616151 248616157
    0x91b031515120604050a09030c020f0406090c0804140604030c030e06191830080403020307080d0306080106050a1e08030a020f010f05070c0215120c070201030c08190f02 74
    0x40e40d06000815200c5040204202091003041d00700c07000d1081d900d43c001d03c0b4041f14940e100250000e95601e07540e0002d0704001c0004440444058000101c103035542c100081190200b800800005400206000c00d100b40c03115420015407580d03014142c503040565020b041c0c0c601011005080c00505010792056a4910b000d5540c40c03007000c0c80d5140d4045030b01c00c00400410103c80300b01041030500b4000705013205404914903402d181d1071044000040e104618800d800050030088512000803c80400141c40501c842802452104010300e880349003030401a0070f03512940c1000566a00d4450f01300011750302d005405080b602d104480703012000746211044036a035410341001c00b180c4000900390102542c001040503140c59001c0003040300d011041d4441d4142c40d41510440c000941780e02403000903240104001311100460140145440d040007007501c00c10300103e43c1024074400c0411200c042d56010301402101e01084c0c034040c880c5180051240002c00811011131034019661280540711007155411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 248618651 1250 248617401 248617429
    0xc09091a2803030e030610080304091d031615020703020303130203030702042408010605030303040210020f0601030308060a171b01090803030c0d06050a1d0c1215091b0315 75
    0x407500c41e941c803810b01602940790b1008090003480344600284000a05110001c191004400654601458542c02101070210b41c070300c41d60040542d01c5146c00080c4e0400040c0031440602401840e910500e003007501c1c0c41000303d041c07080100c0c0104111800664013000720ba42c00700d00848a21901d01d15400820b03c6c6004400d0000d420500d442040c0144180064000075811000d61810f40a107403254021400e072405441082c0d0558828400f24005150075854113100203281d10444e9110b0a60080003450a5403ea1040d404240100244801800c01003038481c0034164030031300300800c1c44090007a40d035110040f00c102d4200b421943c006d007600f0b03031044030003900803d142c00c200c030749a060040700b5155561120203840c90042c80d20030f0006007800c18549520481d010780d01c0704082400c400660780c2d503429000341030308403e200070000d10307100014070240c03240100307102d810301c81a544034a003c0c05074214001d00130b40080030392202c02c04044001d070300c110380c1c1c807800d4484080000c0001e40d0108542400c4801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 248619901 1250 248618651 248618719
    0x2106060c060c031e04030c0b0606070f0b060328110f0d022e1805030a0b0c0f0d06090c02060a020f04050f130504050307050c0d0b0106030509071502010c09091a 70
    0x13044c03005150748405500d09443c00344076100402e8413038008000080c4505000104066240c0d60700340c012445100c9110390007100a002d40e1030440209604039102c07581208801d40380942200090144540c0044240c000c1105a0f5809000d000711000610701050704203000f0720038180c102070088141c9024902c15408513161821642c0103400d40001360581001d140000002e0103c001d00082d203180008100303824030740001180c001074880300100c03850b5621070694440042d000700005418009684617400c01409100400203103142c141e00028100803020b001456514010b12103090300c03804c3c9500303c404a030342c00c4440c846069403c4000ca4202984a064043c6031450882000709200001c002487c01c64801d5041c0c5071100110070402c010144800805046818080c006020f060700907486544c02c50009002c9880540d614210900d4104010080c400181d4460540103030030768216140101030f140340714041c055990558003641e00c1c1e4251421031031242c417580200307040c5003030701d41c520b880c00c6d1035411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 248621151 1250 248619901 248619961
    0x6052203021c02040f0b0d0b0711060408030703150e06010c060b040c0903170a1d04140703020c120c03090105090a09020301030c030c05040510090c090b2106060c060c03 74
    0x24480c5102d2524a1038140c1c081d038240484891403101c0b82c8216454080001c00560450724551104070098400034107202c140407818110440341d05003008018800c61143e0354450303070b0b45000d20009069030304600c440b0b0311050740514240402c80e1300ea01c2080d4055030070b1902e40418003180c00d0600c05000000c2001ea00140f405c50f081b115503038080480ca00b620300400c4005500208402e05261601ca54260200090114001a2000c006a400c0c140200382d0003031001c100c0404070084035520030741c20707100c480111754000b80901c1d05038020300422100800720201c0034209900741c2d02c1d10f5247e100b86121181009000508204559100c0010030040c02068400719120344c0c407841d140b200d82400b4081544c0c1c8030141200000c0354078041c050284510080a51140312520f0084824050903a8821076024821910000f0a401030124041c103140c0c2e1141050b07500e030b000c00c85819021000e001e458107008040c03c0088035542c1d0030001c4c0154010100c0d0844030703034a581c1c44000a03540324103054072401400c014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 248622401 1250 248621151 248621179
    0x3180c0d03140f03100807060f09051507060c0e1003060503060402061e0a2606130f061508060405070e01081906090f02030a0b0105030907210b091609060605220302 72
    0x281e0fa1180130381d01c1c14000c87e0046900d500d002c0c0d90195546c1c2d142800109590400c0c002403c0071020000c5c4065031006c2142030107010342da00360940b4120310f816000116000b001280718504010200044102c1d410101f01c21401c100200b41c90b007400030301c082d00070100002c1c80c3e4043c0e000603400c06100140150000d07151403040c03400504132020780c4003080565103a6002c012600b10301c140003d0080030020301d81c080388442480454080d0044045040300560b4505001890b41c8200000f01c1c51852260398401d141e01d030541c100f1040380c001500140c20018402c417103d07003c0c0d03006803c060300f2020000329001c059181070341d41005440c6641082100c0e9043c10011120320030160040e5029000920080c0012aa50001110240421a400040703a800381404120201c00b801e2422817001301030090060040c210f44070000544015280485194098100308a10010b0007220401800070f01c0003c2c40300b6403074028001c1050142c08500e8a83d002075030103c02008003903004032402554090010030b041400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 248623651 1250 248622401 248622421
    0x150f070b01030b0702120a091509090507030207211718030a030509010c0206090d030e0a17090a0803090a0504110c0a08090f06040b04060c02010504030b04060203180c0d03140f03 78
    0xb13036254405403141e004054641e0010400352042c0c50515a10600254038140380745500321140503a5005000140d080428040d0142c0200c0344200031540700566a0000c1d8a030140e414140400a40198252400101012a400000d81c100078a02040c10340c1d090310f4051090308082e2081e00b445105100014440c401c0b180c054010500c9681c002d4000c100540e2020b0040c0e0b04c440003240c14014942100c49074100042c00395218120b4184810700702c0342201c541e544c0b250262940c40040f1070700705102060007911441c100076498003805100300503509280b01100419146205030050034807854450303000c4803098180c5003c0d284140061030844140f0241400c0c080342990162010380d015405140b2003c0f42400c11400f241d08440e01262103504d0a8a000012514a942081d04a0410004000010100782005942409a03000c0c4400580d00e09104c441440c10840b14041341d19140c1040b0300032012035460103500721071a901070400da94484d81c400d28008251050842601402201000748140200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 248624901 1250 248623651 248623673
    0xa080d0c110306040c05010f05040b220506040b03060d030c081201050915010207090b060f190e0f06070b04020301020d0e0c0a0909050d030b0a050603011202040605040b150f070b0103 80
    0x10140d201d0880480849050580b0b0304403c4402400341020403104110a500c02e0515841c45209494000d007090388070959000710341d000c2e4504800218048030200b140c50070401d03041c0c0040100303c03001d43ca0145000c044100e680001041c2c50310030600c5c0d40e4030101b41401004d90007022503001c0030301c0c2c4d0340740c0b000c00c00c00380410428002c15004005001c0040d800c00700c000e03562500220160021324081c1d20740320030390307000e4800c4d605c4594020b030061188044441100c0003030404018144c81005180c0494240104018001c1c49401d1240da01030400b4031403919080111a01590849100e0205542d5800071078068403450700707410044c0745016104d0401e030602203001c1081040450b9a590003940d26003049068804c5064041c3c280c0c0c110007402c0c030030107001b43e202449000028008640705943da200207070b00c42d0000d91110f0300043d075505081045142c01d02c038200181c88112800c20141802c0000b00e03060201c1d4294046000b90005154030340d60113140203566940c0d078000b038030300042d41c0c5a20307040e140b00d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 248626151 1250 248624901 248624903
    0xa03110a0b280501120212011409030406080702070f060f170c0c101103061c0209040303050f060a0303090618030b010f170109170a12050f090d02060c040509060a080d0c 74
    0x84610719580740004003038010f080c101ca0003900150f40f940c40da030302082440c051a00448650b5075031800507025000c40e0201003441140c0c404042c50b140c0f8a4400c0140c5000401003d035800c54000d040c00307000044400040b403090b9034031440e010704100a11503007600c5131201200311009001c058030402079408030310001025011010070603104c2c881040b001c00801d03240c244080103040c3c0c000740b0004446061560640d0380200c490302802d5007503100307500031a00d800c50035941500025204d008111101c145444080c0c0c100714141c403420503c0d45182c41c000c2c980c0c5105c0c01182c040082907000134a00c1050310a221b0069900301500c05c069503524022111200003d22035806c080c14040f12031105240e040c03013011b50380c9400c4540320b040604500d400c2060b0f1f46c04250400203001c000d04d103914824095100b414440d02415804d10064140544030920701028003c2080841d030207141040703194a00c0b44155411030b0010b940c00d40c800d0b100c5200243d4043d1150b0030408451143d0310300100025401128101d6003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 248627401 1250 248626151 248626201
    0xe060901021c2013030807060902120a0507090515130b040605011805040b060c0a050a0506010503070f0b0702040e06070e0108150f0904020a050a030f0203070e01080a03110a0b 77
    0x15040c8641e182041c0c90140071440040340543c4500d81c1c035907800c0d800508001010740103c10815403607644000b1503800010040d1401c07a9070700c10300c038110b0501d41420410081c149005013200a0307159181552644030b0b000711440107446201103803002202d07080d0560690402000b0400741c0349840d01c404003c1c004d0700c0140303201d5030500f0000140c550240d0440c0710044002c120040a41c3e00342801d01025140c1c0c80451030300103204001a202421301401340d1052184110013405a240b42810b21034505001038001e28843d4001400400c082c0390300c400da060481d000803068035100d003600d0001400901010861a106004180406c5003031544007085107610700d402d0703e4240d40345c1c5442c404442c407400210405600140c0b00c0f055110070389054003150394010310041401c145640c80d10003180e900c0300240d0089071a042c00b24003903402c618082c015080500400e16120441c0e40c034000075582d803101074140207810700103c5080c521044109001c2410308940008503002c860500e03142001094011b07417003c03c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 248628651 1250 248627401 248627437
    0x11808240702250e0c0703031b0e040e12040602070603050112020d08031503100f3b010204080d0807030e070501050d1503021203070c0e0c0301060c05010e06090102 72
    0xa641100c0041600030840e41e401407001c543c80b001c280078110341d044080c12442c46421000210310105442292040c00e015500ca5280c98440c9805010b540d41c07084085d11800b114070740c03c00c4035544581c03880091801100c0114110b0062220b440c1482007281704148028000180400c0d010740024820086030401d60301006541c1c0d880c01500900c00c2010790080d07000c1c41c030304041800700300320030059a002020040b281892107010400285410301c02c0d101c0e141015202c0185500c40d6041e84101174084600751106251003508003000025101c55840e607102c07038104410514180502541694058036100c2c0895602805890000d40594000c1f9001000a80bc2094007550403801041a40443d00c2c10b84034203061403510707441200500324080b1441100f80e6009800000341e515000201060301040000e981e6506150802c2c1860200030340200a541c403181c1d003444004421101107038119662880c0c0501101480d00d007a5015043da50f80c0500c940c4103042c140304610106500800c10105201d0059032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 248629901 1250 248628651 248628703
    0x516080f0a0e0a0614030a0e2b0215090c010302030c0f04060305041101050a0f080a0f02070c05120706050901030b01260a0c03150902210103031707050423011808 71
    0x884105e00780110f5607400c014000f0404142c0142c2082e030101309103000761400504c80c641c400e05003c0140e21a050004100f0482c2c06440e0b4041c80260310018045111280030b00d481150302daa81c0c0c3d442080c5d01d04050340000040c400c1d0000c40e05860280c2c160741c2401e680c03141e440750000c000e03204c2510240e1720140080308150345507028004958414226854920000e030481e801038400e058010f0000400c10f494480a000f40122803000b0b14032903202c1d42d0720003481400e100c18801c42001220ba50b18603548900d401b0310415400005541956209180120b0049404001200e02c180c001c0000800c2c5d0800d40c00b141c100e03011010300c00d84a030700701c00c004202a1640301011800c1d20b0303500809040700703040300d00305000d00b10b0642c0040c401e100b40074484c0075804c00541a0052200b009034401e800041c196440c0c4440019540354094100310300385840f904142c2070805540c1d03c000b03001c101440c40f105410359210581d0140f2505000c03040355280b4140c0080c0e4a00740036440348011005045803040000d03180c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 248631151 1250 248629901 248629907
    0xc07051008040b0414102301050303040803030c0a0c0f120305060105090a05060706150e040c09020a0e04021803010204080c0108160906080a0209060a09060e030a02010516080f0a0e0a06 81
    0x10348210f800c201015520340302c1da00e8003082d02c00841c0c8510858040c04010f260640e4290244542c00e580b4010400e0f05000000062220030006030440d80c800d82041000b004001ea0010660307402c0086500c00583d156800103094480d045d21400042c41549101d8018041c001c4011030348100300041e40b0140300703039560000119410b00c034280801da032280c0001c0b024010340c14100d000c2d0002910911000600550341c41424500003904d038018402ca000c02c1003000200a2803558520080100401c10350401041007405000740501c1188280100e03800f061b80c1c0b14400c40c41401c080c2550025000f155100d803500038450320b1311507020015021a0f000740c042810300560051a00c80012123564146c40c0340d050550071140301c0380280c141e00d06d1507000d01c030242e695580c84005051100c0d00307449401e491441c00d41c1c041c4c2030742c0d4044811403290f04409050f00140c3d070020111030541d1610078122907040c825250002d018050407940c10703548400072401080f812342002d41381c04d614408541c0390200c00d980c2d503011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 248632401 1250 248631151 248631167
    0x1302040509070921060f02030f070f05120a020906090a0612060e09190804030b010f050a0602030306090417070510090614011a0904060e0901061701020702061e09060c070510 76
    0x104c0015a070a5407228110241c42100540c0c0700301c0340480d5425010344004141d03041030300d0038603a4009041c2400b81454100b0810101c861090510608184002c01480220040180074991851b0002846410307956444100c0e5041c82004201496068880800030100d00d4490b0355050841c0c545180131410b4114801c00b10312036401d480c020300c282207803002c24412521554104072542c407400e010200000c0ca4054181d40070704110350001090b24940320400c04a50b145d68005800e640081040c0449611100101d5900982001443c2894003691486c00310300d10800c84d002c1c1c024015101e154146000725085020101e00030707081480014141e44164942000c20311488040032880442403030781e24030800203807001c03032002000080d400b80d0718440300301c00c02d204980142d42c0d0b035504d8206014030191854030040307500d5820001c5080c406c281d0302050145c030501c400381342080342e00103d8480c1c0380d288004940a0030001f41c1401c1d03c9840c403117011035032120a80616803003002d5032051003503814450442c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 248633651 1250 248632401 248632409
    0x40509010902091902041203030207020118060e0d032304170c0604093206011d010e0103150f0617060904080301030602090a08010c0c06060e070207060f02070513020405090709 77
    0xf0141c00c0c0d440d00320b03c0607521400b58003411180e9409000c00035140c440d80c03000e40f0341c8900944015a59800c60f02c001001100c40e40101c082800c0308100620100741e000001509000042d150500c441c40542025504002c041d049070b0040b90001a2003211032625001400844070424103c04484040003000c1e81c44d01c0a004200c0d8010700288810809100305030400541c0c800341020317880441c44d0b50075510300094130312916007482130709240600c442568020f91200342c0d040c20407801c5c521003228800080035941c65001c00c504043c0c403920040c1c2d400c404090345000030308610f400da150080e6108005010182100b20141e6003901404c0003500340d00304070758901d114650001306946568259991003009400a02006400c81a800004101000b0034803454600c082186c0350101004e005103072090a80302a5002600b960306031405010480d0b800007500700030b5500c00d00344111284250203040340350903078960009500244200416100e801c1c282e004100703a4409517040748043c1c3e542c1c042550390044c00c2c89 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 248634901 1250 248633651 248633659
    0x150b130606200c0108040c030b04031d03011109040209011101061205060c0a090b0d180c2c041e080403060c0f031b080a29030606030a1509020609040515040509010902 73
    0x815194958072512206502c203204220100c01306840327856030606c2510840d4114041441d00c42c106818042c86043e00b0301c001e2088000b80034014829890081d2070040c5520a405a50081041c49240c0e00500c00c10320900118402003000660342e2101404980049800340d0f401e0081c0400f1515002d40c1904071103150141e511144001d602e8078543c1202680038001084089a94070740c011459005000d049421034080d0205100f414244004044c03940c28a000c03092021a00300541c034041540c5684180c1e20a4110501000c3d481c400606140c00419401d40104a010005804000c024071a880b07200c002116070b13554660181c0b0710b0400c0e41100e25140c1c5c01c5450004c004402c220452241400305d600550f082804220301d8400003038407840e101491150162100c008a8091050400700300c0d4941c004000c030020a802d039925120062000b244001602482c0d44600e074020654030348204407200c40c200903004100e50315000c18611942d080b50000e042c4180c0c1410045250400140070343d01e04160020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 248636151 1250 248634901 248634913
    0x14161112120310080102130911120408090a1a18010806010503130c080307060902130603021c170c0c04060602060601050a1206030c15030501061803150b13060620 71
    0x40715052030300000d14a8004004056020038454000e001400d805441c0003180800e580c03c10b0549025180825516a040310b000e1181d880c0b62150341008d90f821035001540b443c0c1c2ca69505012500900c0b6580202c3c00034402c0601d080183c003048001081c0303441c0c000341c2803100c40c400800110380400081d52031358000760041c800b040d0115a0b603030903032031203a10498000307602d15030750400e45085802c071a01c01d44003243c0e511500300a41c2054110300e00841c0c0400c1d0308001044c11940010b0011002c41400007549480e000310b0002c0003500c1032101d480070b611400c0d01ea180c0c10700700c10f2541e8036401a14038500460600382c002079810700001c0d2440c01004140c4550b420600c4000049940d13440041c072500740300d503c2d940000042509403010318060041b1386158480d002d07840c0e00103815100d045e030068040060500000c1706119001403154140c0b40e0004281c0d41d40c1003042c07440806420810011a070000c01201e408803030145650102d0111000c07904e80e09400c508000070503450b08a4041c42000c0b9802c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 248637401 1250 248636151 248636173
    0xf081506060d0b0405070224010605070813092c060106020607052104060207121803080705100e010209010e0f03060f10090507021612050c010f14161112 67
    0x180203000c0d030541440300010f07180310b0400040c003518015901c0c0000350300000b58810b001285000b12008003400c02040038469458200010014400c44101401c0c640005c02c0700c420944208414234001c1102a409104014484a01e04e11012145804050318004011000341c203c80c04a201412107070103801134501c81e9240481506c3c02e40c8401c100c00c55486020717840c480c1600051240b28003c5010b0f082c01a2030b4080b07894290103402c02c40c2c44103020f0110007244030f490701580860b004144d9030b120b601540c03a030310781c2c1c54601e1038969400ea40080182c00c20307500c0004010150f01410307500409031382d0558088000000c0c0030501004152040e0903811490000700350000107400142c200620b002528011680c8050b4941190025605607005801400070f44500006241c544400380000c46242c100b480a83d5072402e50300d0a0500c41a41804405800ac1c0500d0740a103c2209208001740d075140c2c1d455510240b041c0461180040c1100c511804078401c000134280340c11000c2440d00044024010300c025 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 248638651 1250 248637401 248637409
    0x1a0a1d0901090b060c0f010e06130803010501140f0307020a05100603020f10110607030b040b0a05130c03060503150105031002070506070c020d080d1508010e0d11010f0509070f081506 80
    0x1000401ca500704c0010442e03000e54900402010200314500300001640040c110b6005041c1035014090380c441000c1e220f02d4a0100750601c04582c110348090800303407402001013102c0a510301440c10044044400030040041c19034001c282501d00714451002e40711590310020409046414074080a9088000e04000000a091804518101000c64204428140f191109403441d0140484528000980b00e40005460703050038051041c490008540711002d40e070a00000c1034850300c10b41c10100c1c8040d01d072128802c0c280c2c007a9010101811002c1d00780c8000401490514010754428403c180c0244076000f80085104103510955200562045c040d0119496000045503203d40c103803001e0b0392103d14030109000107000c903801000101c11806001c0b075868504000109000500c8e8043c0c0040d9040082214051001280d110380e0403095080402c0c0600481c0740036170050151700300d1007000c00e16000c00c3c4030482400007400c0c011200e01c035120143c1c494651180640310040704e0344400c590f0030b40c90b01140312490 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 248639901 1250 248638651 248638661
    0x409050114010b042108120403090e010f061701060c15180b0a0c080705040504090c05093105030301060c060e070e060f040905251a0a1d090109 63
    0x80214008039a1040007159550640340a030700c030000c40d1000103803c10092100c1e02d0b082e0041101c0100407202c04103940c48602e002d00c41c0051800034504110001020540a450800c01030b0090000c0000345603150380021604004a018644c04200ea254441441c00e014440c118160713441c80d5a445025007450341c40400c5406420800420303261104520502c0c4441c031414003005900648441410b818580110b2003100c2112040804001c00c0100300234071550444c2c1214210740090303400140010b41400e110076880707041e4014607401644541130041007060b40540805d810b1704a10708c5007078150001d501504510700990b0050160308144010030049001c7c030042000740c1e00490000c41c03603100d100c00c1141031801a0b0491080c14107030b44180420b500b0444a00400303002c042c0c40401881c1141d40703881d5543c64940b002d00c00d00c802c07080380c1d0340b282004d0210440014080030307440d480003420814040149800000d0707600300041c000149022158041a0b0b10446030030081c05c0300410707074244011000504 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 248641151 1250 248639901 248639903
    0xa08070302220207060b040b01020c1e0102030c1501080c03030703080403030c030b0d050703061d070e04020d1209030203162904150203030f090111030a0b01090f031209090c0e0409 79
    0xd80000d40a4000e02d503640000d00c4114441c00001070f0b0071503041d00b00320445144194550456001440400312500e4400c010340804900b120082d002070a4440100c4ca1480340c00d84104140c0a40380c3c201c44140c08024009050b2020034040d218800581424165203002d070b10b4000d00021480b40225010901aa00081c401c41440c03a0204249502e14040b4080c0033507003c0c1102c542e441100204148695803141c420485980786801c031840c643d10a1f4603560b2203003801050002d00c8035201090441d40c2e00d80c0700040a03540120800d40510a08038050121100c1e440b0680c003900685a04032003458034030340800252007040b002ca011200e42140800040640601d51401660007004085802d9a050101d50700304002c1341c0c01036aa83c908001e450034101c40141a141d201d038148802c60504510b4ed500352640140003010014500d1030280c0102d0b0f15520b00d0f4010300311070320001c0300802400111207005018601039198501d060340e40b1560007040faa89080b40e00300107401e40010703a0540ca403e0b00300c1d074407003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 248642401 1250 248641151 248641189
    0x90312050a09020603040f0615050d110622030c210b1308030c0c07140303121003020603070512151e22050403090e04050604030804050f0709050a0b0a08070302 70
    0xb000a940032484950042d58162120f404a07102d1a08104640c00744a0341140302c030200b008020320303100100c0c950002a0000030002c001d5252280c1c42500c03184242d0f81b0384d0701c108010250300f440c07a41c4110030420107030000361840b041681c400b00d084540d1040040514164071844006800700343c694081c40000503224002018206600102140b600c00145014464074081a507031244201062450204142e1080b000c08031b8600c0301c0c0c82e00e0f42d03000c02641c9401300000040b062075070319200380c12130301c80340340c1c100030352002010041c030000540c00f0014081c6171105841e454216158040021140c650040002c0d40c03003607401007501039032054480005109000503080e000640d804e030a000404014411400500710354620030041407560148030702d802403108680000081c01c00d612000d0711141c1c0103101605010203400800c0c10880e081040740120f1042000791083c8030748070014040906803e56006000d14107050700d024040c0342680b0000e04a0f82088028010f5518540c2030019078032110882411b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 248643651 1250 248642401 248642411
    0x60706050c1c0221040c0b13080307060204031203050411060f0c0a0b07180f05061309051f050618100e0a08030306040f060e070309060609021204020f04090312050a 72
    0x240441041c10b02c00c014507074016881d0482080c00c8a54031158002c26a45106120103000c0420b4130300c40f80e9000e0340d02d041195a510010181800411720050707001c6400c51100040307283c2441059030240c001d480c80f42d000d01d01c45000440044041c1c401c25200030b4501003094188203242d19044d0004c0000220300700c5200c1c00c1c00010a1500d040c00c48803203051f5a441009420400d5580d40300300c200000d0070b006442034025600305901041305180030301440c3d0140710002041c02209281c00350340001000f100c1c1050203240f81c039941c2c181c107002da0112454000410b5000c0450140303481829940c40d2209905100c84602c1010100042c0b03044810010051200d03c540c0a08551191501c040c05030022000455481c1440b04c14441200d04010344200a04c4ca00802445408c182100c0d031500010301d0710b0040344040450401c0301c010010740c2c0c031151449200003400700f40071803600d2403144100e0084810f212815400400d001c1607403075001c0c0050000b54520801615044203500c001c1d008001c6290000e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 248644901 1250 248643651 248643667
    0x1a040c1202130906050306130605040c090c02010209040b010f02151302030105090a1502031e1b0a0e0109171e07090c030506040c020d0e130b04050c0405031b060706050c 74
    0x80382d0052100c03100801d000e1506001074a8103000d810020324081d8014101440c01389800e081e8040038440003032445482d2008241844612000304014003108141000140510780020b8002c1d48100841c80c002d60030304c880f11900e980910703070007031404227560058201d1120000e01c0c4011808020b0281d0b54074090303040c081c40980c809215962003010740c0f6004000c2c00003a070501c10300103484540300a005a00410410074030034141200300c3e00303102001c0002080341d12100d6013000740007515998124268008941036810316030100c41d000000000b130705e594013546d444014102007482d101210407102c5d4802e0300c2c600c1c410001c2000010068030640241c414a585030716410050f03409845540002985840500c501460309201e81002d6401d00e00003050305140c00d1101030413500150b004688100c041102500d403201c0280c10091074241c00a00c100701500d086e03c2080d03000e03001382c01024080e10030082c08109480e030031000c1170031010300184120305151482d65024040c140040040200c144144030600c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 248646151 1250 248644901 248644937
    0xa03240b0901090b0403020f040207050307021e010e01090819050a1712090a0b06090a060306050c040305011103010b18060904090320071a031807080604060b041a040c 73
    0x8000380404186865840044800042005602e034000c00013074102080b08100595618005281d4010309480160700e0f84150700340f00d402c500858502a42020b040300c0b600481e4494030840d00c6120500b62602c41c000c003e00d8004403a0040a401140741c0c0e9072100040c181420514400441c47d41e11403022981d01080310341e00c0c0298055240d5802d01a60b0000c1001c13540c4400300b0b01c4176580121908001c00500388076131201c050080010b00b506008010100106040001b1900100040c1da00304906000f20b00303185500640310740c484e20080c0c880d54641295654014949003c83c1d0407503060004190501e0610900c06540344490502c960b40581c0810142c8960345440c01407620403030190319000c1103268085030308410300c205510680c400c0d400400091050108003801d0020b100e1180301000d440c7d80d544d0804002c0c14400c2e1340c90070000d100d04000082c1d04100010079600c241d10542051010031083c0060000b541c1040000543d0740008800f01009414036901121041d095847e241400410b504011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 248647401 1250 248646151 248646221
    0x606091e0604110418060509060d02010503040201140c160510020705010206010b0d090b011707290f0d050405100f14010b0a030b1c0524010509040f081603030c08010b0a03 75
    0x103102d072a031a070108010500d0223460050784114269103980c0903d130580d000825600c00100001c0c10b02180b6140544542c50380c806860180402d803081380c0c100d0002c81c1030440407039882d200e03651049a100d0b1084d0b00051001c110705045540613002408564242070040d11985c0140348030842056403a1010008a120000494000c0c00b40c40761100566024020b01414034209800c9450702c030303051240c2d05d10346141c241e121560306011803081d01d4440d80340320703030702105482900d442002060404050000f0b00802251078901c40c0280c5e502041444010103401c800e454207000070000d00d00e545e20041000ca00181e00515030205980b9001035a240f1b4000002c00820505c902e69034802000369040040000802810409200305003460761419104007031900c1c00c51050080c83d000c0c12403500031604105142003404000c56000002d19110150017914405544100c40c081e8000780c201b240c9020b41070b0040542034143c0b543c482e56a490940510015406400915803285500124981c2e4441d000d80341041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 248648651 1250 248647401 248647439
    0x303030403032c0706030209030a1203020307080f130327180e06010f030206160f060b09010e060112020c120412050f0303070c030c0f060e0606091e06041104 69
    0x6035440c03a4001000004007220f8008000240e4108000c80e9007500081c800110b5000d4074000d0794400e01000480c0c10031450040080207004441031090000d6019005580300b11003070b0361440a65507070700380c0701e00d564070302900c008500a034031480c030002180c030800381510103003031500309010580c85440d03031403001e021660700c0b11030040090b0000d003100000720b010341078004001000500c41541446654100404144402407144800248201410341c1904c0700620b9a90080b035051014556400c20401a202c7c05004510460308a0008908512107030850b9000e00e44c185c1d119009404125042e200940c04a1128049480380c3e141102c403d810000003032010f804062010015402c2c0743c68401e1408400010035a12508140100101c1903400b0028480040e01842c00c00528101810100051034041d5000740c01d00d4105401d4400000002429a0042c50140e403d40e04a079540328122100c01c00303409c051007120503440d001c86d5151409030440240500c000908038505a0b842d5050010481e003800c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 248649901 1250 248648651 248648657
    0x902030a0e0f0c190f0e070201060b120601020c0a12020904022413080604050d0f090506030a0e06100621060909050703051b06071b08010e070e010b09060301170109020303030403 78
    0x10410403941064003c80008000303000342810480c0c10040ca102d41c102040c046d400b04280d070f000000d290b55100750840401049002042982c5517456200030070308000403243d440c0175105a1440c1d255038144010100300700d032002c2030760755001c01d51a42008042400540280da109150030072030300d0081c0400c0c2d02c031103114080000d1165200400701000b206000160b124159542040d8100404507002007484a40c081c0c407450b0200400c03d030400c0c00d96290002c0c0d04110b400c884007104010300b03600c040c0c1c0110f84000110080381e640f0340d1803400d83e0306034808038094000054820411141101c54110000c10381201741c00c1d02160761a11845860300300c44c40391205551035881000104144542440f00c0810001c0c1d02c0c0f2041a115a0100803c15600c1a11001021980e007400804040042c0d0800e50b805030003480000c0c4039a0404104103030741c0b03011a0040751000c03d44007000165038121441110350b445006028941540c0c039207161443c012041c140034900c55500c0d09005801640e0030f0000794802e5110703407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 248651151 1250 248649901 248649913
    0x90810090201080901020408060705031e01030f050f07050a05010f0203040e041a0106080c0a08180607050c07120507030201030b0607062a0302070507030b150a031115070b010902030a0e0f 82
    0x1000041c00b40c100606913406903441040203010307010011400c0d580c041c4590800d15501c2d22548034851102d6500c5a0000000c02d11800110801c5000e00700000c8890003102281d00900c01c0300750a079201c40152007600d80c003050b01841082254007490301c44c0206d00742401601e04140d55010400d2610204550480310340071648e100c0400518944031903805403035149842202407800140265186c800e0496010034091510300241d0326140300c2032005101800c000645400742080314001c0c000c0d4210309030b040c40c1030044c0e03040400d1500035044d4084113641c00400030082140f468005400402014a255401c4401000140c000c550a07025050b19103002206201c0ca40a140c4540080c8034143d090340f108041c010010500800e200186540a0302d81004441c021502d800807015212050382c01460303001039041500009000c02d440041c0e811110949081d00c1c40c001c01540d81c0118403d400d00100404a003070300501460609501840c0d0084252400180701c141d5410070a2410080c0c0348141d00030b9000ca = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 248652401 1250 248651151 248651153
    0x11070312110f03190f0c060209041d0f0106080109020306040209040602091e0306011512050a0e15100501050702010903030e0d0f0602091305010b16170c06040507080d05030705070309081009 83
    0x3403c5083c413090401d140c8a041c01c14940d400910362684000c02401198003c111035441e83c2e01d65004110a4001200c140c142103042c8034865180d5400415819583d4a1310600140c4c00305e060142210103940140500f10960782c2d0360821074003050241080c2c40040e0700f0b01000d1000d86130007034a82920300740d002007040c2d80c440d10403c051416005030011030500d10030000d600f0743e0715000031940300001c03080100401c10741c0d90f11481a00600407406002014400c414401c0c04c400d691140d1076004050076651401c01e203440b800155568402c40030000c6c0000da81c1a010001f09108038208401c550009102e4003400c00691038403140596030303a9040e00e0b403d60000740d002d9645800c0d4607818010030b0b40c8070f0a00a56140080240c414080c2408182204508010800c100310402106060320300300001c0c02500c80840701d084599982040b1004c0350140f08200300425643c01c00188a500c0840300c0e5600c62a541d1180c008548580252100b142070021045c0c010071504810b001e040280c00703107231000046103509 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 248653651 1250 248652401 248652427
    0x39120c08010519050942011e090204080607110109080307050d0515010518040914070302010f020c0303161401060602101107050a170712080103020f0111070312110f03 73
    0x1302802c02d000b19884000d025485801d071080d40c1244c01c0e0086006124100960015100d4845400b10009800404000884c40f000c8031084031a110092050940d51641c9400c0752208920607801902c100350301030000145014030508809a14001c0c0300004544000c1c150780710095a00b09480c40e401251021071b0302c55040b502441000d500c00c1180020045c00484d007000a0100d215184c8004442c100c510f00c281f51503203403074018044080d03025031480c0a89902002c40e0b5120000c0d40400c81c00101880c04209440d0301c000345440c0c1d2003c004014518081d01d041004240300f089003003c540c41c220b004401101d2110078440e220007055150041c01000420301d40080859810290021440340b082c400d00c004990000f440520079540250340000c0c4411115003020a0b00510324002c090041a411410049038014000c9040381d10a8800d451061424001990000b0200120030641e86c062081000403407104041110103c40078200200e040c9110400b05003040c0c40c604013800075a03c00184e016000030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 248654901 1250 248653651 248653661
    0x7080901030c0323100806010306200a0905130908030405010504030e010c0305180604030f030f1803110904080f04030b1f06090e09031639120c08010519 67
    0x4114a8100910030540c2d00d80d820b80346010140c4c080e8520010005404000c010940310050040c1d0400c41c0c4141da5245001c20141501e100c0218110244c01007440b00c003a41ca800740c6114501507142c4000746400c0c0021321141c80c0c000d00244c800c40752102d1303101c004214200000c6004900500000c1414074240c10050710020701c42d01001e041041c00050000801c0c0d02c20290b03400700341010701e80b507040e0906500040c000e000ba60006040c084220240f68101500b0901503c41c2c44001c0d02c55601d1004210b18200c44200700c0e200141695808004d005601e240200055a101e4482c0c0c0078136040c5080140074220035001900100e400000550911861038002484101c00e9140422000b00c2d640c10400001d003115001d200344210b80c03903810045400c2190910a452204903010040c032a035000034288914080c141150f282d2100d2113a1a07280c00303100c095402403c02a04410801c50382d1454188605920241c800c000d071380c810404035020900c00d100307005030740c06251664104203003550707441402002c50b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 248656151 1250 248654901 248654921
    0x40b01091805182a040c0906080402030111030a0b0102010609050717040c0803131e0609050f01120e0f06070219111801081e01050105060d110f0708090103 68
    0x109000c03a042120038102075010101d001d86803008189030b00c80e500d42080e07900049188282d50300034000d4800440c00c070340c2c1400b03804104442c052146000c2501c10b0200b1070310203450b003100190b10840b080c45801e001c0e003401c41d00648050700008181c50b220400d01c0040d0001c0e42d05825058564904a40d690b034240140d102601c10b00104000071704201001828903641000071a0705080d04a0001c0d00340800340070280010402d4200752a60b4551299807030b06a01c003580203100035440d81a40d00d0300040d130201156020340d0110386500d40414244820400044184c10640d4100100c07140e4102c40110980500c06400301410b00411980ca0883c800c9814014000c00c190b0440d0b2040340080f80c10001a4370540c107051300300200492422501c004508503900c0fa405070040780740e00e01d00000e19076100103800d03805242d1344070740040c00c8480e407903910342070351000e21526038010000d0042c8141c0401560080c001c1900111101c1c2c90f1130b14203a07880440f900440003c0da090f07034000c2030490041d609801800c1d491 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 248657401 1250 248656151 248656157
    0x5030c071d01030b07020a140a0b0106020303040c03150f15050f01050f0901050f0c010903090312020a05060a0506180c0d06050a060206070e0310110403150b1c020a0317030402040b01 80
    0x16054244080007011052102500303003030541c0d02041d0114000d108032a2056040b4140f0740b0302185031903c480c0d0300c160400c0d040310152503040000680350b10200c00d90b800f03958000031102d03825203982c031502054101c841c0511002540d4030741258500000d0700c1a611030301c5640074034503901440c0004108000140c26952814030108020080f000481d89003158a420802d0a105d40c40d50340014844030325000d115a00e1079990310303089480040c103400071780c64000c60384a032541032010045080c041f41c0301c100030030004145a10920104182011f1504480c1d401540944603480d0030841030740342080410f09031a46180d10000207041903501d101800341d0b030080c2070256140c0610500e4400025511754008040804014400701e1182e182d0b60f060150b4400001803010a00032030040298240c0664058807040300d201070350380412429401540aa1400b004005000340201c8100361944010f904680104903030016004034080001602d505610300c040040c200090f48a1a140c07061108888442010b1414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 248658651 1250 248657401 248657429
    0xa030c06320a020912031305041b260414060a0c080f04170d020a120c0f1115010609051306140607020402040b0d09020a1401020d05030c1605030c07 65
    0x1a10421100c1c6051074208035000340d689186100c024000c1c072090551100302400440e48455000025000940f07050305c103411202d0f41e8030300700000c1300d2164006821008901200c02034003800361494485c008462802480e00280440401f03262403002c44084030358080105c4000703040d80d001c02c08294003c042031010081c01000341c1c0007800040005008544080c204400101000802c039503c02080b2048403c0701d03140c5000040d41c8019400c40708201d0001166802800345000003070089901c42e181c26207402074000114401150440301c2640031100700d1103643c4903d060003158032006c5000f080181c2e202480c3e10300346010005201d9000820310005802c003481445a1142c4030305400d044102200c0c40f81e0394082520214010b4061540006004c40300441d03600b14596094000e00903030303803088aa000c0c16940300c0664880011002c13010a0050744080c450413040b03800380d801141c01608918605040c200647c1070b20200e00f413486411180c507003004c41c40700001c40c010421000602080c2c103501e00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 248659901 1250 248658651 248658701
    0x31204061706130e030c1606020d1e0e0102030c07061d040507020d110708030d06060e06070b19020904051003061d0c0d03170c0301080d0f020613050c030a030c06 71
    0x74040f520700032480385560341c80c9004000e58204000b19542c1c4203046041c0c3e154003540030746003600c0102c5413289801500404600e0b0315014440c0c00050760303c4031420340032134403a0040081200c0030980a80168190710003000180392006e41045140c008244070b5844402900c0b07000d098031110b001d08100280175505290604c5809600801c181c014040c561501c400c008038030802d164509441540041c02d1400009208408414160820700035a200707511203800700ca00090901104e445200c074040e01440303000d00800c140700524400421000442d003005802c24000500007800c0716000d03102c880009084d80010070400c04140103500419601040307010f1281146d0080d241c950b81221100ba120340e120708400c00c105801040000d40509683e20315418031b19003d2252459940280103e11180c400d1180307011280e0f115120700040700780c10380d0280c502a01e510301802a03206940c04119481e002d840c205881c6a10204081c3e082c0c6402942c03980003c0c04942009801c4400144004c6850429844181 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 248661151 1250 248659901 248659909
    0x18080702040c0e061b0c12010f1503080f07031403070807081029040b0a020f0f070b04170a0b190b090403020606060a03020c0304240206150f03010b031204061706 71
    0x176211021407061002d004c4515003264100303074402c60f10690290002d414144244c84c154490381c02111010000c00600046803030240080000c4d10000380181400c21054072a080004094841c00340f0908000c92100803003144000c1c07a400c1100c1301d030b00265044040000803540601c9540d04a1402040d100a040c10000c0c00809a01c04855031031605040360881d00314100e01e8000c4800410408000603162100007200035180c03519500081c001d4410b0400a0444003004240b01c01181d01c00741f0717038914180c505070702011030741c1c000300b80c1407098004c8032603407000f140110641c64460720400480200d0280000d0003103013280c828a007528013602031901044006500026a00e800c00d8040300d09a440318031414041f8040d01c10f06143e441180000300d070004002012100c5140888103000c0982d2900c2d0702c0c200e0403030b90384400300c0382000014650b043d803001c1800c002c145002c41c18400740c0042420f469020101e8501050080c130105496000142000850b5100340e0f184104220b200d481c190a0502074002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 248662401 1250 248661151 248661157
    0x6030607031802090106032f04090b060d090b190603050a0303050421020304090509011a010e062109010b01020703030f03050720150702120f030a18080702040c0e06 72
    0x8030080c1a034404089006030074504110700c00070f60051400196685510000300076026029011030883c0d401c0030f8802030303405036000d50144690407010f000e042074074010713488021301003000c5540d40060042040202080c55401a042c0c0a401010f0115890500d41503a03a005d180140d1503841c141c7c40c22105000047c00072034a14045a054940810140c0341c40c2001c0341e043c000303150084c248045515494088903000b001500c111101140100a0b603594010786a09032551900e80e11300300707260301c00000c071030390302680d003d41c0e5200c0d01400380e83c24191076140e2020000410302d41415800c0300281004112242402110a440000e20141451528656014211034018498401859200d00004030054401d003280c2000e00843d070290303818281e900e03147c2c5803141c80140c1b05288100e00800026410f41c000181809402c0207481d17000d25240d03500340664007642001d0a042c0b001c58a0740004040880d4410380e54041c24010148560303038221520402c4200c0c0d42d8510003905020750100580c0080d5945003d13 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 248663651 1250 248662401 248662411
    0x3020304031b0806010801050106080f061c291005060c030403240507030e06010f06050703050304080405030304031a07030c1e02010608060a020903160f03171c0e060f060306 76
    0x85080a0210703503218400100c880e00004502d104e00d1000003082181500031314103c134aa91284520347d114403e00c45c0202c4022144241c1181241555465031000390114100c0207028040e03080c004450704c070610300b2620742d011112184103040002d015903228041c1c4410014003048502600c2d05011401d00760310781c000c0e4400034000b114070907008500c44140c03944032003054001d40800c00c5545007030000035006000d44801009280304010021035240e0741c92981100744d450603190242006c40e195401c50352648002c2c403c588401d4240300000c0c051720100080c0c0301440c81849403400242c036502100400030801018081054140302681090640003500d26180030341b501c2a44a44a10310315084c1e0150031140d10405541c883c2c3c804110080780d00e0f501404c1001000c03002d546070961112284040c40313006000f44080d11001c904200002000c0d0500707201c07d560444001b030300b030414015042910352203804400e280140c807045001e0720346100b40240341e4403982d00d180c060702509062020075a03070200181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 248664901 1250 248663651 248663663
    0xa0b0c0c070306090b151012020a02190c08100510170c03120309010c0302040506030a020a090b040303020319111c02030702060c0c120a0b0f070c211103070302030403 73
    0x600d0180c801800c0c01a00051074105074103104640c0d05140588120307104950650141b480012002c080d49025181c0611149032a038891410803405113a0b500294400c40c05001903100c0c0c48000001a0070007113a180409015100c9548583d15004015052600f50540500090301d04000c202144840440042c1a1090b4115080b400c42c6949082490003007036180c2507501d8407522040d607900c09a45002035210301c100c280203005009043c0c800368181e01960107000d50124050000907000c0d82a83d000c1d140c9122246850441c65130b503a0100c0f08d156004e40c2041d40107800008081038404c0c0b0310140c1058540c03161401981003481441c6203074031100c608400c0c070300407200100300701040c034420405d684902d900100400d5070b41111303004040c1d403510311441c100c2c015181c950720f8401501c400309424802d143c010314140003940c2c52070780302c20101400401e4602480709a44120300031550701c00c80e004a08100c00c0c2c03800903000d9002d4025014200003044c03502c1c5507208200580000e0382c080185c0b03080b241d1180c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 248666151 1250 248664901 248664907
    0x406021504140f010b010f0c0302100e0109020901030807030e0913030305070201020f04090f0c0f140715110702090c0f040e090a02060a0203031909020609011101140702010902030c030a0b0c 83
    0x460400d90140350300328102e840d4480c0c2c00d09400700f404113603c40c2d9403001003600d0f4014203541144003541d801c840300340c0c0900541c02100010140d407000d030300103803015800c1d50b00004542103243d0008503043d00030780055801403001700703821003011b800c0f404039006034070220b41604841c0307030403417842c070341302040460041c10151188086480303079000750142da0303000b405d010010791903d8484100f0b00041080e1141107140a0030001c4008a030780c020b07d00080302c0c01e030540d0f039010001030244140d0b4082d0f11100342115014020203070000c0104003403140c0c484000547c480076a41d203189004006543c1005403445200c8038041064910302c03c072103800c94040390303841c002c107404036540d40a056041410755030000e5000381d4000b60f46d547c0190f000c07000b188500003204400401c03a004030030b59821114000760081d00410104900582036001c2c000c0c0301301301840300d8000b050701e00481c4020103d0103829240540541c0d141c00c210b00440c501400340f18420b05041d4004c0a0141258460340900c8030054a880389040c400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 248667401 1250 248666151 248666153
    0x7050a02010605041a01080a0213031704180e010e072612031608010605070c1701021b011a0102030909130203151509060f0d02280b0711060406021504 66
    0x1e4000c04010b0000034020840d000099280b416005507094005000400c9540090b07a088403910907030310070741e4020507040300700c03821503480d2450334a440050004071081808001140d10341800008803000c00600301241080c840c21805082d5901d03102c0848094124080038425410310b81d080705110441c008000000c840090a11410540c4001d84542000c0001007040b62200d44e10300a041100e03016514600140e0782c50764201c81c14003803403a00800442003c01c0401c140784002181d070030b00141d034100040c5890400c21a4200c0c522007142c0c50903007a512080031a002080d40d50480365222404c0c005503107082e1455000441151303000f003801d00080141d0340c000c010340d10204030110928842401802c035600b0032010801c1080c00c5440503a100d600d43e0700003d5a941085c031042c0130036102c054036030070b4115119420001852160300c0d110791400007285100c003100016444002c010410190760680c0d0b402d079400c1c400507020018181a01981c0c04001c100300711640021038006006800d20803903159121 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 248668651 1250 248667401 248667403
    0x1d0c0d030509040f2405030d080106030c032702090604140a0903050705030a120515031b13060902030a1104050306040818040f0e0d2a1a040b0406050603060103020907050a02 76
    0x4015082c00080d4070302104132405c24103120401ca201c1942404007601507a40300c1c03c1503540c2ca0901c19403000210300b000100003960181d046090030011504020540c50140d41d08604002c1215115180f00302e081b20640c0c0039070a00b1055141c101c8020f8030b0600440c0020a271039281c943d4003620301d801d4a84d503a501d01d420325204006035507020b50f000d003e803a502c5001e0341c401080701b0240404d03e040c540c90315010030002c6001011540c41d008001d806801c0030b1f602d9150b030509100700540199009003100c11a0303030510b09148581005030065050040c1c6071300f4841942c00c103c40300f80440c09455107080206010fa941c00154040c2e01560100e0099954129004a44034072000c0c540920b0700607082503400e0302041c01e150010035001c1060011101c3c00d420710b10b02100c82100c03915202d10460944010b201d00120f454000b803040302c1c05481c0c002e0000040c1940418805002c842c2502d070040c1c90320920040154034046c03c4c2d00035900710006c10280d411500040c001083c05030804080c44800507010042d280 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 248669901 1250 248668651 248668661
    0x317090303030c030f15100302070302120d0614030604030e09091f0506031005220c08030706060f080a030f050a0c0b09010605040f0912080907181d0c0d03050904 71
    0x21016054070384900301610100510f0300181d401d039420000c1c420005085000c500400c0407900c40051800107103a8440340300398025484140154118041c0c81000c91071014044001c20700f607618040c00080130741c50288880f20a4940d0425144242c002d8030034800401e43c4a00c04040603c8102d4401601c0c0c1c407090080b0b460402c00424068813080032903000b041c02c46840d840a4802c040560683c0c601003129402d15048813000c40d00f18001540402401c030f01381500c9402080990b1180100d104019101c00e8428510341000e04100e07015603c1d05030034440c0400ad801108024a40703a001051518615035004e03201918494440d02001400700d031102d0403521440d6030701c408a42001c240740300740c1440c0c9a039501800880c09003034095801e0001d10350801c145441070f030700480d4001c640035081c034245007000c50311031a000c0c0c00486544280710012900c400d1460016400610f5844001803441041031009a002c982591600f055080103085080503103490007000809903042c50119519403c510003d80140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 248671151 1250 248669901 248669917
    0x10030c0908061501080a0c1e09090509160b070803070f1e080406051b1b010e190c051203031306021b03040f0f060f080402010201180b25090317 63
    0x40b18000c00d000d1400c048041c0c19030030440a070b8802000b0b65440d025641500e20703034100e2600081101e1919010068108940c009400c102e00e4001c142c41d41d40e1034130109440d0103030742d040140c5d00700c0f40d50140320324443c0f0403c0d402450340038107a40c10140541c035442514080140740105001380c14081043c000d10810104c00544000105c0c60084550094001c9c444041220221031061515000c241e40c80819942491822403104226140082d8640903820b5204000f40fa0a060b64071807110f045400800d2242d10f981100010740c0e1a19030b60982000d601c0c20035564004c501480094401e03250800006c02200da00440c14048102600103502c1e0440c020f01c142281c0104503511000c101240c000e0100040c42111405901c0c0c1e0340c000d456410b13400e24440c0901c6000081804000c40300c041c0c50280501c280d000340140000a80f60041d0b400b804512101e55004580c4426070108003c03803040b540c11286107401c10340c0d0070314131a15003083c1d001d0700700b9105010140092001d2010704408440d20310841d4848 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 248672401 1250 248671151 248671153
    0x8070314010c081b2d0a0f11030901030b0a0f0e070e01080601050711190f0e10080601030b0a0b0a030803071716051b01020a020f071406181914180610030c0908 70
    0x8817041c2100440c50b0342009808200049860007000038051064100340341c3c2c1d000340d2014514000058006400821109040d15082241d50800040142414182c800200040306600400e0b15000e0b50041c03000044800340350510250500740600e07030b603100054486195010b01848403843c82d0f0400120305003907085050b606400120404541000300c1e944010484845103410314064840590414010710540201039540d4410360040021410001c0c480c3d4008070002c60014101c454400410a103001541042d40c112400000f4031541d258010610b18141c080744000c20319a003800703c10010030708081d041d50002c0210120308289c0c2150112010600320220340c008640c0d034140300344007030b4590f440540500301d14090f00f0b0001036840914070011900c07600c014a40c520b0002c0007882c44151100d540340c1140c001d01040040441c0c60b81a202c40350142c19000000f13905291044108050070790940382141c41c0d16002001c0c0b04854450005101c0c00d800e06041c00b080400c42071008079442000b90b8052059 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 248673651 1250 248672401 248672467
    0x40902030d0f0e1c0809010c0c031101090b0316110f0109051c020d0f030f0b03030a02010902040b0d170309010207021827100903050408070314010c081b 67
    0x607a03001010820958290707200c0d031402040800400c10081014410b08800300c0c450214040080d0794000100760302101410302039425041c42c3c079004903450841c0c00499500b182c1141d807481e190780140801c4001d080003815580f551a1102604800702c04503466841400a0203603d0152980c0a200245012841400030042d503c41824010b54845008210001d0343c4610000d4000d00f03480815110340c1500c850b290303804001ca031810100e00078145580042c070955a1002c50b501a59410b00c01004035440360382c00419010001d0040208030b81c0c20240c414410741d43d241400c8002884000060500b23144a05001d88980ea101041030280c42100c100070340c4624182025411107219070501030260040d400740344103401000400608114498050304000e604c6030b1030301034580c0807039048840d043e4440e28041d41071030341d2130b44e0480c42c0c94860b40003110b4417402c02007844096103091046040e41c03207407032034402c0c22810003000060744101c54594035421308400140700020010304e0704a54020103002d43e0300700300c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 248674901 1250 248673651 248673673
    0x209060f090f01050909070f0512010314010b010504060c0303110903010603080406140301050901180e0303100810090b0f090a08190e01110705010507061805160602070f1404090203 79
    0x14032584098190307845526000807446041d44102c0949441030005804000b20b034485a90030350b01c1d4a003a0903c0720810004028000000c0289410640254418000392a510b850a210f0a003903c0e010b043c00c60400070103000030008990321801c1c1026858041c20001508040202c1c40443c1e40302d84903007180c01d507080903800405c02204000400c111a80e035582c0788540480c6204c0340580784070a01c0b886511208041c01404440010340401620010806c000580e508042403c1d03425030300b0440302c040c00e011302d101c01000020800d001d02c0780661820202040f4200440d40d803184418800303010340b0709501500000401c000d20420110b46807540040742261030b854030001d040c95201665141c9000140b00c140d150019500030080030201600d41c02c007802c2281d080c0401115141c210b8074003a80c2458a80d00c04540e41c07503660400b01d40003401007011b841c480d019051040c1c0c0034002ea0f80050304560018130300b0480d28810b1140a81614100124001704448400008026040c0d80740041e505004040e0064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 248676151 1250 248674901 248674927
    0x1e020309031002042319080105011814010b0901120204030c140d03020a0803062d090f0702060103020d11030d11060117030f070303060b040909060609050910050406020906 75
    0x2040200301101299109441c60035920142c2c0190b00c51100e40c601c40030510345071618031101c1185842d001801041440441110788580550594403411403070359158010310100c0c40380704030300c010400d542c1e10500c40d44c00c0e080f0f032222a498051041064165010035104590b070301ca9417022404028a00381951610b890b42014880d42059110314030094404584d2640e00e814003001141d10306402d9005002400b03005d80383c02d005079000902d2103500c0151110b0f81e807241e50a883d50102c0d10030b00c5100b0094100c02e000d00b482243d01c0c0283c00b403488007101000700883d4943c0000d40e141540d50541d018018004280b40c900004101c10010640c18060490290012075100303580038075a4220904864050f40d84491140243d1150100c020681c0c00800403186240301540007030621a1213442c0c005100340e5540038006007504160030440610343c84040e038030280441c500402c4040c0038031000800007814606c22056035040d44021110005803607600250602116a0560350650b001610b8660b0f0b03070028003485 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 248677401 1250 248676151 248676157
    0x20405040c0f050711120703030908010b061303030f02100617010b04021918090203071706010e0108240604060e011103030c1c0b0315010602060609090303070e011e0203 74
    0x1080c000c0303103800d15441905110300403010740154151906880c2c20f40320b03116801c1d0740a401d40c0a41d003101c2d001e58242ca02e06030800034400203501969600f403410b8103084113103080d00c40c0e41410318401c1c2003d0203000003441c50001428100e0f0f40c9400c00c0e1460100f08182641070003250700c01c00c29154900303680018082c041c107191151000d481c000030064034400740d003040128000c012038000b2000f0100c02d2032945030300480382080010b0300400344808040d030750001d040c240c0e80700b1a00d98000a0b000d10303405111400e005000c1d600000242040b988044200c80004d0020748024402d0044401600368459071301560b00c96500c2c1014082c004039075440d150100501118a400081400603800c0260a010401c0200030ba03030003480783e658280d141080340724030b00b0038425100d03260719041d0f90740c0e00c80700110355000c02c086800420282c4010b80703107625050010342003150040c42d290045d05c82c0b400300280c000b000f0017203d6121a071400d190b40710705400030048034011130008040c1590040c04902049413034002002e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 248678651 1250 248677401 248677409
    0xf0a0c05070306090212060408030c1312060b12010b0310110c011109010f021b040903180f03140a050a080c07170114060102070f06030b13050f010305010506010c150b03070b030a0204 80
    0x5000400c00b50042400d954030700440d80904003010920101d6400bc040c5401808440826100300a215843d5194481d0300f50088408842d1300d580c816400c00a800c000a00000f00b200c400000c01c03c1c3c91560011a454009880d00a00b107199200502d43d80031500e88155012441194001c00900c0000384070341503280c2c45250054041141c1074542050b952001464220891180c0f040d1400c0910706000c2c08007400000004030180b00680e21031014180322100395500601c000d145c14000a032035801c10701c0344914060318180b1643c00014002c40880c2c0005580326007583c1c455100d42d540c0168140c440d00344038040c0c00440a044514030907103010340e4150070510020a85406140442e10780200690703407103002d40708200c98402810410031245000b5400303071a03c0540500780d40101c000c41760080c02180d6003180d144da80c00c0303603002c01132090150900c58698840c40c00e007000d4000210f95100c860380304148000249550384c842d416003296403070900c1040010125410a543c42e0b0a0079910203020b0f40090007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 248679901 1250 248678651 248678659
    0x9190e0606130c020a0f08120a050610030207021c08040f09090b060301090b010611030d18030e04180f1a0403170c040b030f06222f0f0a0c050703060902 67
    0x20510103603010f0711540d2100780b42500208018003065540191061588409032503603503060003980140e0b100040c0c107612603c00207000291600c2c044c410841e1200c0c2c228802800c052050112000584400c031088640b03429140080310515104e107002c104a2280f50003844444c56510341c00251080240c02240300305110781700000d40d0fa6940d80500d400c03107900e64005446028060010070400d40076240e04a504822603094a20301901e500e42d02d000c0d6001c0082440407620070003115800d155100210b01c0303000300c00b00c0781407007507401908a00409128540c030203802c83c1005840c540800070003031b284c071409000d00c6500f1515480e0504015004e03120202440c60310001110000799150422400c44050301c07524000f150664442a681e105600c20050000d40c00240003105041025250300210071169604207010035420b068001c40c18189401054801440c559010003a6820784074005984070908441c0c582d50722000c4210045600805102e8042e129000c0c61f00d020060005540012031580c0c0255 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 248681151 1250 248679901 248679919
    0x10e04390b160803090c03071203020114010510031a0a0306090b07021f020703020a151d010501120807030909091a010b07030903030819020c030c0c03030a050909190e0606 75
    0x70084140710b00c560700b0315000d0407540095a10015504201441e000002c081c1195480e090000100e40b8180054000c1380355400d40201950406a0900400740703c10900d80b414070b815490403001c0741032200071008a100b450f0f00c5d840000d4001301c8403954090185001004100510355030304041d8000c00e0f2006c415250609684000b811160000802c0d4810810305200c0d205201c6001c1803801c000d4104000441c1140100703181000410140c65005411608041e070010702c0c00300d40001500c249009010008541e41002c004100e000d040175407160700180c2000d16942d46428624044442095580003285a070345080c9030ba2050004090b848820612501d80c0841c8590301d0b103400203258000d041c8010300150b801c000a00000c0e02c1003480d0340c0c028404030003c40514178001d058500f42c2c0c0107000c501ca210383c070200d60790180443c2040015641c4405801a501c0c100824800610922402a10074064540710001c03a1181e085a0842540d00c40c81c104100066451040320548403807040d140348e44120860 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 248682401 1250 248681151 248681159
    0xf03150a0e070e0f070c0f080d0e0606010e0a0e04030e0a1e0b030f130503090d05030d060506030c0708030c040f0b0304060b0a05101209080a11071508010e0439 70
    0x30600460164401c0c41e130002290303888907021595245d00181c02c481c40c881e0351400b0f10004043d04050030400c250500041608451010f45910f0043c00408541c108265050ba41580d40c4407c005402959440b0800d0f0f101c550b00c0e4201500c00203c43c0c90019000b0142280000700104107602c0d9052100d00144560301440d51200100c10b14002a01e000043e1120503000c20384c4488070348683e4104a2041d0b080d1b03400c207100351001880041c80b0240907205038100107200710f100c51491050340054901180e00c00d080d0300341000480c526004104004040c03460000111302104a0f03001518002c1c100442c2e41c3e840b49486054030905d94105840483d400c60a0801c00081031602410010a45d1000703004990318400310708013110140303488000c0c1204240d4038418440447e40007001802c2a5409031220b9615880b100308080c90655941d200794200743c2e200300c41c1020168420b10050445d45070700c1e40ca059586980c20840540d0804102e44040740d80c50140e400903510010303030b41c5264001e030154141c842540e9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 248683651 1250 248682401 248682419
    0x17060a0b090106032a090504060801090506130c1203210b01120b04060509040c0e07050a0c0201030b1305181b03150c0408070b07060b1c020f03150a0e07 67
    0x1111501e611034030742401440624825031124400034400e1104805000c5265241a000381c003089104000030040e203014021410f25002d0103005012190080103c80b0141d100e0a1321000c000d0440301035100240501d505010078038070301d070380a40043c0a4040c000005442c1c0903082104181407240624000b0006110b041c006101d6060044010303180ca0404105002c218801021038400c1d455000d5030305c901c041075503100c400c1030501c07039485a260419480d0418145a0360300100800880070001c2c100466240c450744035074561150355080c04c01140c5100840c00051118800c1c681040c0510328000c02c100c10141007174990400c0140c9602a02c0d2510001003140e02c40f00d5292283c00e406500c000003000b00158445d921030f40c0030340c00841b40c40c00d00d5110950907090001aa104900d002c0c0c1c0420303180140040c0c0e200d946400003044031800c1c01c00790721604900780110384020191140d420305c034a140c9161428408040200c0004c80d62011624105000c0030003010603607a4400b007441860800300304111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 248684901 1250 248683651 248683661
    0x280608150f01020a0222051303080c16060507030f0e1b010509010c0b18030c07080c010302180103050718170c030105070212030a021902011d07051003020f0c060117060a 74
    0x401030f0302400ca00e008036000c0c0f0580c003c501c056441050b61503808aa04039409214050003000d810916020188503424018442100980b0b0007a901b0b00402001102e0741234607201c20780b202c0c1d00403000f040c641d855810940051840c40e024130403546c240100310f43c1980c00810a915000d41d4428468101c0f82004011569802011102404076130014152400700c0e916101c00c56100c3c00700f012146034840c4090040f821500001d003051020751102506000c94201030081c503540e280203190071400d15915075002d81910044001103818161b03a1000314030000e02c295504007400356200d86145680d9503a8989026114400700d0311001800340b184801e05524041c0607e902880659009100f4a170310010344400e150301c0a0500c021855082002c074103c030b459000c3c0c1003100181500001140c0b0f0281d140c00340d10304580303040003025411402c4c0c03d0100e90303914024028000d031079103001610b40080411101c010321074150003940780c2c0300c3c0100005501c9100b90030300c031070303e01900d0075500300d07445901c0e4050a8403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 248686151 1250 248684901 248684929
    0x15160219061e02120114030a02010c11180a0e0d0c020904030e09090a02010801080f060417070b0a1a011419050f030f18011404030806130609021305010c1128060815 72
    0x18005030580230141d8803d0b004840342174041c40200d410303000b6100010708500407010041040900502c20040d42000764411035401129180241c55001002103005128081c0d03958001c0c4a0380c9050045024036100d170440382c40020700500201c13014108000c002d81c0d91500c4030303802c030300085000300040ac01c4d00e03002c902a040c0d0117540380144071548030759491040401c503500603c96242002d20802e000305907440e081c00d010300c075220b0000403000e88112689001d04851804241807100d214a1100f002c43d4240c00c885540ca21048040180c80061204844d94030031300c0c401110080001c41031005a02d504e00b180380c000c5117070341044840000389414550a0722966460010ba8181800c0041c1c04030b40030b400404c3e0b01110003040f42d6600180401d0417021135200d0b40080000703603400700d0b102060f04050700550019240900f003050040b245984c0d101404011200a20b0180850b0090140d9200c407016655464440180714102e40070344454000304003440450b611f500c040c1082801ea00ea07410018990b500c41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 248687401 1250 248686151 248686153
    0x7021e15040204110d0c1218031403271005010f0803040504020a0507050f010605030c06040803040b0f04050a060206042105120c0d06060215160219061e0212011403 72
    0x90341c0e41d41c0030000202407800341e0002c501000c01403038804603054464068240f031503032281c200170391138010f041080707032500c0c4400c2143c0c101900c240d030080f83d04a04040d1540d040265400d659681c2e41d015004207000462403502400300c3c240107506041e0700429100c600c017070700c5c0d50100540d80c2c1c0c2d8803448080e00003e06c0784444581040205025904194004207518261814060b1400d01551344440c41c082a6000ca010310303941d0740009000e01c0c6800d20444000341411904a03040c141011710711034907486271f0320440c461403600113002d050444031207041c4c40c018800203050000c01035498030040d440faa0304035000c0b964170090a582926490002c241600c6900450ba1040e00b0040018000058141d014240390000300302031002d80b040b07601900540020b407a42e5406132001040d50700e41c0c0304940ca005810408501100701d05254001e500246041c800200e80982030440c20403410800700415030000b82d1102c0d06070100b4100d0255034550020328001c0003404082d40540e0f41d0302019480e49200812890341 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 248688651 1250 248687401 248687443
    0x110d0201120b0303070c0b0a0e010302090a090e0a05010c050a12092001090f0f080f030c0a081b03040f05130b09060d060609090b07021e030a05071a07021e 68
    0x2180711168003031030b0303101405000c49191106540345d0001d2151940e1007554548400603c542c6480e5001c440e000720041c00382020350620b4424000a0800c450b2405180c01d15945c0d803070104c1540008001c1c54240c9a000b070002c003c03070b6080c80c100074455404034500303c0105d08603006a20440040c0c0c0310b83c2001e641c118070603841c4102d000d0f08010000000034407581c1080b00b20303100841c0e90400c2c405400c00801f030b170040040207286840d080d82c2c10902d03014541100ea420501000044030400324072600c225a0001409580762005131908004031100848030310240310110f800320321018001001320035a0021034100140824030465041524a00d00b1081d800c42e0105000c10040d042030340c0303a000382c1f51180c04007140c100e403158181d1003154401e08082d80c00b445c1c21402c1c400702c03503014084031600b80450405a0344010000608071b640e032180c8410001006030000c2c4100030700c802004c0c44105c0c0c7c0c611814080c468148110000e586440c00e02003900749080c8203e440036240c8000500d10310100c09883c003100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 248689901 1250 248688651 248688677
    0x90601090e0a12030204050f041a0105030612032b0504031e0e041a012601030b0612010c0c020301060603020c100e0a0b01030b09010c030536070f03110d0201 69
    0x40d06526400107072034881e110a01c4000f440600800c11003000075030340140c44500d0b110070410340a12011100d80500d142c910104422580c034052000c590500b0b0030b0113556512420b01080c2007000142c46000d142c0804100d1107000b030703102c3c0081c6461680000c001030109038005ca48074111502514000c0105c1d4101c007080351102c0c818805c100c030384040740c00d02c64081c00b50311020030140c1c0ca0342c0400e0300d0503007440b0031612225a048210341c3c080301144400c0c0803000007403e01348144e00c041800050b202440100c0007a1417580e03079840c611030840c42e81c0020f204c18207682c50058807015110200300c3c400c0d4240040415491710078404c0d2a0741403184001805007280e0380c201d9400501600a400649000d9101d2401c045002603110718001c40c070820000240b0f1601070182400c40750a011441d041500700b80c14040f4800b04105c81c0000300501000600f00304a00c04811111094580340c040500d0080c0c890020b940880c0c0032100089a00445e0cc070a540750000003040307103090100c2c100a01141c81501e07030301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 248691151 1250 248689901 248689919
    0xa0201080402010504050301060803091005090a03060203060607060f020a02121305062d03100602060c090105091f0f020f0c150309010609090c08011b0504090c020a0f050c090f090601 80
    0x20740050040c1046881e01d03440e600030a082d1106a00003540035440000c10541d5070500d0440400000c29500d40b0a05010007071000400310f03406448064034190300403020071101d55500302200d00c07072a400030003000000c45200d0359034083d400404460b40035002d0300c071a00d0568031030401141c45102046d16005c06550400040001c243c11400390403211000e50ba250f0701090400350310f0843d07a0003101000720380320b00d400b404010042165401c4513085402c04414000c0201c5a04260b0307a01c60750900b070082d02d8110700d42c00308814801d151000c9820b4003001450410301900072901c1e0300494200c1c0e080c0e428607001e55080716540c01900041ca030b0020110b1003000c44045130140a5500021194004514160b550780c0c00350559109120998540344806001c1020300c5007481703207140b00c01c46440182615004c9440260250003240300e05502c55813103040e015110b900c240301c8060344c5a4410300000081e20141045075131a402002000d00075480c601c049420150220342040c800c40420004100583c00c0103564 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 248692401 1250 248691151 248691167
    0x7294605070501090501020c010b09100f05010f0c210e030102030118110c0d121d0703020f06160f1106120a0213030f0501090b0c0a090b070203070f03080306040b01030c020a0201 78
    0xe40b02550f80d5040c0c01c000910a000405000221100225400712482c0400410300c6028289042c50072035908100152004c2d000e8100807074900f401c0024100060040903254543d49610040501800c40c40807410b00800e4180c2520094081d601e00034038401d01014903080707201c203016180c03103844100008000501241c01c01e000041220352507a0501c2c074044440c2c3d2401907540101800300d106c04001881900803446040f900001d035686004031a00c0003118651260074500010b030080340401101c8409858810455a070740030f64400902007245141459410070413024002c8402000500e0021403519041041d40d90409803202c5070300d420740310100d211009500c07007400c1c0c484919180000001103602c500800007094010340021031441154a4048500c1c100180b6144000b901880100f4080e64008081d40076903050f181455030303540300e500000380ba09403075606c080c0c1180240003003c810000681c01850013440c0541d000e20598400400650990700000c03079100041e88a610000b015620400607 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 248693651 1250 248692401 248692403
    0x50303040228060203030708070905010c0308060a150801090605040504030206071101060b0408010509060a06060f0503090f01020c0d0e0607020d08161502040f0b0406020729460507 79
    0x808101a00b4108020481c50301030340b003440035800200070014019000b0f030380941c0c4001c040c0f80242505050200284c2004002800601008803500000d0f1658503000410400340c40c00c8008d0303030449003031464014101202401514841400d010307000807a81498002c40780213603410740182a00c2c3da03d00d0030803503449a041c0d002d041d1641d2039100c0060348156000041000d040240d00108282c6012902981f41c0b00024106458842c940072003040042d511100c0b402c0c04d21502d00d80310756039072a030740c02a51a04124920036000c9510000e07200011000c00506440c898410ba250103c2481c540020071065005010000c6e4016150305c0304200000d40d040001c01160604880800505410f03032244c04500e45803c100b401803541c0020244481c200c0c90302064010300032401c81926141c14007000a440780400c0c0308055032a010040c030056941c2c0e170342c0c0965070340452207028943c031071181018010200c0030600040314070710881c80103003040e0258002d81c2102d482d40401c15400d150346015048420f54401c0d50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 248694901 1250 248693651 248693689
    0x10f020106030609060c08090f0c100302040f0b0306090106021b01030908121f3023280f030819050408090906060304050c190312031b0203070503030402 67
    0x1d80800002d8031481001442c03030180b02c0c0040d07502d84212002e01320ba00b000d00020010362103140c9090040800040c00601000191079241000784103400a8000c0d00a54100c1440c0750000c0320042100080030002c0d521816048800001c47d07666260207986070403c400190031010782d44040211b183d4013030b030010504980b140d141c0c1d903e40028100c484507881d000f5108107843d03c02c00165444501c952120000141400d034090001c50981c00f5640d00f80040c00c604241c21000060f042e00b420301c003a4400b42079808134075005030105042c0c640111034542551000131402154660341071400d0220746100c1c00d040d140d0001a1a240f048251800cbc1c4100707400030b04006400b010f031356450076268854003d05010340d1003003100540359840c0a0800c203607003100070200c50103400e086c010000030400c0080c0580d030000080e186010455201020701c502c20280d50800b801e02d00e080744c4c4205a03107505a01041c2c0114070150b814030350f0b549060049840f4460740070040c000d80d00600209000d807500c2101d00d54000d034034170307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 248696151 1250 248694901 248694911
    0x170304031e0e040c0207080604020d02060c10050601080f01030203101e0c030f0615120e0703020402030408180604081e0f07060c050c090f011401031509091707050606010f0201 77
    0x69080c5103078606264540c4001100740107510841c0c1028061240409003500142c1107880c14a40c0f441d94514004001030720032280c40b14480c0039900ca1504542002c2c1665003036034802002c90468030050401643d5003800210b0a1001a54410848c1c042c00e041e650b0040c05030110103840001800a041e502c19240300c0d0010302000f40b45450300310b104008514038030341c034081040100d445051085070b0040c0d00c002d079113400040044a4103503210045a41c034050145001540e000d105044a16019642e000290041d10000500084c0641d60000d0407552202c98410070b08030702c00d502030011500551244c00da82c0c2e444034841445480c580091000d0007400401141c03c4200410205807402030140e01c004041905e40b0308801c103008042c0b01e007401500c4182c41e00002400c00d41030b07c1140080512440c1111310b610103403040c060784648c100030f000f08608044405056200c82c2e00e88004e0a5070b90301101c030744001e0301580340708904140076106803640040180860340e44900040d50095108202d405c215541c0f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 248697401 1250 248696151 248696177
    0x20a140a03081f0e01080a03140f040510050c01020d020403022112090f030a030305090d0c050a080a02030d060803030106030e0606030604020d051501090b010e06160813030f0b0702150417030403 85
    0x140403603170b008203503040080c0418052400e02502c90402c400509124210400c044e418100c0132304100c8040b03d006440903076050352081c404607464010500c0300b010039400041c40010f09640b0b40c000c0c0041d01d000321024082c0c1c0fa4040c0c0700c40e854411000680b12950096071886400120000140c41400d002501041510b51102300007030030580000390480209a9500900800d80c5040158521100c05070811030201540368071025a94201400c0003003088800041400d6034500c00e2040c1e4814014500040c4881602c5540e4030b92207800074010030002918280c0314040700c1d20001013040c01118060013412140c0c07525024414160138090b0141c60901c22040c00055043c26110964000c00042c4000104145035900042842c6040c6148074171400e0140010341480610140d0513200f282d03c11101ea07681c02003424030000c61b0030a548040d050450b07006507a814440da15004500c50710042c0e00382c9150413880f030000401000162006000300001107a40c0c11036480f004001d5030001d0190400d6545d1540d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 248698651 1250 248697401 248697419
    0x40518040302010612082b050a2013050f0619090303020115150305061c0f0b010515031311060d1b0201060b0f1315020a140a03081f 58
    0x2055200005048602080181a0b080c03288202900b8840d41542241a140d110384c1400d00505004070340394006402004041c25078110450b00300f580b06c2c4404c0c88103103082d0304500020401201c88a840d039894644c0782603c590000c0441d40b10380100d1000301e2030355042c5402d00611100d88081d064100303c003080b20841981c12a0b03250b10300d841d0300303550b060005421494002e007921040d800c5403225044c1040e0038814582e0303010085e0314441c168600001c945d41d41d0000a010043c0710400050340300c40201841c010f0010050070b11202c54010f80043e04666a6003041c0300b1107004821714803200e1b10080c80070501000b50360b203262800b1402940c4c204004c1c10000d000911640c00701800440c05691803e902142c02261010f800c210740550000f00129850070400300740e0341c0300b440441c4a08010015100081c480d1645010015102001002c02c2508070b10901070347e01d000220003a0f4075008900e4003403540701c000098004070203905031382d400000e44030310000c1210440ca020540141da00e8035800880c05200c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 248699901 1250 248698651 248698669
    0x1050102071e05041509060602150a02130510090608061203190905150d05090d020d0c0c180e0f0109110904060915020a121b08040203070320040b01030c09060e060405 73
    0x205c42000340e96028030b8290075808075502c6500c0070055400102119038405041c0b08007a6002d40f0704000540da4401c00380c41d58440000d6500070139480b4140c0c45007010312960042c001c206482c0d80352249041a01c03031808100b5520910341060180350720400c84d070203502c1080c040340f00900d13000d03080c5002000d440741c0005285000d100d81142c07030100c022403000c59404c030b14055180c01c0103030745014001118400000030f40701c41170000c02da0107106540001e1740411803003070031f288002c00612219002905c000a030400180c8413104800502d442401400f80016806101d07034282503500c0346a030605c031040b480c280409184024002d039035056035400300f140400c0046000521101400c0300050303888445d200007501001818003054a154600504545c100c441030500c80000107640c01c00b16225030741c51000901c0c04207950801825844112400f80c1c0344841100d1035442c03110200e40c24032040d2100c10044044031f1502e905070000a003110400c0080341c0c00b40101d14078031000a41580d10380b58491020520b004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 248701151 1250 248699901 248699921
    0x91314070f111221070c080906070204020c0717070e0403081306020c0109120e1c0809030a0b010f05010f0f080702010e0109050705130209060f0a1b0b0406050108010501050102071e0504 81
    0x3075400140d900044e0090013842c01c607210562101213150170140001032901c05e204000411403040010803060550700d0700d0a9401865000b041035503641c00c0044100e40740c40441c414000701c150048003080c015240428600c090b08c119400c5141e256403281c41c2110761030350140100e92001011100c01307010030f0f564001032400c1d40c20b0500210f4002e03100c1c5890310410a0081c1d04c00200404c0e2922034000c0c0c1d440340f02150107441d102d1007800c402901400c20359828410046081d07071610601801101300000c62003498125880080c0812556079500e0041d00c80c1b600c4003003c0800034944200c1c07111007601849140d60005094400001c0c1e040003103480500f100d0507908240c5103a4020981048903203000e150400b80740507504002c2d030402010b01e0209442d40145030001910881c0843c2100d80d0ba4440d1110380c1d108c0c81100d840c0101181d8030300303281502038401e031010368a5904010001c01d05d0241405014101c51041c3c1c0100f00302d602d0040000f45210f54000b0f00307210301071141400509a51940580da01d90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 248702401 1250 248701151 248701183
    0x1a0403021501080f15040501060b0301080d09060206070503180c06031e06060702030d0f050f030411040515150903010e060a020c1b090406020c030d090503091314070f11 74
    0x1441d2120440c00c80300580c0269603a82c085007901d410581d01007840340c44480108119109900d852900c540074101d10b400c115804003001c00005941d10001910740307900000d07515449030741074451100300d072201011100c81003c66030810110b90fa81c180c4000d08801d080211058440c1541034100180f180c0e84180c888801201340c050310815140c0c1950141504141c040b20700c64680081940426180c62010200005001e107100d00100414014000c5528007a0310701121503803403070700b80b4040c01000740c41e80b2028011840c01c80043e000030300320407240c0400c0070001d0407942074005040c208a42d9500c0030903d43d401d952285040c0380810700404c43d40d8029407082001603266182c0c03a8140d0300d0f1221100303810b0006a0300c414034850a441d688080b54025401070000359442030b849100364a588140c05c00e940e00d15180408d06014448080080d004d00c0c10116500f040580041c850203041c1c4800d8920201058410300108030b08078050103d0180a80f01401c01d0003c1c00100184103041c0700c000702c68031b03401c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 248703651 1250 248702401 248702413
    0x1b060203090706090e04060513080415201c03111b0c01080c030f1e0a050103020909070305060105120717030a12020c03030a091401091a0c04120f1a040302 68
    0x714506101c220007034441da00d8002c18040ca0119250100c0304041d00c0a031a8580d04c0c0c01241005c3d0240e100e00020303540010f4900d40d50355941000c0340d103075507800d8800c0c80001e0300c902001e0541c0703d070700540940c4200c0c142c00410004e4442c00c803030a84410320003402814141d580d415101901c1c4070300060f1a40b00c40c01f603100000c2e0240305071031070308052440350400c1c10054140700300300c0410566400d880c0c000007051045d00f2159a08021035807202a030504540000c2034020401c2140c25903078200b14103903803003a02d0f40c051715141c0c29000c0340d403024640401030240d00f00000600140c1003d90ba04824040c03018221602c095845500707413444840481c00b40055000003889074203160300090f0f600300d4103d501c182180f820240c220301a4603400081c10300031100391a070610b601444240c0c0680458560204000c00c50542c10b480e010803907883d01846d41010760102800690245100e9081d01c040b00c207040044914888686d4407a04444c40300041201c01c5e01603000c03010f280c0c1c2103104040707108911036001444 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 248704901 1250 248703651 248703661
    0xf05010e060303070b0f15090a0c110d020d0806041b05180619050c01060902030a09021305010b0403080c030408060f09060f010302011b03050f0a05090a0b03100b0a1b060203 76
    0x2080034010410740c02a0301c10840540004c40004c1a143e2050b101d0650595580700c45a01940400c10184419071103949101845030a4500d540310503c0c62001e910f03803030480f038014803159403030380054001c0801682040d00e00f0f41c03c007030181e001d09034000b400510002d00d04211a14640c44104c115100c807000800200e0b60629240b1040e0091440e03450031501c040c00c0880002c2d200001304010b410700001c00101183e0300d40026401d404c501e0107011030700c3c415504d9242c41035202c0b00030500544160301c5407010b89041c080d208250320406040e02c2a0132410307071800381035031070b0b030f140a034800c1d8505010b0b880704120000d00400207104450041901440b1201030303003408000c40d03190101c0941010103829030170004000607030300070803560380d101000d005d042e03c8821a03003000c1e26036024940c40c2120601000465441140e4004020054040304407003826500d600e52010289030b0004441841c0c0c190610001030101e050007002910b888880c915001020140c01100d07800194180981259101e4001c01400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 248706151 1250 248704901 248704919
    0x1b040503010213032f100516060c0906110d05070c0f0806010f140a0e0c070b150a150f0309111908060601021b0607020409020a12110d080a1d040f0501 66
    0x180c0540441e407810f550f003006804994141450407017901c204010301038450380038018401e642640c5015210182c00c3c0c2d810f81000c8024186109041c00050303200714001c1010b60141e00240e54105a030b8005100c4606084001d1302c281c0c0c00300380300f60f40080c10820002000c0800f110000f0103001200301030181c079450403d29404100458002000302a4041c2c070b03004054450285600032101c0140391504151201a6008040d01c9201c1001d405041803904115428512203640300d0785420036039a481c00b0310b81d100710074041440c8840c0c088000407811111120031034425041541a140503d11081442c104c000001d81c251383c03003040300781d0804010303001005041d04c203000b4030b41d10200c00c0c00038000c5400c0c41d55030815030300e102008151040ca40420483d06648460b0300c240d01e2707258040c100700a902d031199046407510a6454041382c04034209140b0b40158203292444510680e1301c601d502d410104010002e44080040c9451000c442240840000c0669107500030343d20013000383e400010300c41d41004058 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 248707401 1250 248706151 248706173
    0x70c0f0e1006020303041209080a0b040b0906040201091503110d0e07060302030105010e0402030c04030f0b040605101404050a0e011a09011d010b0a02010e0312090d080903031b04050301021303 84
    0x401c0c850000660401c259500801202e92085e44901100c10400e49024140c1d6100c038160841c54803442400001c0080103000340130030740214081c80504039195100c0c0c0019659141c2103070021300060200108001d0701c81600f4203c8034600b59402d011650f8030440310469030030303000b080d4401d0181e41c8600060042550601024018220a2600f903103158181400070300010f5240480f94007555000000500d84080d08055038003a41c1e005480a20409080c00c1c581800f200548055698034601700229a1050491090004441810200124100119007044010103004194185d07a640701c280072441d80501303120b8a003980125400c1440404841c5e403d00c5408001604000340f0003d2840301e00750031a10794440c490440390102d000c00da40b54035094040340034040c2e9001c0c40c007092201165045c0740b45e514140883c030404080782101d494051400d000c5400c40d1042d40c4194140e0000c0020440c2c15001c099011004400c0000c06860141e5581c0400c1c00ca030b000d2020b103c4240344150b801e00811000140b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 248708651 1250 248707401 248707411
    0x607030606110714010c050f010603050d120c0903031d19090f020c0703170403060207080702100509090a0e120403050304080f060403120902011413030204050106030c02070e0408070c0f0e 82
    0x600c880e0741844014269905000a1340d030500007501d0b840e20070060200000944d0110810091103440d580e0301d841580d910590f140e583c003050044098610f412903510403c01180b14541d02c030329881d45103031000d43e10300c0b2418030481051031800011f5407442d1100390f005100111403203622a40f0b10f1801d045803044452035100d0112841c0108011243e0110020f0324109403508031220f8008064010b2121101e4840e5910040101d4000305549090006240c041c060241c000d50b41c024490800c901c0442d203612440941c10b6000300d2a0300400d000080950061084104174022205500451001c03034640c0c0c0c009900c100e134640d00024050001450034044141514100c000030b104030b040c941c1d405002800240c4004000507a180c404800396807081c4405400f03900d100361100e5980c540200780c1c40141a007070000740d000b5800c0400000303680f8400e110321040c200003035000e490041d0030320300c080384000c0c0c000d0700c1950307664424070601d00401c05051103031005001c21115a001d0500d03084000a4010740244 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 248709901 1250 248708651 248708653
    0x100312050c0a0b100312020607090906050d030e040209060c0c130605090a111603030b120316020d0c080d08090d020705130e100f0902031b220e060703060611 69
    0x102003030459200041c200d01140d481001d00d2400d0340c4404010602551326800a0200e03d0b2103e88203140320740110702c603802441183d0b1042c5c56141c9600d5040190b540503c01c058025101031700c04c2e40400d10800044143c8030300248094942000e94000070015042034501f4007154005034044011484c00189a01c00074200110078800d1b180303000002158620024061100320351520b00138244030020008807002411403551a51040050b4100100100034041040e4011030326070307003008040d480000a940760740b5000024655108660360a0005001c59440211800207a060300494040400c1c40102000360300e681d00d40107a80340907200710f0300c2c10403410b2968042d508503c10500880c1c0310f907020340180f0a42d0040c0850a0080000003910f400078030052003600d103140c154104440c4ac0300350842450300c1d0080f030455503140c3c83c5015410038032248420b00d40e13200c0c8141e41d9449030300220000c0c04180098440d8001512100b9601540c00c000d42201c0d0000040d0b0b440c0d80c00d001076508002c104d105101254 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 248711151 1250 248709901 248709907
    0x1b05180f01140304030e0411040602011d2d03040b090a0909170325030203090c041b0c0305072a0b0a120e0f030c07060e030f03180409080310031205 65
    0x400041c02d845900d010308140903000100240c14540141d00002c014140034008014000050038940d0258005e03018903030040d42020b080c100040c031000d2031080001802c1026290602000500000381103000e007080040c000841c04102c0b81803018005400200300984145980b004040704100c000502600880101131600b00b215020805070710f00c1742c10990101d001107550341c0380c40c2d0000c032141c841c40c640c010788801100400a052941a000345001d07050380d408a4190009480420054a12000c181c41d580c00725181750b022440d10901040328124042d0808070314140190710307100120300010700000c0011703400c81104500c1d98442041e2200801441c0c5643c1d0400401040007130054990a0b00c14101c00d40b0f604800e0345404051040c1e101000d5a0021690381f054680c100580781d00c3c8900c80c01010a900d00180759007400c0c04155000c1d5070341504091440d10260702640341d0941c50018290f40c0040c1c0d500803c0000885150040d806400142c0712210854594544803842080a801c2801002014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 248712401 1250 248711151 248711179
    0x33e0d0e06150312180618030a0f020f0414041b0b041202010905010305040b0a0507020c0d03080108010506120d050c0109060911040b0619110a06020301170609010908030a020a02011b0518 82
    0x4ca0980c1c0840305c0c049403500e5440d1143c0d0546162200c41c0c1000991600890030303200104040f100c95105c0c800d2094608000ea08407850400c0111074074650400d44c20f2640720005000100c400140c7c1c40c1a0400c01c00150b46c6d02d0700c540e081e4030703282c0090b044081042d8480c00403406642c0c200da05480101004d203802e00c142c0c685a52000c12801c0058003540d04035444401064003540203020000300b5000c003404440421201d814000d0080ca001c0c825060b0300d52800011840d03a09001070000101c00b881c40041036030099000e0219540d5010715240405075683c0d0041500152481c0611101303503001e03881858886041000704012540740303c200602c0744c4000c2248402c1001c1000340403074030b4111410111100340ba406009424040703850742c000d182c5840040003060500004000481c00c201050440b81a540d8a503071aa00b00c1d204840c3c00713016228180000750b110780e110b4005081044403403001281403d00035613040340f1a200880503501180340490105041e11403800d09283c0300b4811102058a180b030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 248713651 1250 248712401 248712427
    0xc0409050a06051005090111061e0a060602060609090109020907090602010e01091110020102040504020c01200c0a0b0702240105040b041b0e0a03050a03033e0d0e06150312 75
    0x580c40c413200303200000c20200126030188404807982003441013680c0092900c0d0506a00702d5040a181031503060b40c250106002101b035126038015210a50002d1505d91143c00800801c0c1d90003c200786c05664850a201005854248043d4041c04941d218140042d00b040c0010f820755049400c400ea00382e00d03214184003c600c45820000d105201900d00d4580074407840800c0b80a84919002544c00500005640364900070552002807032050b1310324002c01000303907980421507511030825001450b50180726407c01007400c125489821010b240100d0f040e0461400c0d000d408204105592145040f034000100181d003440d0090b44001d000459040180c003229120718410030485401f10740401440d81c41c510351a84485280c0406075810204481a69505140003405401c0c00080030104078103131002d0300100e5120450807041c401c0840d0304560305681344245004030f030300484280402c0d9034990101002d000c4090040c00e001d01a180c0910b800f03154000241440c04003041a5a00258010450801c0e03c0b20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 248714901 1250 248713651 248713669
    0x403320a03080708090a023304050906060a0509040b2e09140604140a030c0e060a0b0304021e13060305011d1501060c030c060c1d121f02120c0409050a0605 68
    0x81d040300c840c2642101c042358000d10680303413072500880d5600e41641020003540480a44108c0382c2c2290648066521407080c02260b0107150020350120b8010301c1544054581900945014400600310b1440403400c0c00d41c1c800201c00d4100320f0210b514000444010721544840e500020b030a10001112114005c100403442c1d510842c03140f0000741501c200b80210301d55840c005030780210703040100200d8640d00c0c2c50040350740d650181c8941c0d1054281d220b00042c0200b441c0c059a2280360014001a1140200d40c10b041c07604560064a030351140440d40c4a1014804a00c140b0010354001e80000405a11030120740c43c080c10080541240c41c1d100d4102981c1c00a008002d041c1035807800c0c5000601201c2d0383c40e0540340e43c0441d000081246007400302545499600c400b08030030046a10303409800100440c024802400d40490201440350804d01c030420306124540721745640c955041c1001850f040c0c0990480c00c01d5001034824800c1c0c5000002c1c1000a0a018040c4c10b40044204004002c42071800d400605515 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 248716151 1250 248714901 248714903
    0x60108070f05091504080f011503020a03020d0f14031209030310150905030703061e0c050d0b01050d050c0901080a06050a060e060d1b02010608030f0403320a03080708090a 75
    0x814001480846502c5000d50f4a00d0b1140130031095455a8a441c803058a43d0344a03800352050b5803800e003400100010401206080306d030060300400700c1505680034014074003840001542c109005d8410b11002031150407020010b074100300059512282201c803041d882d52401707041500158024424400c07081c0708441a00c084940140284419449900d01070710199015400316505004894000061080580009801801113035038509a0b0895041c00b0301100c5100c15a0300000745c0500610b103903c6030703039400014440381c14108542001c040d400c00074142c0b04200c0d0403050100b0041140000c40d40c00500c115042501e000e4203201ca51304050200309040302d40c2c400c0c1d1041000248404c052502ca080c101c0c2c01501100c4400d021224440c1d040c808c02250f039408070001507103090400100c0800c08400d9501403820562294074191030764a490802503061000c0c035130740401c000c46d030346101648001d02900ba10500e8000d800c0c903540c5401d0150a24000400d1403040c00915010400c1143d00480c581640d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 248717401 1250 248716151 248716157
    0x7050d0b150114030a0906050702030a020604080c01020d1e1503080706050a02070b1008060a0204031703180303090106230303190e0d0320011407210207060b0405060108070f 76
    0x4440d207030004071040e000b2522010040000042400300b205401d0b00b0030b0119901544003840a0307100d04000300d0384c0c1d1041d045c0d40001030704144081000202840700521815581c400090700304014001e0705070440305410502c02d8003027495840710548845030b008002d500e02500c1185c41003103156898031a00d5201c0e58000400c090f680d10009100c1c00c07041d0303045e0f03940d964001c2c4031038090f40743c9800741d00d114680c1070085201c01e220f604c0005400003910700031942500da00c400b006c0e0f24144443c100d85004d410190007058031240c92183c20348141c900f0030265119500305400800c07141d01d03100904400c55000b1030010580c5482c2d10002410740c030000200c032070030301181d540980140754003081210003e140c905034542c00010340c48990141a4803010702081c2c030705d030280484001d1030b16802941c201ca0002d007406900800e100700103134507103008040c595a00d21882e40d81c2015003034650b0204040785e104610490700030f9079a4540c0c14207814240f10702d42d0300c11820309024100381003030f510141006841c11401410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 248718651 1250 248717401 248717431
    0x130503010204230103060e0a09201c0c050414150a03170706060305010e0f0f06040b01211e030f08040803131a01060c1a0c030105042406020d0207050d0b 67
    0x1890b4880e0784080c0040400c450002120308000b01b13584089c100c03002e42520340d44400041c0c0c82d0038000b01e0399100148e030002026a400c242404c19210007014503100240e03021030494000007040d13195070003200c484820b00e251030f203854a400182d010041c0c40302e00840c0e00540c403030181440028001c01d1981c851103c1c120340c0c0d07601c408503460a1b50180010740c00040195080410805804000190403180b80001c8407e42d40035404c1c404089580d40c50072900a0005400c880041000603072100441001141ca050f40c2e035445026602c50f001424000ca24082c0b04a8203080c461041c146c0c0b1801c8801080528a4066a24100754540b01940c0c0030240000052019140944041000c150800c070049805104e581c101503031b4500c000780c03407400d0f4500c0c20748144000741401074002680511007442802000e81803410340c2d00b80b00c140030060407000e4560300c21066460b80005040380001d60301c4021b28042d4020a2403513040500241041030b5588500e008000036010500051440381904d9070124803080000c0c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 248719901 1250 248718651 248718719
    0x1302011d03031306030b03070605090a030b041407060e0a0e0709061b02031009060605060a0807050a03180c080f0d02060c070804120308090d0e0907080916080102130503010204 77
    0x1c154070400200e414001c0b03a1440c0050905d0305500201c1894070218141c404503540c60700181c070544903411415900025103d405c0c0700051455210035081401080c02001c1a019095554605801c64100700d0104000480d080420701d81600c406000c0c1000e00c01000980c01c010310094101047e500031002441005c08900003000015140b883e01c090300101140d01c02c0ca0940300301e0000b4001c8440c01d407909070030100048cc550a0140c21101c5185460361002c0365039403240b0f81112540c10000300c090070182c071400c1d04080b5090203000c0580c03860190040152007490080798a2030300800e0b4501e40503a0708140ea241c68541d0700072540a0303101e00010b684a95601e030601c0e1004071482240c11000540903011180418560303c41c0026204824075000c4401000c06a01c05603070400c40e914480344e1007030100000075a0320348650003950300004984100c548450203c020850981641e80180e1110380d4041b0b119059000880d40d0b000051006074021840e041c203000f0281040c052800d2105000d038a61042a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 248721151 1250 248719901 248719903
    0x507110d0510090c18110d0209010903060608100b030606031207020d050601170c010903020a092a0e0406090b060a0c1401090305040608062b030201090503160b1302011d03 75
    0x440941d0001d0108800543c070301c0d00c086003104a01420200807000786140041540c0c81c030404d4800e04000103820704002d0745490f22006076020b98000c81c10012042d200000150660082c0805001800050b00781e111485040350101c0341900000e510a0f0700241c24441280c60100d12403070342e10390085100741c1d05c19880c004107880004000f401803842c031401000040310401049050700000d40401a2420f0200450044404549600000c2d42c491429001001520780a5120388502d0b04e075031000080341c40042d40305518980d0300c041002d011820144240d0341900e03080c40b990001d41603d21007008840711500108555004401c065070070720143c070403020144000c11010920380c0745884c0080c0144101480c0c014103a40203480360001003541400801c441e8034000804090542c150100c5880d044801c84500d003844120340ea080d800d5568480009020860038801050850b070010001000d02245150241e44000700610442d40c40b1450076a84005170380c01355001c0810240140c4003052030001d44002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 248722401 1250 248721151 248721163
    0x9030109120306030516031a06031f0209010908010501080601030212031204050703120e09040210050c0601030b1012050303040b040c05030f0d02011d03090904082b0c0507110d05 78
    0x1c0c001000da040044000303685a000301041e40d11620990344610041840d03000c10b0f003a1400020442a041004a1094803910803100c0d403041006044410f0f0701c001480c03260180002c000c070b500c00e00340c00140440c09960024029030062040400030041c2e585001c0701207884038010700000344242d0316200019009041081501e0074100c06441d0b030f40341420b0501c2c8c01562000c05100c01c07200786849030b03040500c007409503903580285400540030049a40c1c4517403c020707108100054503010f1003030600c0250b4018800f0816140070350320501282c4594144812510f0004905a0242d0f0041200c0346d18a40000c80200c1501c0c1c0017980075400740416100d134600030481d2403841e0030841d058420b103400720540390030001d00c4800094190300200211065585244e0250307140002c02802c1740c3c42041614014100250010351260041031506c0c2071400c40c13140043d0711805501004083e12400e41d0100c60590315104049660b11b80d420700503c1e110185d07590040a050040206204020802c00001400300030f02007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 248723651 1250 248722401 248722403
    0x50c1b01090e070801050102100203070c110613091d030304081b0c040e031308061b031b0c0f070b160803100305010f1d03130e1503010c0c021e0f01030209030109 71
    0x1902d80b807030041001070103002c003403042034014812000c580c000d01080e4821030340110f00b01da031080300042642c4c84101d021030462418642040080001289425001a403a07003c2c11503518085000303d100b40040700c10000c07101c0078440f540c10400a00c400101a0811112007100405140d81c0c5030140604280c00d01d220322070036a4000f4105aa8003040e01408070040c0031860100c040541e03240d44402c03816564080444003041c820b4096000d611181c3c0640d0003450703000902003440098002c04c0401c4d0501c641010b140081940d0154480c46070a25003841098081c105090b00e4030f003020402c012150008804141c05031004000001066144031003840c0200074540210003442138402a030001c00080c811503403850400040364143c0c02c0540004411a0441903414000d0703030f000f42c20031120b4008218050f1420541d01c1d96050400200e450138002d1950820301a25540301d80212401440003844cc4807150345404001c41d18918802e59403059003500d41c00b02841c0044c0c031001100c0209005180c1100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 248724901 1250 248723651 248723669
    0x1d0703110409061701060b09060d0609150602070b0c03090d02040e0610180506100e030718020301090c0810090b01091208030601030b010503040803040f0305090607050f010c050c1b0109 81
    0x140128501c1401d402000450340c908001c0e01040380c0602c2890b00320b802a002c7d00d80c0841c81000000c60600d0148060b001a2101084c0003a805039904881011524110210324075021a29410009107130103004074002407401035000c61030808520042d684900c80c0603403c501c5446410080003c0d503d91707501043c0d042c00702c002101c01c5801c00e015040c0c11192544170324440d10261140300503c0080a0103802d00070500035040901510500009440d085003080180e03802d0720480000280f4008150001823800d18407031b00050307980d418501c0d0a4140c501800a503c148000b40c01804880324400300c4000803164240400105449580c1c0101e80208084e030002080c0c00100901c9010b00c0382040085000350303000d0720301b0820b00c10031400540d811302040381d02511103401440001c0100703242481a00020b8824500540f516508500042e00d94015000075111680030781c3d511100c00801b441640243d18244c00c100782000e50b59950316a89401d01d609178000a99400322107803142c2d003310f406101800300f03d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 248726151 1250 248724901 248724907
    0x2060c0f040905250203090306040f060207150903120c02100518030c1c17010b0307020a020909060901050f0105032a041d060a050408090607050c0603070c110303041d070311 76
    0xa030504c203810003120681d61007160981c101141e18000400c440f05688082c0280806a545440301c4022200a00d0240c500030340801c04c260000c1c0d40b0080740d454010200000059041d005e042c0103042520041140071014585024030744840d80002e41151021800c0b90045100c1c2e80321400340ba03003203401c565410ba00e4803001c10041d4040202007460b00404140700c408000c0c0c410003540c00c40301c410f00c000071000c9880c60301e001407000315000001182d101841d0300403124440580e50200c0c0b000c200887e40950035402850a0000c1b0080070302031960090403c0c990f1850a504200c000303500d86003000b03003511102c18859000749180801403040907001030010f000700722a1002c0b03502801e001048914602c143d0144500040394440030b4400c0300d01a68000007040d0805188405200380c603481010b06480b00c0c07055021700e2407603603503c0e802148154095030b10100226001e00e4116506001c803044588244c105000602544150710010360111405038030030007841e11401c0b001e6008104141c0b120071040e03000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 248727401 1250 248726151 248726161
    0x13030602220b0903150124050427050f0702030d090f020a030c08060906010807030609031701030827031902121507080a090f0204020d0e07090606021204030302060c0f040905 76
    0x82c074080d040d0014143c0c1601c413841003400134104051000d014a10341020103020341c05495210241e180d81c2007075139041c00341c500b0b500d541300041f42c0740804202030040602d41e18031112103440d50081607000b01400300040014104020003079202e020340f64000825640d10310f424020700103d820032201064010300030802c0103840b41020410f030946801142801d2145038042980318a0020301c65040390414809840030508503aa000c02500f40d21900350104005205400c8503041042c0a144c020751050442603601c0c00503000340c04060307440b0b0380c5028000c20002d80d203401c80c0c0c03004940310a0768909195a090f140708075100240c80c0c1e4081449036261407246070070180c03034860010b60440c01152582c907003000c00d94070b40c241d12003601d0301828001c040c464620440030060500740c021f0904810001d40101d25000940741d101e00d04813a0b076011911550310b4060400451350184000845910200e07141031400382103440c06551080054003602e4011304c000b8292424000600c1504c01500181005220314144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 248728651 1250 248727401 248727419
    0x51305070f1211030c03040519051f110318010b04020405150705190b01030b0c0403050a03080c0d1e060504050c04030809041b0206250e01030f060e042301021303060222 74
    0x207e50071122403241c2c3c008040002114203820a000b235000d00103002820007110090385101c64103061401e2a500d4940900d0910a240d01030340c841c80070901440442110440418250f80d4000303082801507104200c1444152144103d40502070049280b10350765500d10b160031860070540c01418454071407041c02c50020400d680c1d104034105d030b0080c0c100d4440c0d51035420f4150300500ca01d120080950b4000064880024000c007041680702e0400d480c810306001011030014191066030344650100011519194141c1103d88254405418182d80400c0a468200341c0c81d116031003180409000d2020120310021180c0d6690041d4a00d0700e1140340ca40703071400004002a40d51641911011700584a04562808000031b0303a034034940701e252607510840031100440c0190010054800d00302020350300c0303800101e00749607030303a000038000c0d441a400351401c0c083d6030380d508401031107240400b111640100080b4407400c0030118401e0550f0b40101c0c0050b42d414210225180c0c00502c80e50201c54544800340014940d90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 248729901 1250 248728651 248728657
    0x20f0411030a0b01091508071106010605070b0f0c07172b0b03010e030d0e0a0f0302030a1112040308030a020c07030303020418050603070e071413051305070f1211030c 73
    0xb101c0300c280b150b140410019111800325000d0310701c00c1040d140400d50071520072a0b016800c82c490703080c88075030600c1200d0a5030a20001360000c00204400003143d40403c00c40e901055400811010b50780d00a040560840e0044d2043c41c2d000750600b000c00905140030b2042d041200c46100200b045c20701c01e207000320201c0c81303120100e040d00340c5007038500583c150050074103008070401c181e2024041d41c40c200c1d02030741c0d6900501d04444402020300c03c00840d1800110b020204148190190300116200c0f40707102c1e03000700004000c682d00316890304500e6490b034421000ea000d95017581d03407008445032640d0719281800000d0043d08441242440352400010505400da8010030035a12910f016801040643d04980141c41060750096015800540104000d125418005400000340e00d08011074003040d00126840340c01c4180340c9100048080f904004514000a800078030b210312501c20700203403500403000340c00a14110305000602a0391816002d248080350320103681c0c200c2d0014200d489041c407041c5044207030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 248731151 1250 248729901 248729911
    0x1005010f0201050f06100306031b0e0705040e0a02030705090612072712140616021c05120406020903070825180207150c0203120f01060c0f020f041103 66
    0x6098040d003804400d10601031584901e01e00303d4210815202d174824030403682821034003001010350360340000c40040e01451088070402302e4440f05002c12424110040700540000c0c1c501d5003482810041000342c00d000c07902440c1d00c81910350700103880b643d50302e0090b613861051611150f840303800041e44440c51404000d01600030540b41c0e0f16210682441148c03200c0c05660711b0960118010041030400006144544007030080e8446c4029100040d1000d4195140041c29070710396038000d0742050016a40c0364104003102248a94001001a0044880b8007a0140c40f822403005802c3c5c0c0a04000340030f200040e01210b0078401d000c3e044410040d43c0d5046242c85800d400c03020030300c01c40000107050886207603002c02015075500c0e079682492070140390440c0c0300a52001800325000c0200b200103800c82c0446220740140c0b009250041d5588030855107001f190170380c1c02441700b402c180000c00140002548426805c0d0070036800070001180314001c0c00050b0000751800301c41607220b400c040110040744015400785d8010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 248732401 1250 248731151 248731157
    0x1103040318090506030c120709021b100510052e09050a080d080c1e0f030a0b0103050103030e010f110303160906030603030f0e1206011e050301090f29100501 69
    0x79191001c0710b0030b954040d40c041d40e0562100032003a03140d150003040c1c07508100f52202123410b4195191550400e9801840c40000e60034040d10145a0b01c0c2e506104240e00343c0480c48003001185042e5800580307030b02090003098011900702d110b00345411a0401c42200121580521101900707041c50018200c0310340b801194010040002d000920000c00968400f40c158103483d4429282c2e2251240d910359040403c0005184500b0009400481a481c005118007100d9801c0e0b255240740c00c00f210029200d0307a055143c1003607d842c004001103a44240060007480b002d18100d1804000300780201ca15910754400c0c0c00785800000b061001040c031341c88815a00e054240c079202c02c3e841d9548015000c139007a903c00600462404c80c1402c0c1040e11560011840000051004401d0207140b01d029203041d038240c20a000743c0000c0203004050402d0985200000c0c0002c90091290030b105030f4610000f0103d50000800150a00b0084070100c40c2e024680c075201a42048001002d18051104040c00303801c0348a95408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 248733651 1250 248732401 248732447
    0x70e1503070c23010b150d1e020a0c02010305180a141005180f030309070605030a021204030c0204050c070c150318032c06220b0409021e0702210111030403 68
    0x840e0800b440001404c06204406600386100c1e0040302c7c000c0c01d881c8a00603035003c5480000c0c01144503a2000c1c01e85692036948000600c00c4504c00941190000740502d490502d1024100c69143c0000031100001584000300131118031800390500c0ca4a541c00b4440d045c01c0b030800c1c1c2000581859002c04c0a202040c40c0100c440301a05ca8003001d441e0720081c0d480c86040d420549080c0001c40c0034000450304001d500c14018034040030134040e13000500c800d40f81100001c00258400007035140c2409103e4011030300c011094034043c065a650b80143d0142e200b44070104915030408402e82d8000d40c050015800200c030801461195840d0007064414000300310045083c1c0030358200c014003070481040c3c012603405012289040803000b200740c030360080501c1c8845020b00d074900c00304880185102070001003140c8000503884002402880400c42444c0701d030310224081c248800c0c0d0141c0d850003041c40a00303d540a000c0c24803075080c02c2440c05070004c103001070040390001052004059110001ea001c100390f090000d20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 248734901 1250 248733651 248733671
    0x4080d3c1a0306070f02030d1b030f02040b16151b0f0801150e0d0c080d2309090a0204080d05070209060d02030c22091109070e1503070c2301 62
    0x440007003403025400d503001400150146000c0c09441c00249558011a03007001c0c00ba0110b0020354040f1800c01c0c04d40300030035503452130b100d406006034103c90009213419401d20742081c20f106c14602071700541004040c1005042ca0906c40d0051001d04080340300e00080c0203186102c0007507403618440f00500000100002c030801e070a1840340e00300780d05036640584007840003409030034100c9000a0101400d03900c041c5120103071000500c128642c01c014903030302002d4214250440c4000d081c00c01005550443c1140c42e8614002650110088a2144604994108403a1900c540786002402250848034151223031b0404420305a801c40f025008407807088601b42650b075102f8041c0700d50088101d00094265108a8090515180c0103d24031004040410741e190925003181c0343c1c40548106e0b020503904000300042442c4036013080120a50300500a0801c03486076040c0d440450a02790074114099440600400803400d0300788680e10f9541c42e150442410300c100980070681203d0144404c02008107036203840a040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 248736151 1250 248734901 248734931
    0xb041208010b120a020d09030206161706120a080418060503010c1d010c1709011103131a0d0c0e030601080d050316031805150a020304080d3c 62
    0x1030680c0c2c40800c10505011018000102c812000303031080646079000e20000000116522440c0c146601942c010062401c1c0700341c0c4c050a10010700911420001032800c410b10041d220041942c000c10281c03200103041d91501c00381410540c3c02c813401040c0b01d000213000070399020788061040001c4d080500030403045d5a02c0e4101800c0390118205800424800b065400c10304c4242c0e500c0d00c8800d0f0040c1440c1050018a43e43d0400308510301024440c1d4480110320b03401c1559009050030024100c403802545000912040100d4012243c840c0d50110900b924004100301e03440c40a850b01802510010710040091100c0901045201040140203125160001940000000d03807103110305000c3e140e280ca90745440030401c2036070351602c16035028162507a03551409520074448205105000c0c02c0985922149000310303102c80c2401401814100c0d0061007032101280e044011180f965600d503a00046003040e46591a142d40708071003100000c0b600e4a13100030041c1940700b11552040145000803c858542600c81c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 248737401 1250 248736151 248736167
    0xd021501120203060403080402150d0e0f1612020103021e09030d051801030203130507180c08010b03190f050c12100f0b0a050409090c0302031b1005090d08070b0412 72
    0x40c3d40b5a00910110700800d000e03018641d0014000f0300100d9900b18058280700503a0701511300780c0f03155036076070040540e03401091002d80e0624406c0d0015040c22401d007615100c4c1801c0c54002d560581d1201522030045a010743c2c1160503040c81e152030580305a9134031aa4a142d504181041c900030301990401c0d42e100d5200704200d0b00300c0000000110b20418000004400075000113184038100059000e00a010071010090800140040001e030401c10001043c0403042e6580b401140c01404003010040c019034040380700342c030342c4422421081d24988400b03200d0740c0c01401d0803c503c1c0200500c1c200c244801b0410f64002004c1e00c02d03019902c4445074681000c24001c00a40e0322030000c85e41850b00f82401482d240100400e0401c1061800c14200b03a214541c0c00111401c84808450001980c0c0c4c0400031400c05002d00c8901c4510700061480301021400414403000003580701804200000a840d00c25030f0321480304240355034211084985886083c607125415410540d02590451034020030030040a11444103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 248738651 1250 248737401 248737403
    0x1150201060b0a0c02060903010516120c1e1209050609120f0412050a050d120b04020c060f1b040f2603040506160b040b010608090309030304170f0d02150112 69
    0x210600d0954108422900100351307030380490f4020400c000c0c5001503a003d00620b401a0f85c4074144041c1c1100031807019145c0d00b5681e0304c981c1403d06040048084c1d9811103880241c60000c0b404401b40080c5882080710301022807131110507600e240c81172582c2030203000550a8070a40700c0700111000300c507480a821005001c3d043c8542890031041000f401207512a200102d0090b00c10b0f000ca480110031071781c590f03082c48122070821002420880030301818101c24080e4040d043d005440851420262421858848400034014064981844007142007030707601100242e4825503905ea465107031a02c41c2801040c1440307521604800b05804190b030710080d07070103414000318805521b00451030149024180526500701650312030582e860840c62601103001c401005100e20b1140d42c0d503140d90360404a01a2001002805925465000303103c8a16a501c000040341c1c140c071958590300c229620b800d9400307481c108900a40300c8007402901c0f40385002640004800c061f05045440ca03500301c0c1c3e01ca1411034400d002d1590 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 248739901 1250 248738651 248738669
    0xe01050f04050c010219020f060f04091505040c020a0201111c031509060e0414100608030702120601050105041e080a030903120e150315030d020c04180203030912030702180115020106 80
    0xb50702e100520346480340c8d2102200c00380c80681001080490004650400e4bc41f100100c0d1300c1d8404002c00c003003c080c0d0000680011a800c0103400d1030810000d40c1c03400d0b1050000e050010310001018038803801c2014410f00c540f920010300c00b0b941c0c3e0b800010081c1c80b40e1307242d00301c4000c4071410120b4100000c0c003d9506550201c8219142c650312510b80c0d00c2d01203c5000c0c419104c7c004d440ba4140c00304614028400681065402142d0300c007024030510624408014140030950800001440300d0307a0b01ca4101c0c0c0480e6403420b8036188403501513010502ca0300380c550101c01144a440100800c242d00580402c0c101c9001e454604c00c0b580c000841903800c101341c0c5114581c00182180c41c10000b000c0240655003001d00c0c010003050040310807001c2854514009095405a440380f0001c402c546403a006010701610304405074200ca2013a5400300e6034901030251560f1044c844242a42c00c0c640c4200142c418841d002050340d400a2a045549400c0c0c01c028000d0304030b8003e01c0c1c14501800350050180a007103c400c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 248741007 1106 248739901 248739943
    0xe01030b0f10050a0b0a05120a0e1b010e0607030e0d1b1205031b1504060204150e030a1b09020705070f0f0305030a0e040e01050f04050c0102 62
    0x203100c0c12003030340c07004070a20903a2210064107003210b080c05c0000f81c03911b004107030541e4140074012000480140d0300c010052620b0b075507044030f90490094003d80d030f40425413041d012207154402000c540843e61070281c46009090000007401d40d17074081c2c80c0407a0b10205400000704548424481a20b000503c40c10f003d90202190107014000e15040d2030050004580b5564992030f8080d14000c1c3c080c0220070842c4141140090240160042440580840d0703032a052400030001e4000b401128400c030342206184400c4c9000c0c00d2209044640207008054103400c1c0c0c0da980690115240310a01e01a00039a00010384100c107001401c10244540d001c0c2107000d0614103241801440c0350300c1001c0080040d0010004503d010007180c012485c2440c002c2840d240703c0780480c01501c007100303020420750b2800c41008030b11000c841209000d0b51080d001d55402245407001243c2e0b441d035610b03d640b6004118 = true := by decide +kernel

theorem cover : BRFrame.Cov 248561151 248741007 := by
  have h0 := BRFrame.cov_init 248561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 248561151 ≤ n) (h2 : n < 248741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
