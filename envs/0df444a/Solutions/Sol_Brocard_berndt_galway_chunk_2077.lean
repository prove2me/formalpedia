-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2077
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:11.654307+00:00
-- url     : https://prove2.me/submissions/e540742f-da04-4f71-a809-166a4c7f98aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 373381294 ≤ n < 373561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 373382544 1250 373381294 373381297
    0x18060a0b0d050916050306191503050604030801080f030f1305030f0a03090b190516051c120506030606061b070b0d0506010c080307033201060906031a0d03051e 70
    0xa1070028200ca10381ca079101040402224117024164050b800000040c1c030550f8021840041200b034020001154402104580e800a1050f001076485a018400380403c055018002500604124014162414000581035120b01c03450a00c0c070150200070850001c0707803100f1580d0100419000342240c0003856201c03030b00b913218881002e0503404142007080c0000d00e04c104004a03801c4d40380d05000d0001640042500340e845400c8100084040c07003000d4010400101e0800458030381c060800b20000981005050080c80c2642102c026030b240744c1401c003403254580303000440f0345e009a8220341d800e0315040c2d8101c0c840c502d0243e84103407012504c100c500c00110b10020b0720082c0810328054034180300300c4d9100801550782d4a1758000c000c02c640c10410005841030700c01d45c404100c1243c00e030f124500103944a21405004500e058001c8110303c034041c010412150030105000003402542018001c0c0ac80c260074075484401c000c000c907406000f400300c3c1601050f00c1142202c112030b10f15102102c002c0491518070461b0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 373383794 1250 373382544 373382551
    0x20a02062203080402011b05010c120b0613030b0408130609060e060310030602090a050607200307030c06050f0f030907060905031b0d020a0e040f110f18060a0b0d05 72
    0x1034050503444414076000c00020110308030303019100e0b8501c58481c0d80c0112151075030484d0200802021003000d000003502801410041c04c680d80e6500006010298108100c8805412503407180b0300030003a5583c46030212100d0000c0340c2d04192036407050350782e9003080c50346840350754089512030040840c0800d805400c145030209480090f61080c0e0310102080600525100a4038100551004a0401c00004441d500185101e9030f004cae0106050310b0303a400c0031a140e50030070300b011039210805a21201101c1240100b0a10000c0b045000b00b503594035640f905420320f4014040c00e01002000210481407030100401c48000d490b104100c1ca5680c5410044283c40e14010b02902c00040d0902000241624000404032040e00f041a1101c1c0c0c0003c071a0308010606e00030b1842203030404092503000805c2d400c4030400f944100c2c041e0750111420300003440c0c200700800e0400368061103602c400e0f2100c840c0c0e80f1442451540713008a0750948490351500c100180c0b070b8164503802400a0b03c0009580d0004000c0c0ba00001e01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 373385044 1250 373383794 373383811
    0x20402092d040603110d02010203040b13050f06040b250f031701080111040b0d090b010303120b240a020114070507030905030d140d14040b04050f0c09071d04020a0206 73
    0x40140720102040b0640e4201e100c040c010307024502d5401018944503110b074070004c2c0f050044914003961004081c04e0b540100f031384014080440d1008000c142403060f5031041c40c0c03004403030551405040c038480d001140200400d01048880c40500f11416100d5458001e040640102103000c8117500b61400a00c20240c18086c0c40208104a00000b1500b83c14020781c91260301d0b190030142000d003404517001c041c0e00305c083d0f61117107113440d10351000c00300c3c404029490107180a50348404c440403080000106540d090b503603040c00b40410b003c0076524031040c0805c840850285d0706e60940c1d0b550044800324007502e1083c1603001c0b08441001400841c1d40c0010060200d144651500f40d1001d94490030162034508511802c40898484400c5000c02c42d012070041551652201001684000d09402c502c800907045504451160054003070005120082101c500401a000001c107085082d00000c924402000381c0624207012200a5851011010403100010400c01900864513848100b000035603408054030403c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 373386294 1250 373385044 373385119
    0x120a0c0218042306060609061c02032a0306010c020d060c0201051501080105060d0207081c09060b030c180903091203090f0d050a03140403080705060403030f0608061302040209 77
    0x1262040020608540002800003130442541c91805101c0581d2110100aa208008126844814484040030030940e400080016103038941070840c1810300c20107024040061200341e40e4070700358241c0e031000c9070f83c441d00070703c0c0c10046103031244007003000002000002007216040c030b0105c82c0f580340d0550000344141c45544800045252240040d213003a03000780034041c3c10900c00c1120401d50002070300103200051281d04c80e1440c100003000d41d031001003002c3e600d03500b00d5910f8540c07042c01d2201900078080e8410b0210060080519108001075403002001b1000e07551507004000903c810005006540071048050280321103002c0072030b006d0f6140e600800e070452080c003513a1540682c609000c0c1d9400f014960010003482059500d8400340e80e88102c00c102d00c10b1413442000080f0005620a010300312291003540280500c1c01d00c3d20b005020b41c0d04002c550380c0756501d0480308010303035040004c08641001c0300401040104045002150191103040d51180d04480c1084929091071540d01c40030450300030400106c2c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 373387544 1250 373386294 373386323
    0x6090c090c0a08062e0908060f16031e0204030b04050d0906141614030703140c0a03030b240c0c03010207030c020f01110717100e120a0c021804 63
    0x480c0103009850503403000855820015a017030600e0a41074032002c1000c80c00b0700e401c10b0048440010560683d8044000608a03041008180c0c000c00160350089100200e103d15440d14107410400009041009800c00da26101e05001c0f81110802940d40380e080440c0540d5136607124201013050718419101155544642c541e28103015114524000980e441583c88a414000c42040a007a40c0c1040700070301c203240440c565900c0044c108035624001c00b14a14059611516507040250500017880d852150340030781008070311019075000c508000c040b64141000038202403550701240c13043e035454641c2e580000b00441d040c00840e01ca480a850884508800c8410100c20181498240d004510303004002c1414941c2c00320042c90050300e41d0344040018948003200c03d00c0c22203224504045588248800079030303c1c00705030420f17000b030025007201030b03205c07009019610628071f80aa6440c1694060707100094041030500d03402d445500c0f44551a50010189004105171605400c914141694100c9010035610f401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 373388794 1250 373387544 373387561
    0x6010e0402010c1a0c25050307021314010e090d0206010501020304060f0908061005310902040f0507030e0c010809060103030e2823030a03050c0f030d0509070e190f0e06090c09 77
    0x1c5d031a103034007c003c0c2d803c250059080c003007c190262041404580c0310092b25008080b84e90703007240285680343c10414035041c425405810039003001c90b802c00319001100180566600002190221404d51422002014503d2400c441038851074001c0c0b10140542001d1080202c4918054015a5406c42c1c07981c58104401c035000c2e554000381007150341208504d645c1c03c49070a0081e44400070841c005030010074034841c107005d40c1088070710464a56012a64981440408070320400051100083c2030a010400d0f0500e2201c2e0742e51400c051000808204c80c1741c0300b03141542c55010303503031800100c100c0006031103507103000e9a400c4089150044000001034003506004128420717020f003005046c0900500f003051082d403002c507136a03800301c12282c1c0741c5d202e01a41c0740b44180007000185000d1040c410001120b04207a212282031007020380c0855162500441440b100036402c641004801600c4030000507100704001c502c0000c0c0808450210050080008001c3c5c2c03004040750154a040c41180d480004d503840050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 373390044 1250 373388794 373388857
    0xe06030706091505071416030b0a02041809110901030309150305060f0904020114040e04021203030606030a090c0506030702100f020418020319020a050a080906010e0402010c1a0c 78
    0x40f007480b4008094016641c0c0d00031401811202c3c0108040d10072880b110410900d00203000503603008400f813200c000c0042c486042011904003003042d0b015443c007481c0c0107031100c01c2c0b05000c1c01c42d035003540d46509140402c40c3c400c10a0040d040060700d4102c0c15a507a00f070180c418486442a1410080211048105103101e80b081c0341c811030004184060480c5100284444000020401c070b06000c1d400a01d41d000302c1e140e001500052102d40040740d580d00d414414810070f6002c1c0f01e41c1000d940c3c8148140b203141c0c3d0b5290103a0368003c4498000060402150612080041e465032000390408400800d10900a9002c03a00380740c0b16525020600c80710000c1c5501400300e100b6441002507903807484080170001d075482e030021500721014040344450411660045401c0343c2c00720040d40c0c08540000340150341a40c202c070f216540150600041c20081d803509180b8001440010002810440c0c01c00b0703007408001c600d50004900d50f81508403a081d038030f044c41c1a00c04660142d24100803645041d50400ca100c045060b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 373391294 1250 373390044 373390049
    0xa0506041b050a090803041401090b0306150703050d02030f01060e0f0a06030f0f15050307060503150f0d201503040c17031213020418050705090a0905070e0603070609 73
    0x244005514403840d03004030b80396002180f240d41082013121001583d000c0400141000d003410100180100700300d000050413441a40d03100c021103000034400c1141035a6061b4014403255802001d8075076401d62490216040e11690165010852000c0140300b8101d01e120201c41c140d4106c0e4403084140340b03814041060307001c2044c1d22980d00003584003007401210b00c80c2d0800740c4041012100828202c0fa48040d070401d9915850441c0b1110f580018200014501080314100505541c100b036440d6061a07180c9810240c000305010740550b191082540700c94546124a005107504218403501400841c02600911040d101c02c50b4440d0380e9418400c04110404421203001d80d90118640d4070f030500d0a0085c2607040c1f540d2002503014001849500c5021505400d0309129407804400701e40c00040d0b52040001321084100e02d00400a51036068000140000820005540c800c84030354070a652140c40c280003130100040c006106003d24280050348291100c0d606000d880c080b0140c80140b512502d00700c80e48001032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 373392544 1250 373391294 373391321
    0x60603060312090111060a0f0b0a080a060c0509060d050114010f1b170d0b03070f0506090915040905101b021510170604050c0108070c020f0f0a0e0a050604 68
    0x40e03003003402c500d000700061050980c1814200264140f44501c0c500748241111000541a160011980245420320400380c11900c101c441040c1c00d400c25140c65628855020003c118960300d0700081c01300c6002e0010b40e00c0e180d800a01c01982c0e00700000c0540044c0c0000e108800303c0005410340c4404942c024114548106004d17a00c50541ca0314410704100c2d20104000d0a403411a40002c10f01c0c07101903001c0051011345440a0003144102e1820207051800249034042c0200b80c0040a00340926980c0c88101c0752203203800c41744161076488190310600c45001e10801254001c3c50100300808014021a0043c0c181581080c1040204288406c4000c1c400300e810009005800145201540310f00400740315030400c0c007910f1101011030310746100032b6070a08506280c2c0851340c070540070401044000c0101016a400030300c1c02c2201da061420025180a00c00d9500070711404074501f0420b103035111641c0d5a40c0c85c1000411005d00d440c0d42c0d640c0049115002e9869541080c103180001d06a41427034054800e118400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 373393794 1250 373392544 373392553
    0x207090c050d05100806090a0b010e061f20070e010b031005011d0a0303030b030f0a080a0507060908161a010302010e040b040b041401151403010b1c02070f06050606030603 75
    0x64240b0800100001804050a19080030001c50301702c00030842d1621803441140141000445810f1038a60031405030310108150401500f0488540c03582200c0c0500018558100703a40324207000c0041d60540f031512a51000400d0400c65107081240008240c0115964059080f4003640ca556000e1103510044074181c401c2e0000c0c80b800c02c259449010082c2641a0b1890300000e106a0b05001403544501a07105400013070307c1e95a2503246142c280704807200d803101400242400c2d8495910746480e40030b107207540824440041503902c1444525004612065403080c20203645084006c410303d0100012384080e581003c0f000c00384805145480101030503250141c40d0116001059000c0201404071010440c0d001900ea041c4258a6110340c0030711389803040110b00c03002480d03040841403100301c00c2c02c442400070042130f036031903507a100d141008580c10740314454031455680e03595a10310b82c10700641c0c040401205200141c0c000034040035102802c0d1440c8500028000b64590404006c83d5000075610b6a41c581c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 373395044 1250 373393794 373393807
    0x501090e1216020307030b0406050a0b060a200f0109060204060305070c0b060418051506040f1401030807020d050f0106080106061110051807060525080714010f0612030207090c05 78
    0x42e1454200c900e070310060840f03840c182c403640e610401c0300d0152230413600203480e0403e0110207001402005224041516100e04209222174010b02d28501a40078600c4030341b4401e051101d005d000e02c0300d10f4124000c50024001289a450040e00960003403217800c00091824011800e942e203c1d00d85071340d0080d00955603035102e031a0901044020030303e900c02c0031030f010881210b40700010028081c80075210844681d49600e403a2410030302094849402291500c070780340100314000d02c85428085419a9004451561034040c28404940340d4806404050601e20980c100174a003071005402010940301030000038070041c0d5403050240e91604074400f1504c0a0380040098540208551384072039840300b202c1d180c800c00c0720032201c502814069180c001000240c00041e000401300100e101c02c0880000c0d000700c2d9201500b040d1518092401110001050711040c001c0c41c9000350001d40bc00f12518103540d40800c030850390b807542c66440e050404803c5001d400f800c0d000086003442031180b812100c600c4d03101c8a18010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 373396294 1250 373395044 373395067
    0x6030d0504051813021002061f080d0e03030f0c1c08010e130f06020f040303081f15020304080d111e0606130204030f2405070f0c050f0a060501090e12 66
    0x20001881c5a113240c8118840e50007503030310403602020958581e0041c284504080c030400131f000b00f00b11a000c0c1c151158500800031130740006021503422440745402d0342004600d00001c2d045100c2c800f4500f545000c00f2511304900b80700442c1150001501c400006620903a02d541074901f603009203c0c4190300d250a60001d070441d09000c0c52110b03031034030510840d106000070781d41d20710880c0c12014100040749004102407040541051f1a250800c2e22a440ca01846101c90030b110040400f074013035581e5062030126803101d942e0081060300c002c4c0460900385e409159104038000c10344c04081c89900100e1142d425400001400304421010112a000150160313582e09420f103c03c00d0030041c070540b10740da400c00000001c5140304c0c01e0240820311403880c40081c0c0b9091100c580380003811200a00c00d15140c88240900542c010b0300d0510400703150f003070114400c003840c1002070030f118075600c90f000c16004140f10070003000803540c8454182c4444e40c00800c45900e0f11442903a076221003801291a10108100020046 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 373397544 1250 373396294 373396339
    0x312090d0807140d140a0f0905070303050f13090b01170f070809030c0619060e0705160204060308070302010c021606023c030c01050105220c121406030d050405 70
    0x709480c0301503a04d0101c1c04083c0400700c54000481021002401c1c05000b078034060741c00303900d0240c21010700a2215056944400745c46403000c0c800281404000a610300e14030041d501551076070b607004002006459600d0202c031000c0c000c4e00090a000907800a41c040214200c8515940505001c80f1051400c1c1e8032642e0507a580341004c1c1c868003803407005004010031150200508c1d4454010810304000c03070145041a50103503446ca4110881c4510181d0821142c01e03403200545240c0b42c4d58150307a40104a02c0d00100340100034a40003c1c00382d560010b1207505040d0150032591780448640d08031800d10b00340780d11018551610340140001130300001804180074201001c1d03491015496494601a02c20480c500444c00003000c44211081c0c00100c1d000040071800c0c8651401000c082c0e5100c4100c40303203540b065400080202c0c1840d001959450b040304814856607004049003518041008001014044088041070448025102c0e1080300c42c2c01c40250701c10000d031401c641001c1c1950440e08124400040704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 373398794 1250 373397544 373397567
    0x140c0a030c110703051b10020d1b080708030601140f040e04050102250b010803180d0321020d050c180607140a0807030e04091e0807060e0312090d0807 66
    0x1c101c0040780d0b2640c0b40005000c00401140324600600c81c0d02d44880b8840c1148001003112845100344c000001c1a154002c038103150300a0503803a1810344140c1091806849600002c0b000d8507082011914204000420b8025801800241c031404c2641444d01e51a1070301b44180d28400c0c03014003040c00100414001541c281350042d100d480050300700000040129044510b8200001e00010300d00542c50511001c4071707000d805008400c0c0a1464210104041c1c0e003c80f045009040c002c3c0c107180300080c00c0c18411030150207030103c0280110401008442c0c410003940140341060546403404000c00c840d0b4001904841810f01100e40e5805d850500c1010000c03280c100d07580960703201c0103410407080609000e2023a5040390b032040002640358840c41c18000c100405c00064580101c0c0f40145c2c51002c40c1101d454210b00e84e445881c681c220703030400d2030301d09072a00913030783c00030011810800403030a84c3d000030000d0046142d40d0300003005299910070103e6030345c005058400002c40d1240700481c184038441d1081109 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 373400044 1250 373398794 373398797
    0x30a0b0a051302070204090602030f19020405180703140906060102070b0301180b0303121303080609060906100e150c16030308061c0203061003030f0e0a150e060403050709140c0a030c 80
    0x5100125071202010399004aa08031178008031541007208033034000c200f880ca9991010360843c00c107403c00c2c01042654215895401c3c4210341e90740010359441c800d40003201401d6807030002c4401814001a40c036076034035081d203500e400350061207004220314040344141c0b03049503e0309050740c0034104c0800d00d0a000f44085034503150140410005503001000550400d03003e841007210084198255082c000d20a1070042c0c080d9114014840520004c2c2e6583e0114540085085030060f000301d13000142900d0a2503030301d00d0141c21403400f86000806100d10b0000c0d0035070040f068150f40c6042001c05c2c407164641000d01006010a070b020700400d4560074050411901e103c6480105500500180c00103843c2210448118141d040112010b00070141e004c40c050a941e111400c181900c0c006510019010b151180235000380d000030000740d5015039214807440305001d04003500c480d650300e0f00c0e41802c83e02e0700524002c28440b1401c0c0350062902d06400703030241c7e11407650040d10030b090101c00b81d07044001d05440b030001c90 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 373401294 1250 373400044 373400051
    0xc030605131104150519091e120201030f0b10020309040525110102041802090f03010c0e0d06150b0408070e06060702120a08040f05090a0c0c0f0c0806010b030a0b0a051302070204 78
    0x4071800e024071b0141c080c00040340c0700c150f941803030002da83c0c0301004214410740c0004101041040898002c5605074105075090a012134070000c1420854010034032407848541c0a056465012982e0f60040000c0070613410a0f1414030065032107041e420119008600c01781210144801c810460b180f1401284d11000d05060000d450681e4500c450f0586c907100002d410403070381e40050101c4e00e51518072130720400d0f07000039402844020f400140142c40c9000d071048131809000903000c1d030010800382e50b001c10621010030420400568551618074059086400b45016603c1000d03404586074407054140c074804c2c0d8008021610b40070903070382030102c00b80381d80208000a214001800000408550141010313002081014000601d81400c2188841020b07194150540c5000700d003140503640841d0303000310b86801001d0781000213017a241038001600e40390b10120a80c020900040f800d0399050300110701460a9a8080c0300401d482e900700310111030b4610903141c1c04021502e0b40200521a034015040340c500080000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 373402544 1250 373401294 373401307
    0x101d04170a0306090614240d150302180414010b090a1e09030509130203060d020603070203041d0f0601020c0108041113060306060504051b030103020d020d0203010c0306051311041505 80
    0x81303007640c82942140854182503c0000a21309086d01014140c50809205014141a40709242a2880355048030f2880940702c101d1410b000d100700780072000555029040503030a2221181c078900d407100035035017254800c2d503e1805a0000b1414003e00c030548400400d180da0319151100c075503004100c07d01082c5d4010f0b000e0340101c190307020345114000c405030007900c503e40c1e07441144080000c5540000c5c041c0503400d10601c01d03c4880d4030b803401e402c14941c0d03040e070362217649880c0c01d002a4a54020b5901c0409600c0040c0c50881e13850501c00400c42c01440142d02c110400d0f00c561005a0b200c00406440c140020880d5000a001c1039140c0d0a60f41075000260140d03a61202c540180d1041d5100707904242c90b50b9444135010070503420144101903104491710102c0c180f6155421001045110600c006442003085462941c00d6588000c4000e0026500600800c05082d4518002d40075004500c2854824070704c403222402a00d41074000d0891a400e8026068a06402d2400b19800384180790000d070100710003409032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 373403794 1250 373402544 373402559
    0x100309021008070906050f0301050402070206041211180c030f100b0408031210030f0b0601031e09061b09271d0c03120a1d0405101d04170a0306 63
    0x115241c0221980d680000e41c0f0300b0807000341c88005258000740402c82c00f000f40301e0504522200b0740307040d51400c0354096034420381800003079a64040e0703400403100c1e5580f180c1e890013000600e00d48540b4150307003030300d641c05041020000d801050908a42c401c4000d0310800000f4100110b0340700c40d560000f0304a050500271500c40c85220070b10780003a00107403100da000007513101e90803489180090f4002e5840341c5141c1094195903030a40b190402e090000c01c00c406140c00700d207c580c000d81241c12a005040080003032070300f030000c50348060058000141c90280c075060548004c0b005240c031402d000986600c507546504d10b05002a40c594001d12100d0352a0b406440c000390176503e4501843c0551820500b00529100740cad01d04441c1014100400c5a20a902002507503000034002c01c2034134102010780c01d104020132841d0f11304150b00124140007550040c9020708001a40034142040411b41c1c8092a0509900d003201000c121100301c255000380c03591000072104800b00680e000100000c003201e190214403155a52003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 373405044 1250 373403794 373403809
    0x509010f020f1c05010303051603210212090a0803010b0c0c090403090305120702010c030e030a05010f1e1503020607050a06050a1a09070f030c02010b030a1b0b0c03030610030902 78
    0x1071014510b4000440c000358407a550510000c0d00e41018003003045515550307020b4981d00c202c000322161480b00d011808249030043d14400402c281e4041c1c00d00c80f064038220541d00a52100c4031000e1400c0500000c070784030403000100207900310780c400a034a113181d0800c100d505958008928030305007441000320110b000d0306d440910074010381c425141c98101504500d426801e201d40d40d0701d90200c0309824880da10160fa07020b96005180754143c180010110702c8140441d05110130400007418560034030304a010035081c10303480354190410088420702004848415841500c0102d4149001014011414005071400800600f0300512520450f59400541e42d1007006451040b00c00e0f18106a0b101da402405000c41880d0030b0400703904071480300d0b42e80740088000d0100c0100c80c03240001c241d07482500c00d503154000d600200a4840090860b061142d4a103440b04c3c05405255480000a604000000d40c84001d0016030ba05c45400c880074604565442c002e110740501111400e004140d198280100980c98240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 373406294 1250 373405044 373405057
    0x904021303170c0d1d0904030c030306060e0d14010902090405060105090a05040519020f1302090f0105040510030504110405010e1806070903030c05120c0708010e071202040509010f02 80
    0xe03000e1161461070500000c0110300801940d1004800c02c00c00410f04800700d0107070070118582c18070903a00c400401a1400e10005a2546508240c8540c140070a0542140c41d000819100380da09100e4652604011a24032020800180c0c1100401b04440000380c0c158001d8441102000d000140802c92a0001408280290f4081e141c41d00803030018810750900000c840d5204039102c1c020300085c10540d4600780c0c0e89452184031240c3c4521038281004554804004c2980b41600078003a0b6059000e00c1d000b60000d40c840c1041d68031403034003c00c28039101d50150707003510102c0308000d0050031a00c0010b841a4050310006108035003000103880310140680c0d85124950291184881103004c5142c0050051710300c0020141001340c0768080306c10410303129030000640040c3c82d410b2410584c8125030340360003480e0041c11003003401e0585011960705448500000c528080342c0001009106102c2100005034842441e4040e0001b1144840c204202504140d0040c0c0c1e001307a01100001509240300320f10504030f800c8103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 373407544 1250 373406294 373406317
    0x3022b03090e0c09060403081612020d17010302030604080a05070c03080702010e2b150203010314100219140c06010b090f030f0d0309140d02030723060615090402 71
    0x400e01440310325604a20b043d40410303207140c80c51401d151440014058040c5100007040c1240c0040e05502c06000d007032540c4801d56000805d070041000c0340700080d44130041c0f240718030005440c1091603030a0400c40020b40d0f040b2034014016150517155600d4595040d44074a184c034062040410000002500ca110f005000f180a4549035445103010302c0010701d02191705ca6403038412003110011030390008071881c040000818100543d81e04030918640780101c2c4a0700b0b4680c125141c400301c000030a01003403441108002c242c030003e591b250015500701104034020034032041051141461075100041c010540c401d108000303420001c1c1403042124041d0f10f0508241c00080888101003078414084c20171810074842004200c0141c10201c0100d003e26a070b521003800c2d00c07001c040e12000400244184541c06a9400c0c0201013900c2d441c0941141c040d43c0e940c40801d00322018201070401d45c4030000c0d80c2d5105920142d20710050601500d600041100848511240c80822001080046050380d40c62000f0314409000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 373408794 1250 373407544 373407557
    0x80417030c03040c1e17070504060b03040203070503120d15051e01080604060302010210090f08031602120a0206041101050415080907061103070b091005040303050906160903022b03 79
    0x502d000040101c0585c0f2094203000303c0c031200200341140103191420740d003003001040e03440848480e0042c600205580455003251800318042002c003184002140700d94004d80842e40c00503590000c6c1a600c4142c0a000e000b08031007402242c0d01009240c2041c00c0e40f14001c2d048040550301c520024200b001042c0c0c03005e00e80581c0e50101e00d010b50b0408806035020404480412440e03245400107510b032a00c0001401c030740341c0d0360f400000400c0710300d071280b80c060b503001080d56031a0300d00205001e107100365207103159015200e0307508005203a080a004440409074107502a00d05078580707a5130062010502249035050180c14080440e442565490325007105640d9a1283c081e4109009a54186405d80d04414200151266440c0700c82c680001200d12240e0300080b04070040d5034251415007405c3c4c01000f8140114100b0040c0400d056240d041039002e04000c0041c1c500da6144c0c0b40361440742031103403d05400800c03241141000545410b2060408047e01c58944901c0c28841d43c1c4042c0005107400401c03004a01d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 373410044 1250 373408794 373408801
    0xf040e0a11030705061b0a1a040b0a060f06030917030702070501080907061e0c050304030b01091a150c0304030b180f07050d061e1d010e1c080417030c03 67
    0x10381905490949200b500544100c600b0040410300324070407154044040d610a000307010100204124820030690001000c050006109401a841c00d20903034090301c2c509000000b0075040c22543c45840d0442d09140362102c0b4007441e010307040d000751540c024183d07010404141c001b0300044d00d441c02103203d0341003035000c3d2003080e00f400005044040b001c0c1c680e0640b948040401d200450704074804240040c0740130f00303844d1019404c060450304d030601da03040146a40000716001081001e00d900c0d85040c8d80b112242803020b080305014000c01107014040c1d1903807007003411a642c05060701910085c440980540241d9190544949800070004020b40314100500c2120b0501e0f0641c690a115469107504900080c0a08920b0040001d850006541000d006265101040b80c0e0b0819030781c20101040140d51000d10039100d42c1d01c45641000040ba60b403004a5003800d5854200d0207003c503501040c00b502445c80014000c0c0840105c41c4407200070000c41e02d43c40600d150540e1012204051403103100e1400125940f0701c1d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 373411294 1250 373410044 373410053
    0x213031110030504122d08010911070f08031b0408030c011803090b0a03060918060b060a140304110312031603090807020915040216020a080a0201120b0f040e0a 70
    0x1070038580d1020405140000303100001e05441018040c064141c500849229084c0440c203d018000040a0450310102403641c0c0c101d54100426604031007481b0000c20040c000e542e00212544960a40100390740003c1b00c840340012602009150003071421101d40c3e1307688401006211259005400420044c0d001003220100c95809004441100f607103080070014000a903035020b410004580122080b103032000c9604a80148640c0c0482c005010010003881841034100d5017079503101c2102c006440c1c4c1802e1050f41d949509003541200c010394102c0d074074141c1c5881d66108080094001400451f40c00c540012081076075030781003000c2000e42c100c42d68442d640341003400406110440360506441490306204400000c5484507007954040c1c5e405440d400125a900c02c5181107003151100b055034824404242035003c2d031005201520402d1099980075190307038403030354030075904c50200c079000b40041d480a458000004c086d8003c4800c2140151904030124030000000301921942d09540210b0b500c078050010602 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 373412544 1250 373411294 373411309
    0xc0304060e032506030f091a040b0c1c0e071d0106030b03060403050406050a0e0901060917121615090812100302010e041503080f0c0d02061e070302130311 68
    0x40d190f03d50a001a00000b100f00348641d100c901c9a9018155110752041d0800001c0e0007011116600030a03801d82441d055510075030410040c1e90694081071920001402c600c1808200e0715403a10b00082051714580040740b00d4050008804180c001d03009020000444a10b0303004150451640105050040d606208005003268241401984a039002009002c04240c124003150191241860003903582e02c2444002d82e1074100071215a07802c01d0304038000051855200e044901640d40c41d11000c01500910f207a8965122085119600e422030200803001d0140a038049081c40d0700d105500c0300c400d40c03010703c0700c14048650640040e11855030014042100c525409031559000744210180b82d40181550002480c82000d14034050050b41da170440001c00082e507000d14001950700074038442e51501103c44901d0150010003031100648a0003d00d60b05560001c01c0701c620032107035110f10300c0619564041a416841b40a4014014103908214580422402c45000000b40d4000d020321041e1789482410b002c3d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 373413794 1250 373412544 373412563
    0x819140706051801020a0e011b0b09010f0b0d051b031e03030414010e06180a050f0a060608150406090602091c050c2e02010b09041b060c030f0f03020c0304060e03 71
    0x41c1d2042103640c03041c54010340310622107c802c1c60f19003141505128014000d40021b01d0103002103100c03404000350320b02c0c1500244000c105250090200c80500c0e0309002005000c5240200240c203c5001164034040184204011810080848000c01940000c0080d0010421290085a00000f042100f880040c0e41c980039041c545a008020302e04d00c0c1c11100362181c6020f04050f28080d2444800482c11070708200401000d608241a44d003090b22815880e07a40c1c00703214070102c83c010704050000402c0e59020645100c8000407448105071a6100d542e40c01c01402409000c544440e4240580c5c0001d484031009089084030004070340f40000c04c3c80c00c0140c6031162030341c0440d20448042440c1807c0703017407480188050301c5102c490300d6000c03c1200010782c05404a10381d003d0700401240100018045008000841d0080e485003214a00362034440445141c41340c49800340120300c02150a008851103143c1300b400c6406140f8005041030034100919086501552040f0700090b1414481400c0785000e0003508074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 373415044 1250 373413794 373413841
    0xc061107050901081b03070504181a0402030d030207051009030509010306080f030906070c031727060306090a0e0304080703030e03011a0108041a13050118081914070605 74
    0xc0e80d8900a41030f039640520044c0c120890044e07991700403581e1820425040a00340c01071080c0142d448101080a15103400841600d00860428405292030001c2205500a0b6006000b42180740801a01500650300c0403000b25400e00c92450203680c440300500c0f5100d400f80c4241d84150f510400000010203075216600b054220303400c105d103070b0401380e0000811031b5034849068442c0b0780c443c155030419070028802c5034030150402c0c1a551840c1440000440201038800c2c0900400880c0c24502c403001e00d82520090180d500882c08001103516031505640095000081001c041042801e0f60b4416007190040c0d8040703002d65028050920400d9000102002c0700e0005900802c203c102010356500071040110980f410300c0200c002090500a002c54948003801100916131685d0410b00c1c0d0001148401c0c040c1901c00b5440c02e001900c1c00e440149000d0348441c1c006e000c0c58102500c00740c4020154910040010600000c42c003640640c0f4a800080e001107401100001214a0301801e84d2042460307810700e846 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 373416294 1250 373415044 373415059
    0x305040201120b01021c21021918090e1006060e011d0f010f120c020c0108060d0b0c09120f0f011d030f03060607080c0d0201060501030b0a03080d090c06110705 70
    0x11202c0c1d17400202d01e003110040006c1c0000c42c48aa800540b01e0000200252110045604001c1403281d0260010500003954110130800e0840002040b42c1d01c202150307506011034010078081214043d9604001c1e281e40b5440190365112440010140817504950700c114045071034090000420b681000506008401918030200c800a0f10030003e5640b02400c4029810300003003280c0f000b20780e07100d80d06428100c0038240c030400907003101c8900a5035601e0014042c9000176900c0d0005405420b0a61002e40c04a030311150042d020788848080780903a401a001d020381000c40c2000300c1c84002e00400c074540c0701200e02c0000d003011840c5440003500391001c90b20400c000200c0100c8440310048000111140820341e460250f459888010004550f032260550107010074502282c07446904102040d94290152160000c020303540d9180700540030783d116901d025a0080743c1403002c0002c1107452004100c00f52181130001405c19490b035491003421029000440004ca200e07804c080101410001c00d07002d01400c84001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 373417544 1250 373416294 373416311
    0x501080108012307110a110406090605010e0112150b0712030501080d0f140d0203070807021207081e030c191b110a0305070602010b09010b0a0f1409040c030504020112 73
    0xe420007071120050303010f0191010001800d581c41610075102d0030407a50245c03154194541410300b108040c2c104090b10951402d080000d4030501c603c5a80c08403072042e12131800044102c0015940400c1020320a50b02640303504090b000320900040070800740110441440d140e00b62404d110303190500e1900742105240c84c060060080d21000103405107281d006241c0760204028240e0200e84043e8900710044518001150b05082d21541b5005944111a96601c284541e0346a400c22a521a0741172400b0805107030070070009000c100507100a11a8180c1d00030050300b001306000d2082d8140e0700c21100d07401120030104204581d180380401900d0741500900c2e000002c440744841120b052a0904801001d6048803103880c00c0380d40310b900003500159040307000e50709110354412000c0d002e031226092a038803618081d0000304907241d004041d51003a40ca1a51066001c80d00303100140c0e021010380c49005c42a0000744001105561030f40990900144191760208050174148000b4200e40c04404070118a81c0c01d01051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 373418794 1250 373417544 373417571
    0xb0327030d0e030c07051513140913020907120608030307090302100906120c0c02040938071b17090a0605160206031e04050601060e0105030106080109052e050108010801 74
    0x7800151102100d007044040080240380d1fa407440340c610303901800c011500300061007060050301c0074160718080d21050043d80d02c24032546135034403546500941c40341d402400300320303d9031040300d07410009888103c0020b42c1340d80310400300e071440c2c20442d50305c40002d0f8040320034421802c101c2c88444a0406034201014420706003040606401000c0052003846a6144800034000d1f00c1105c040401a40242c0100b00840d04e608094104040b02e6a03840e8004000921501d41c0b02480e44d040424884101140e00c0d140e00c03446400c076200702409000c0c408049444515a01260b540001030030103400c4040c4055513600700d01c080c00142a101d030301c9001882001c2c005040c00322011001d801c4003590440717925550303a88000c07105060810b03a00240880c0f000d0171040004200c40091028161120754130307032400040f040d07801141c49210900409000a0240c4010000322030305801164002c103c00705046c001c1d8841403800014103046042640029480c18000c10055070803024081c05807560310300901c80824024907 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 373420044 1250 373418794 373418803
    0x51c0c061704060c27050a05030c1c140f01090b060a06020d0c03030f090b090622060b060412120905010f1b0809041e0c0305100b0327030d0e030c 64
    0x2503c07031601c546002203950311800c0c405020107020b03030b0b000c43c0c0b02c0e0303803d10b040c400070921b401414059030113554081414580010f50540e00c0c0c4c0b0007406001301d8a580080c3c5001000403642c02c8034a83d20a104c0c20480000c188030040000400b9000001c55000b01d0400122152015201c10300a082c02c00c414840940d01142c92240003d060801030346e500300500c2c040300100144110109400d00e441c82c04410004111000d81c0110055411205140caa8181d031030140d0760701d14802d02d55565200121400690fa03070b04044c01c01c0070024001d40c205035585820148a048103403048412068450400d102035421161400281c0001e282c403014000704914003030142030140c50300090303408000c01154100418001203e103121b03409042805080d1507694044a08440407030014025405c0c01400180c2502c280b0500f4450484148002241c600c0d015142010b64806400440700c1421090500d0044001d030459800e50808407008541e198600c05c010021215603401ca18181d41080100460b030030400503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 373421294 1250 373420044 373420051
    0x411100e011115010f05030c151c140a0903030509060906071206050604080d020d05070507060e030321060307090905070e0601180602010603020f0603090d0315051c0c0617 75
    0x80c9080340100011107545040c03045600c0c0301d0a1080c0c1d0002180c40e022400d801001c961050f021681c080308588c0411040d030000c1859601000d1041c0720b00c0c415180f48030400c8000340035504001545001c041d10b40305d14045c04480c003040c41c0351260b404004140d41481800d9000303d144010700b0303441c10700600b01511050040c010000b0800090080728044010754010401824000c142d1a950781e5225000ca403504440d01c05c1c900036028508107040120f000e0401c507542c1070b41c404054405c0904040040d034070b20600c0c035041074042c030050150301362400840d25440d81030b0a2801200e14a460b10104052420849030014a80641400300c54400217500207800e9003500d05000c01c6e0301c0a55210700040754406003000b88000c6242c1440c5001a08503010351107481600c0c001d40300d109814004100740a00ca10041e140e45805038040640c1d1500300c0c1c42507104001c00b00c001032030340c11200e554400054a1401c04d201000302d49522040000c2005a4101c408004000a0400b04070002102d10b000720340e4071004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 373422544 1250 373421294 373421297
    0x918021203030708240603340c0204051905040507030b061e0d1b0905090c040605010f08060f10081f06141309061502010b0604050d020f040b0405040503030411100e01 73
    0x14010f40c28136106170303521500c09540a07104646920380201c844110244c0c003c140340007241c02d01800c0743c1c0d003440c44400e003005c0c0125803942c0b01c4190081d0b0a02004040040141d64000381102c40100009660b000710b41c0240d000324006c140e01400c600305041081c501030589489020070b60881c1030441c05090140000700400c64229010dd111805c240000c24030181d40702070040051a00801c40710010f0b8000d50188090108880480403c9002d00088400c0c07402520f012034511004490700c50320856015a0100015120484420705800414090210140c102002c80d049408126030082d1383c001c0340c5c0001c01c11413554a00c4a01e00200502100340c2c078044441160b400080da0a494501102050b0040c05d07007003400c010180d6110034141c422800980c40f00010750a00c048401a03280100584041c1c0b4002000120302a03060307800c004110020718440b64119481d040318110035030f02c81c4a03141c462406500515601d20b05072500c408442030034290f0300e106522501c0d1001c04240c0c854080510520207 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 373423794 1250 373422544 373422571
    0x905280b04170a1106060d170306042a02060a23090f150609090d09121b0e060112090c030f110a06180b030c031f0918021203030708 58
    0x200d09240c50a82c040800031510180000340080c021a03002c0b100c60408051002590000d4890100b08006c5244030000585040c036445802d82d0050300ca1002190024401000055a80c040c001d0001d5014108000082c00c1e440318a80c0d0340b480c0c7d4040c440d542c2c1c0001105c20400140e8500c2043e14060303240c0303041503c2e11921034000122a00b40800040841c03d90140c11109160413242000803844412682c96019003000707070105a0380c00e0002155500daa80f90340304c107810303103013408184503189042420a590300d01d03200084140180c0c0c400058005080c45040030001441c244001610104a1a0074885803e1401c20b42501169480c02150b081e03a43c001150f03c20407200d4140002d06610550440b07070701a4280348002511500015038a015030080141000c60982c0c1c0c86c0d03000c545010454074080051003c0001524525440d29400e0808140b0b20241d001180c4071240d2108403000e41c42e4010440c0c0b242d0600c14107602d411b42904402c05902c00c015807542c0750108000303101c108042d25014500c640c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 373425044 1250 373423794 373423801
    0x60b0f0f1215010f020604020108060114040302060705031905070b1303110f070e070c030e060c011104121a01150e0301020c0d020115060e09040b090304090507030905280b 75
    0x200e034119800140c0084000c1d40c24140004400c50002a006400d80810a1000c048510600121301c66210f10f40503100c881542c2d64003001500c1022580d84c9210072860104000f200698801000c2c02d0807a0041c0015911b400c02400302d10042c104a4840f4410300c803060120f003002a107030312005580007a1410443d0b08410720b5103410746d00341c00500e002113003a02a46c02048034210000500ba412108206100310b41c0c0d131034802d0140c80c80091380001400003100b8014000702400d0003001014107200c00300c000140c0290010245181e604503800031010010810750660a100d458107840c0e0841512150050075545001107290b541010a41804140003200d00390001d140c1c0c0a6065a0421800c0400e9407954030b12020001d000301a5804100384000300d02c000800c07014413031708001d05044400b030403212030354807107031030f40207540d000100407841901c020000440c0c00d5000f805481e01a0580d500d000c01c02c0350061510509110080d042100090b2041460300015055a040d01850640040c1421070710346 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 373426294 1250 373425044 373425067
    0x40b010b030903030a11070c030f02100504140f210a030f02010c0e10110105010803210126010b03012a0e090118020705030a080609100303022d070303030c0f03060b0f 73
    0x240381000341230256000d0002061010450f4a400ca0318404c484840c0b0201138141c060310309004030301031aa2680305903d0f48540302c0c1000c105c3c3d5048004000c18040e80790366284401031580c242078441c1c0300150001420714081503007000c98140f080740140000c1c090410500b03c01000305507581d00f02c034461503c1121030b040c803c0c00742d0400b006004104000340000e6840d446242d60320b500010140000b8101641014948000c441c0f1440c186c420503d056405120041d4107a0b18a02c1d00c5440340799155658a20300c0f01d256000d101c0d50440d5003241d900940400c1d80d0a0014103007010300c02c1020144408001c1841c1965264030100e03042d20900a405510060800801c800a01034168010501c2c400040d80380050b907001001c06204000c08c441c00c07480c6542d04d07071b40340b0340130840340c80024056848000302c06003200c50086144e1804c5003440070095000c0003240b03402c0c40e03d101c95209802080c2e5818085610981c4128a4820030503a07081c01c3c4403140c907108000d1b095106040c9140c680303440104160711442e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 373427544 1250 373426294 373426297
    0x306040926090a0501030605060708091906030609050601170f0a061d04050d0516172104030e0307050108040f0501020f0d0c09210209042108040b010b030903030a11 72
    0x2501000308446001c0001418180507600c8104007500c501280f910001d15076100b40601025100c001c0c01c441d0030f00100365200071141c0c20002d02a0f510520b1118a81c20716480854044000d0490b0395020039103528203860081102c0019280a0403c41c03101002041c424100c440303150441003000c1003e0f0540e88a00c01e8800501a5130060000116031202801203c200190024003031401017090741d001d14440c07030080e1a14032a811113a120350520112100105500c90800808508120345851401c40d60f26240c068458103511951084800b4009000c245a070065000341d40344010350041c058203003040d00180000074006c1c4024402da20600081040041c20b40648101200ca104402e448001082d04200680b9885841000090201c2d000240300b281c14207100300803015a04800481300d4280e020301103800300c010b00980b04485651254030f075801012401e03840803c9141d6071011182414900302400c201c060340315811140741401480503442c8041f04a98002c0040f102c00120081c3c0f203502009607 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 373428794 1250 373427544 373427573
    0x1120b28020a0c15051b0a0c120201051f14040203091c0f030e030406080402060a1112040e0c04150f1e0c030e030708070603150e0a0605090c0c0303060409 68
    0x109070000c00c0c1428803640051462514074070540403881d0004c4081a040100c0740c0454201030200110507600540c0782c0c101004090890491030001514000354840c10380000746429404c0060790f4a034200128900000c1035119440c0c0d010001b52030452034013401c04180c9809140451107540d0002c003141912804000c100740d20280ca22001c10040150b50010702074004401d031742d001180c1000000c80c10030704080201da050790700a46131001c454071150248400e03500610004c42c103010107842410000e0300c0c100025582000215501507640741083c0c0d50b8a40c0c00e01c060700b00701e0b503404180000d0001a010340000c034032042007841d1070040031201101c03c4940411000140440c900e25940c034220b080c1d40180f2031540342d8020b0311103040c900e00c44400d1564800c0760303100d507074420340044500340030712803194200c00c8000404030481c0341100d84401480802020a42e403d4901940e100000c10140c100b0341c2c51554032400180901d400d020400c0c14581c1c4a01c0001c20390f51289640b410604200500038070110790 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 373430044 1250 373428794 373428871
    0x50a120902030708150c07120e01050d050a020a020d0c0c0603020c160909200f12030c060924070c0b070c150905120408030d0b0301061d0f01120b 64
    0x1282c4d0360380714036549580c02e0200040e1089007001c000341d051400d070b0040382c0025501c5008130b081c80c400d021003141c91404510049042103010000744180640c1c0d03000741400352401e0240140d41e2400d4010182c81d1070022201441484100104500400d0b111003240041741d0301c5050259554900c640f00a007081241112017070341802030740010540c6030b0f00d5404039030180d00c10307520001d07400d01e28401843c07582003c03c10103038040409600d50b0800d050200e02030b0803c503031039021a81820f0340404800e0a1034001c4415241541c00365540201c0c0f600c8850035141c130040c87c04964003140c105607400600c01480240d000e4203200c004400700d540c080c8980d0200c15415084400d1540e142003141031a0090020b00344207031103520608900d4024240c02034200e4048900301c01c000c514184c100c400c80e10140125032400755240d56942c03c000303155448101030084010034820554035914013580c41c4940400c068109054250b108031800b400680310224450300842002c4a44103040403034421032682d10b9170240702c0030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 373431294 1250 373430044 373430053
    0x909101a0306011403190902040b0d0812071103030106110a0c0e0a050a0209031b0a0510080f0c130924080102040608150a0303140c03040e0a0f090201050a12090203 72
    0x39568441003010710b0051509980d104004000880a00e40c01e00094942d0307078485100c80c0c2c02507401032481d400100124400b40010444000301c00c0055410400808151802000021a014a90250040c055001c00c1c0b50400c420444011070a007680c81c0414001c2c042409100f0b06d00d4207040f2010401180050750011005c903d158588010b280f1041040e00d400140d81d04002c0803400001d070343c3c003d5070350390748020f0300400e9590441d010f1f16042c00105080b42ea0031000c452004143e589514400b03803210031f02d58440220301d052030070203c401000014206035404c0700a11550920f175641c6a0044200d0308114000305104031001010781c120310034800c010321a0496500001f0366448190050000c45400d034965508075616081c02c142e41a44440085a014580b1002400000e0042e840804000100f01c5400d04000c64510240c4c5140c0c000e070820507102c03500100b0443c0000203030184c1d10000c02c00c080140304032074050340003900e580035007484030050024000e01d402c2e80800301c3c3d104030f41c00d980050880b03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 373432544 1250 373431294 373431329
    0x14030406051b0606010e2103030106083c27070807051801330503010338132009130b0109020a033902010c05090910 51
    0xa40300d548000031820300201d020402d05038642011800744e202e6001a1a041d55004400c0104503204450314030074080001880084003100504101840c0601082d03110b10225003006030a001e007443c640007040c038900c9804d1545081c1c0c000040c03503154107088180b01680c0241c46000c0c040285010010036291054065007200200140010b03c60781120b1610094a800750b440324144a4003010000d00c24824072100401006255280482132a003884007624001010500307050390a410324117182c001d00001c0010005005004810441551a280180c9070f0000e05800342500c41c0e00c0c030142c2141c40840c81d030318000134251140c1100d0203032002c0d41c00001007110018107940d000960000c0060113000d860790304000b43c0101003a000e188541c603040f558000300c81e0320780302028001e540b2100905082507150300c4071007403000d0740100c00e00075043c0710303208660074a00700f442c6d061000d151529010116030410400071104c1d50403038203d80c80c032039003a20f02e042c25540794407c50f04514025405008409000085c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 373433794 1250 373432544 373432547
    0x519020c01090f060c02060c0f0a0c03020a170604032f1c02070501020703082505030a080a0b0f040e0312010b0a0905030a080306011209081803010f0905070302090414030406 76
    0x50119204090b207404074825281c00b00c80380364510f68010480820f015992607009444c01002500000030218100e0380321950811915040c4513440340d040304d10780200b840500851030030242e80c101a0030710301250400035035100811a81d03450064000b4080c0300090420b441040c003000c00f01903104d0300001d48040409804a83c80d41c0d1621070304000a20401c91045156243d480480c45d8801c8980590050200f2409c0d51200c1d0001da2009030000c107000040c0980000d540082c0210600e81805040515100c1c841000060180000140092541803510740c100c0c0059441c1140e2403202401600e001070345188864405107980715484e25180215101400040d0030302021004142241b590b0b5151000301d0350719005d041c0e65000318a001041d4100070b0000444a51280c1c0c0c1030035101c1e580da1408101c0082903141d0444503031003652555010ba4201d0b4240d8000e007030034011512132903800341041048907819210386451f501c4a010084c81600c164012a00303201c114910300c2604050360055940d995500c580 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 373435044 1250 373433794 373433803
    0x30c06030720191704080d110c240702010201020f0c0703140f03070305090402070f1101140315060307170a0b0a0801090c09021b0616090807150c03051902 68
    0x507001100401a810703500c2c4404049140c1c115084036004500c80b006490740c81c6500d0380d00c0b0540041184200340000030f150740080100c00f58007540380d11100d03e0300c031441c1e1b0407500b00300f1310303c409034082c0343c9000d100503c003180d100200040183c100030f8140c40d0701040c0b004074060b02c92229846140e0307002240d41d104005010407035100b00ca2181000042007a02ca00380282c58540007241d4a160390004d001000220380200000e201043c0c0081006142104598803400000020b030030a44841c09034006801c000d50700311002242500d410a80c0c0303810b52806409041810f0302c41e06206001d4100032000c82d4a1500622404600b41001a00c10140d0300c2d1502c202c0c5c0c0103100e03400750503201c2d818403c0001481d02c1c0602c10354814a03040440c8081c56410900c840c0083e60001040c2c0c65440c0b40032151902d0001d082c02628042c190f100803004040440d080000c0c0a841e1941101900e600500810440d44509110300d4441c90313820305111805030402d003004da415000d40c503000c040d41d048144080802035404075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 373436294 1250 373435044 373435067
    0x30609060b030606120a03030c030e0d08100803070f020d020a0509090a030e01050909150f2112090603132609031501060c080f040305070e070f0807080a0b030c060307 73
    0x90441e1040e40c0c910080001145c80a10b121085411254040000c00e1294100f08035200060034007203048001c143c00c1a00d0503032046030341000a440780042c419601c1140d0021030013856001c0c015400d081d4282c40b8540e115507000b01c02485011101d2a80c0c0c215103605002000030003000b010019a40b901e05a8903840c1e800c0d03000220300280800f041d2109035800f4100340c0c0c414100103413004030707903544100c0c0844403080142022a44084e1080500d50595103003121003130405400c84c10850050440303010185800c000e030281c5040c0801c240500d62450312140c099990101001c05415204202030521a080c0d07081c6e40c424405455000c1c0045403207203020002414a0750081e01101c00c2038181c0801031044110030b0040d8000603400c001c0400100790864040c000b0303001131120403480c0541e81d580b400d151038070951012501d2103100040081c500d400504484010340c250a06051500e0110801412460700030583c056165a46c2111815a2010060403ca070400034021640c4d030708205202510404103407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 373437544 1250 373436294 373436299
    0x40c060f05040e060d050c03030d090b0603060601080c0d0e0a08030115030504111e040f0608060a140604050903090409050313050d080f0f0c01140103121e0f09030609060b 75
    0xc510311a11403052045904585074102034031015119041003004a000124007500c1611a8078404280d6980500050001501e01000003815400034a000d16650f4130081c800c80c881e401090030080c440c0d0308a810698014400d8900c41c0d603a00c48c010307020700140070f052102030151242c0b61f0140c0c10499528000c41c1a140100109040820b1450044060f43c004030340007007001c64a900710780e01609108580f0000e00c82d8941103081800c0709600400c046400ca040d034801d00f603840d1001000b0035041407003400d07086965000103008410181e18000721461010303100e540600c0e074800c006400c000d02401500c09155000b40300b4403060169080c00c5550350000c100d940f54040399880009481e10307003010030204540d030050a6500784485035880760b0007500051903005012000b082100c95626082c82005820707003001c04420015415801d00320486402041c44106002e44e681040310311103441d03a80d02124800c00d180016002c18042011917403c1c45a9000402d0917090545802c02c00950307402607807181c44203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 373438794 1250 373437544 373437557
    0x10306020319021305133305060c0706260f0105040f060305060c1308070b07170c061308130e0a18030507030503090304050a030305091009050f012006040c06 69
    0x2c0300d00b498202d03c00c81d064021403c01d04401003185041c400364601403050a00300c0040c103000c00164500d0301030f1100c1c450800c1401030721190035000910381144006000c058a07410b0800046402d140d507611110b00a0905004841181180c03c040c0780e081841803032941c01d695035550400980300b45500d5000e00415114030f08010790500c2c40c00a5214110807250040b000b0403d40d04d40c7c2c0812041c079800a504140341900b415008100410300b00700200c000c154a0f603803560754041c58201580340c80f080381c2d059184400c3c2003100000c07040000071426000107000c2c1c0501000483c03407502c0303456442032082a0120b020a200009207a00c1c1e42c00407144592041003040c0030036046031144c01304100030144000e011510a0011a010900c80c2001d103a01048074411a031074151150000762140300a03900071000034400051040860505c0345000205d4002c0d4286002000d044c200040e0003d40503441030f504001c0401a0b0a40f00c10605074a140305100c5401030300c00341e0800e818161000c207141d001e100042444d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 373440044 1250 373438794 373438831
    0x40f0c0c030840050102040308030a0b0f0a03150b03100e210406110a060513020f120c060904020706090503031e060f1507060501060815030109020607030e030a08030103060203 77
    0x25010f94000700010352007202e50401102500c00c0440d508650014078682c01d5598203070001d4001d100070006103001d202c6039901d03850062404070540301e4401905000b50007010307458083c0d40b180c01202003601d0340240800c0c10000015601c0005001840344103915200e12803408128406c694802c1c00d10945070700c2911030712290207034040e04070a003951480017a1307001040b0400a0b80c0c8100748941800f0704410507213840e595580c4a88095550076611204603410a00804045107492161400e4110050301c082d40460700603000103454082c06c1210a0194000042040d50b940d126812200350036440700042103454200e08000d0356a400441d108903646012804a13408030702885a0306110310b100521400c884401c5205005c0c0c1081078500c0d240c1e12000030320000b8006020b230b010f068080c0c58195a09901c3d4a4100d8604d208022540d4042e0f001340d240400070400342c0c544134115481190103080000007065040c0120307141081d100d102404204000c030010081081c00c0e001940603032440d0412180b09074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 373441294 1250 373440044 373440061
    0x2040914150d051204030c050a120b0c0a031103090c18280603080a030504060b0a030b010302150c0604110f0405070f080903190c1e03080114040f0c0c0308 68
    0x280151100c1c808001c04000d440c45a180c9421441c00c482e00c00c00030b403003042d80c424584850640254000301e91006480d08103000a042042c41d04006020301c0700349201583c2c580d00c505207101409040e080c01c004001a29114880c02504424450780d0844001ca40e00d261035000691503102420340c1500c9280103242002c6089245101c041c000c0c045004801020108514071400c0c0708107008542c8841a01c84800101150354000680a566000d450200b03007858175142c030a00316520f04030784c1407150010749400e1010402807100c46041d01d90643d03a10005440ca49070301c1e8030b2401180b2041e10184184020041001026241e140d5030700c100340d9070109a007090a0400040e1360086440500050140400a06407840b03180c5580c0c10a0306d407003c1d240340101c10519001001d040c8644c080110740042301035420020000310505d0a8a6980082000e520040e42c00030030044062058190104015054415540d16980302c100303100310400c42080301103170090b0054400e8182e40b42c02d41c042a03001000a2488 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 373442544 1250 373441294 373441331
    0xf050607050c03030703020a0c02090103050d12020301060509011206050a0f090513080a08100302030d020a02030f06010509010b0c0c0402030a0b1002010b10030f33170318040902040609020409 84
    0x2802c082e001d5800c559070301d40100c0c005c2d040309125104001c480045040540c64a280040c0690302800103401a040c214070041c05003941c800b1550071182c8100010010164040180e07980c1200900c4c04080b94a500003e00c0d002e007108e90440340d4428240e00c000248504542540c10855040368401d01441c3e81e200710800d400c10034020040c01c0b6032400c1000c00101c610441c0840c0d0701c074001e07040710720303000c2d45a4001c00c0c40e061a0601c024007580c000d4015074203614003002000c4949035560b0060100f90306010100e44516018410202c04400100e20030400070010f10491038120000b038001c549a00d07010b85e03800003415940d00303001d01a0351004541542c581c0b040c01f40421003107000e041c0410803800007108500070003140b2500d95442e0344e80d41321000640700c020b9400345240341110004001e58001c21400b800b24a40743e0111010302e520900e40c0807015404001c0c0e45400d09910a0b00c06112104c2e004140a0030610304001d601901d00900480c0c540015406081900c4e00d2160070044440005d0034000711 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 373443794 1250 373442544 373442557
    0x1b191a0921060a05060409120203090f091506031305030a0801140d0b2a0d0e07060f2c030a060c090602010204050a030f0317100617061f0302160f05060705 68
    0xa42d00a0400500c80c0360442d00200e820440107480095150340e00d80781c0c400000011412030300181c00c005070011303480c50112014103130418100c13005226420003986074091890842482c41c003031391010000496501d520345245540c0c3c0c0d001010f1b6a030f218003065004007014424024950b80750305455920205040c4402c100031480d52100d0200c4070f9448040001e504c1c501e200042e00b030118055912106194840c202a04a80c03a04c04401308120740554112030502c0b0740c507044101041501140018569400484501d40030114003807400003141000d020a031107001034001e103401d40b0820b0901c0381045000e03400081045000d9460040c3c9030740703d081c12400e134803035032182560146024034203001103452039040072622842400c1201d40709400c42070b04006d0714400c0314083c1c081d00c207014082024030b820492000f4013231814079170300f003241c508940003401140c0d511580c182130141092542401d00d019904031942100c0c00b154000b6402642c1c03030100008c0440c65001c48070b034014030340071800140c0203070301741c409 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 373445044 1250 373443794 373443859
    0x2030c030a050c130e04150903021b01170103080901090e100501051b07181b050d05100305101a19030b0705070b0406050702010c021b191a09 62
    0x3a68070303514200405440c0240820b41c48410030002c1900d50003660b10b07a200100030300410f2002610705030404081401c06203112041c8107081040100000b94042a10000d1070420710250034243c42100040f41c844001c0e4140c440380d075020000200a019541d40035264000d402d0b42c0345080c40b07899054140d0508410740c3c43c080908030440007070003658041d00180500102074080746041100d102440752500c080c0e13501c0010450031034003402650301030502030102c80842401a122038131200700c0004006215511443c0c0680d2307034403408141c180c10070340d0144009503001411547d80e820321b00d4000c0011b20300442e01107542028010004101d04001081c5c56021600e400c002e40124556140e06c4144038000f041c050401808200c1e010005210240c684c6c09035000360000030f05441c0c0210041c0c211503803100c46d40c040d9440002102c1e03817041c050002da201618241c803580d2802c00c41414000740c1d0384494200c1c10b1450583c1c00b1515003014500040c00c00354000715001441101500346042c0f1260104602c80c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 373446294 1250 373445044 373445047
    0x31f0806070c060f05100513020a1209150f020a091a0a03020a110d031b050913111b0d03140f0411010c080c0a03080c130306180804060305010e010902030c 68
    0x10007450040d24a814920b006107030102d0303141650900d5008480b4102c3d507078020910358500900403401c054060701c044480c035810440c94888002c4c40a0035080032034001c5942d0f5500d80d0b20711020404503841012000148002c240721003040050f00a000e074014481c410300203146403500150444074000c1070591011151b090529105d42810210003039407198420009008680f907504034203260030040c038416488242e6001803181c3e40c0300125451180c85a8032032081140500c00d4110740c0c0d0703c500e41416214800840020100c1c1e04c101c41d105503020352040f42c1c4007400d00340c107003080141d0b0114212825490381c2c0c0c0c3c100120740703c0a5444115140075215107498000caa000180001c084080d5001c04400c141010541b16495944d000d0350b5902921980c3c0407034001c0200801090780046400380c01c006d981944030b0401884940120444119106c09005141c440c007040b0004009590a6a0041d40141c2010350f03440d103601028024020038440c041c5444c11030f100020f00e100389403080d2809944130354101c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 373447544 1250 373446294 373446301
    0x8060906040308060d1a0901090c080312070f02030d0b04110a080f010e1b07030c080726030714070812011e0905040b15120d111c020604020d030306080a08031f0806 72
    0x42109107030042c6154610365279261400081005203808070010040c3c10010b542c8c40301214255002c1c490301400280c00e1121100d0005580d54000c01a100c49040c00706000640751114400a005005c02c14007450042c1b40000d500000b641d8002800d41c407032035190317108200590b81c40461424003c2d080b10740e843d00c13001d64545148221511030040c00c4a500070325080501031f6454882000f1640310130b40403030b4940314a4252041e02c105c1c001180b8210308070854124110300e4a24800782c245d241480003101030000001d034840030006004c040d03c080400c01d04030460340d9030f158801d94804030200d03009900d1155000800046124660003424032860b4404410102912000301041000f030141407160350021000600e046001e100304200d00608030039544846813452515012424402c080d2034014200119402c802101078001032040e030419815281030f1010b40071410220300a01c410342000c122405a51414001c0c441d2243c00346024500104680229003118500307500d04524600c82c591250b003004001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 373448794 1250 373447544 373447583
    0xe090a021e0303160807080418050703050705040b0a030608010f0b0306090a1a060f0d0b0a14090615060c07121a041104020f0706020d05070f0503190203060a08060906040308060d 78
    0x4034800301d440340012500740720855542c007400390001e8010030709c0711024080511111500d03000e2581c104e03085041c108078070b0070244c034000d25602c0303140a008801d2000040b0003020034441e5001d10020301619000b009001c09141e503013805403580d40740f900d11920404001c0791051602140003501d4682c0101c0c2448098401c603d2036240b40c07002048079038031815a58000c0500c0e02d4110481c2c090030b01c03a681080c0c0515000700d8000448881c0ca1300f40f42860002e03400c000480701c1c00120990000e198010516034131300c4030b0f00018007520500c8445843ca00a280c8000741502c00d800c1500c07140c40c03242c90310210072101000e44091010f001c84004e0f0004e440d952041e101800c25900900c52260004140d51401c1403039100c810030fa0380900d40c12500d10342d40c0c000300049690303c00c0c07800301d07021868a0710520b1410022050200105050207000182e580007000c20001d60351411804004e00130031090701c2d15440c1000015842c2c00c402c860a50116541c41c00007149494904139403410708d903004c0c4065a046030110f26 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 373450044 1250 373448794 373448827
    0x5030304050d021612031209150609140f040606030203070335090108040501510614090a150801150c030315080f07031b05091602070e090a021e0303 65
    0xc0683c144030b54169807c046500900403044041c0c069400440800b45c2080e54404a4140d81c0c88084c15501c0c21030344104c0440a81040c903082003210718004c52646890400000030400b6520080d41445040d500208000d002103043d00710688a00321082280e0036174a2005001000d00c0901c0c1401d10104031804c92903000343c240700e8029008400025005074000000444903540020f10170340c00d0f405081c072484c01d02c00020a00303a41c44c0c844624005040e250803148248a403540a02e0b42409045070880689503d0941501c61502000702120507250b61509401c90820400b5800400a0b40300d400100d80a04c44d1004416018000d90386c60500300b4181c0c40450013040840000081c00c2603014001420f1541000015802000710026150091651901644081039900c3c420340181d03105400f0442682c907c1500c9500c01e0034083d1050000d140380500b24208051074018000c4400c91005021501d2030019662500a2081c1d401740000c0800310021138501a800900c60351592003041907041c222900507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 373451294 1250 373450044 373450079
    0x32001060e010b032802120a02041a180402030f040b06030c01050f0f041d0702060a110304060b1801062307050303060423040503030f161e090e010305030304050d0216 73
    0x202604c07203203503d401c24003400c0c510810717400400794010445940c04103400224680060f0199000c40c9001d252000c171120a2412840040740c950000c0b400d0b03488030130b0440001c5810f01c0010021503a91424100095440c50305036016140744076550000b41c5a82000a448541100144c44850411901411596423503010720f4243c11001414040050341410b05264010361055070ba40203a842e06d0030b000001e01d842d1008203030100140c10300c411541040070303407001c0740c1d0040e4000c0f501042150904003c41c40540100055030714600c40791000003106075020005003100c48118800140300d20900c0c0d414282d80c0220302010f0803541040000c00d0f40c9191a42c804c400440201000090540e00300300e5003000c0b250100c8040c4c034503400c0001080410444952000e0f0b00c03270360792050740201580400c0d0082031800b44e00340101485100329080e0800c81c4c0a10804001484581c1e010b91041d038681c81c1203a1a6003045da4102c0e01440382c61090f0003610b00108811900c0030b1004d980c1842280342c40d4894503100e2420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 373452544 1250 373451294 373451311
    0xb040b10051207090c0918020d06030b0a0617030909010918051c020705011b020d0201050409090c1406041208030a0f1a1e060711030712032001060e010b03 68
    0x8040051291a607003807a00d182c0d480c850103020341525201c4250103407501e401194040148182c01030103e039034249170854001c090800010380f244e03540701186000704656000030340214030000c100406903241d42c001605685400d0545483c0507a8000f80c0d42d5a40500e464440d0701002c004014400341010354850496078020950f140300c00709058032007500388440c400340c0b00c1042c01c518084203e4603404104540c001c2600b840c152114101e100d9014080040e1903030000d1203043c0040202065a228005442c090701c940c800401001142c0d14007885682a07038441c000e880011403080e01c0380780c640402502c044030342d14580711032400b4070303982c07940030603800144041c0400f1f55890301c000c0b01d00302038410341c401c42c412004640c0a00e8210010004070f0140c040e190008950080312a90103515014103441d102680142221072103600301c070009080c50b5180e044241900503000e040340c207040d8005181c452015464810340400c3c00b038008464240e807924014000c3e2100510700421203001007400449c0c0c0448031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 373453794 1250 373452544 373452571
    0x9060306040f230108030403150b1201020f09010e040e07062a0f0b09060412050705120c01090c09090506010308070503120c0309070f140f01050d020d060e060d0b040b 73
    0x401510100d8803c80c224104880903036100c0d000720390340d103104240500b2003007008509062030355403082015065001c0500707002e910f481428100c0c0e224480c0e040800520304001f0740d1940c400d140e0f0003030b10750442c0c0c803d180041c984202031105401c0921913200680c5602000d4081541040e02c01c3c0c558290038400c0c00c0e84036000104d03103040600c00b40050b16800d842030301c1500000303426050081c1c0d0480003400344089a0488400c0c00001440081c0d130707800048807400d003140c41e0704403400c1140c10400c142502d42003039480001c8550401d00190701540003217200e240f4000700b41e610b50899408a900c02c03c0c00400603480300e001800071801d01c4003d010414801e00c222850400060f40e410034407141603404005552010041c04107030002030000d48041c0202c00039078920036161600702003c8407004000d4500410081c041100140d1080003110342c4001942c2e801d658580840c20440d005200390b200340341c106403400300070a40520342002802d0702c0301d8201950b00313920f0325162540c41c0c0d1590040d1492006010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 373455044 1250 373453794 373453811
    0x14070f0f031818051e070305070207240305180307020f040216050a05010b0d0201140f070b0f06130b0102031c0f060b030f0a0605060301090e01060f090b01020706050a050906030604 79
    0xb1000d0140024220402140940c08107004004050301c001512070001c003410101e80607101e40041c86091741c404e00c2458045110f0715802c1042e800c12103541c000d980e00048840440b10a88043c850361200c1c000c07a940c1c204205d50302e43e10f00c002206220944141070750001c000480262401d840c80411008000b4401840d042c0700e008582016000e00508440c01d0300039004400c113100080c840d0700661281030304c0c507200305140341d40024828a20a01d40c10030703000d000300700c821241600c8000e9a450682c04141581070341406d580032100150110340300d0344200340014545900404500602c06815010f030015800c0014291100140b02c41e036200c0604840c1d43e90704000200700759802200c0080440d076540f140c1d24100310740b101d22082c80081056507000d040c144200b005884000440341100c94145000500f10701e00c0d1a02800340800b1340c00010f50055494003c5210106903003c00a0304a09800f112800760b039504090360940518a146000704405104c9400a414490b0080d0b91042004100203200311 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 373456294 1250 373455044 373455077
    0x4060c110120060f0f090705090a0902090702151e150d080d0b01030e1507050304060b09040b0106120501060219050312010e040203060f090a0807061b02010c14070f0f03 74
    0xb4900300d0150721640310304140003031003100b81000303500081140c81d4600a440d000455503503c0c44a84a0140900d981e1070025800e50850340c841030740c0542c000c080d86030b241043c800c002e56585000741400c44100c5080301044461070203c8a0700012114030103690029070300c01501182004100c00002c0d04624071002d544c000030008030003000321007a10325000a2801000c000141150401c405507038041e40001c03240300281d0031410205e0b030311441610704283d41b942d542c134240c006071162203d01904003200c203062000304514092114140d6000342e881340b00045403210000f082d100f0078490b5074056000b0341c0d11441c3c806500c0d000008814094012240b070b001120006802c158000d80c4082654041c3c0340600c000c41c94240301ca00e4001c1390001410000d400e000300000d4480b07441a000501f4a00c1c00502d403410000603400c46164401c03402c11200110702c00f000f0180c040d008a254000000302840d110348010351000050b9906507420041000078115640d4600c800481000e00941c140803a0110550300c82c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 373457544 1250 373456294 373456337
    0x524090f090a0c2402030708070f030c0c080a0210080f010e0c0f0d1b0203070503121003051b130c02061b0f031f050604120f080d0e01060e01080304060c1101 69
    0x5003024078070101c1300c4030084032401d42c0d0225840114115002000a4000f040c2c0740e2098916007504003965035001616490705403180c2290304402484500003280c00156000c000c10000c1003680250340001c1455040c400c11a2240011079100c50302c0c01d6210014890101c280c41429403203200180d11501d041180e90070000d42d42c118401450300c142d182c0804038400142a1500b0b4107000c603d0009504200c02a2b40d456281d015103a0b10905001c007420010b20741c1400131220500850304a41039961040b8180c8a40c0910b901c0d020489000b034000b42c1c001014240d5611500040d10340c60ba01a0007181c4070765020004611841081d8036030344a00b40640203c0c03c00c1340000314055002da14040401b00e02c0d0801c030740d040380816480b1520809080c80700f0407900400b40c0154a40a910110b0604100050315000d449401840c040580a13403070282d0b03a284c903110550224068030312800e40e210081c3e0ba0380c4003081c1e82c0e01c00c0e4000c440000da41c0e80700d890f0008036608411a294081410880a00c42054200b11400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 373458794 1250 373457544 373457549
    0x33906160f05160303090618091b0801051002030d090f0b090f061b0711030a08030a06080c0f010e011101090f230109020109050609030102040b0c010524090f090a0c 72
    0x74030300c141080040140c00c025030140c405919030a8103d191554038003404983c0c040c070800c0b00344a100134a070100c5000e1880018050a9a01820021203036044040e0a0890b0391500841c0800c4081300041020324129030602c11541d00d40c4d00441c030744018002c8003000780c20320340005c5610400c620610710018000e268010b104a41c40001491000354080c400b80c6041e0014001d01412646041e0081e41c00c00301c2001c90381c42d19001a0480c1406500001080c0741240d21040540112000310601c0364400154110108071040c1100701c80c5039030b10f03110402c04005012904d07103020900c0c50180c0441540540341c11001305207400000111801240c6400c4081005440200e440030306800507813a030203030703500c40124279503503054002c1011060030b80c0041c1140400740200c502c9580c0104000700181e07070075011900688064640903440b680f074120450f001c0c07c4103a40007108410198891010000c1640b61f8550a030740050510061f07494000410300182006440c03044980503404210001c90044c031100e000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 373460044 1250 373458794 373458803
    0x6030614070206071e08190507050c0106051503010302210307050307020907080702060403120e190b0708070909020a03021912392a0203390616 63
    0x203840c0342141e8000c0c202000182494184401e0308a007041e10403103c41c1440101d40241448403194494002242c0c5912121305204100781c100020015034070b500201800340e406401009210094a4a040000b15042054600003141041c4010009480c1100888109100201a03201201c03201c444140c1190301c03c080039102030b40005078100840c240000126400071151811480318108400b000307446000283c4044c04101c00b9405e0080400515445401c10141d1038040f0303640c601c80c6406580401c0340c4110305039000043d05000400440c0103051086c425102541d4a108042c1040504002500000c0110003099401d020010500c12990354480f040e0f0650346070101c018445503180d405039145c1002c80c1c280491300c034001214011881d169003040094030804080514807800c0125280001c0c2c0754400d050082c803010b0380c140c4000e101c141c070308250700950546d400300382042c03040b4454540e11f001092510381a041c890605c144400340440c03054500902092511441c1c806441c1148441035041c0c1d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 373461294 1250 373460044 373460081
    0xd0206130603060f0e0601120c020c0a08070510050306060714011103010611010509010c05121e16020c03010501150809010b0a1e0909230a06060e070e041a0d06060306 73
    0x101410f044502c160080650768040b00c0b42e454406d000030140081d6080030701e01c55850702d92003a501d5009001b8500f000c2d40c0503000c0410f80d5a00c5e944c42d660f42800388100c600542e100c650403468070744540c00301c910a503800b8105514010060760303400040714003d800049036550300c158840c2090412002907000700925a10444c4145400301070343d08492024201c4001d980c500700c6a845829000b000b55400305201c005020039079038840100c60542420441c60041a040c50000c000786108001e4100c40050311a9084650360100d40341407508a0300280180440b170800c0f0300700038010b907200307207a4540d0150102d800818072a80c24001f01d03a140c0141c0c0c000403058560300340d15070041da416244a01c01407205c3e1800340300c158030648880034480300e48000d1664141151f10b080380504800c006242c00154040810001595151040a40c014041c4c6100d80040c0c1c4102070454a80360a004400f00c07143c00c9041c7c0c01030004500104101d551150004072659074481d9800400704000f4803401c6d1202c00c940840c04c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 373462544 1250 373461294 373461299
    0x307080a0b0910050f060705060a0e06090a0c03080a030b0316090b0103090804050411070b0c0d0c020303160809160801050103031404030506010e1e07030b100f05090d020613060306 79
    0x1800c0d0751140401c1c90107070300b2000410203880c0840a2240031518103035920302c800504000032030140c2c426071502401c1c0f4440c013000d00c0355154107588101d0ba800310120644580761a60f08010b0b4a40d08500400382060380c490100307101145070740000780200c650390300300040c0c00b801c000c002c02d08000c0c0c000c248070001450101c04101d0b10445008a203600002407800b000003401540c2c8651081c0140d0261601944d42ca03079000003098407040440b0b1515412000c28080c51400841d0402594444029258411b0510b10019141c230300000599015051040c0c03101d0900d8000501221100d40050071010316104e5100e101200d200b106040704003411800001081035811800c5c007420402d0404000b040c0d15004100c00c0010440204906041d031303490900c1d03a021b80e151003c0d04042c00e0255810000010f4240090103410b03a0180d02603001120191403000801040c9001903c0c0c0c008590007250110314104010411843e1118800600600c028421030421108003000740340918a5080480884e5403618203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 373463794 1250 373462544 373462561
    0x40b100801090b04060f201608030c03011e0b030612120705070f050303040f09020a020a080d020a02010507020c01020a0327030b07091e090c0c02030d05070b0a0203091c090b030708 79
    0x1d6003007105500d181030007180c103246101d0800503100080001c01d0100031540c007018541c0110a10748c00782c1c0140c0c18944a0800c10f4081c01c0030b0f0300a10454409800410340d030200c103095449927908403220601d1440c29680d0700d405211840d64100c840780707400d02912074031120f503441160103051420f000e000108400d5040c107004901052440d044140700380c0c0148010880c1d102c1c0c588150003620b543c8400962203200340319007030345402460b000084c411400420507002180302035014101c2800b10703070f001380850307240d60b4011303a15030480170f403000c0c0140c00c400c0e400404240034100c1583c000120b070580f210000041c2c0c0403d5281e00d1507420440740303100d80000744074840380d010900300007810360b0f48001e0500b65820003e00041d0002071040d107a004e0b446290100c0501d010b5200608550717005001d6a4260f500c00400130324651101404840029148001c43d00d1083c0794401c1d43e00c1500034070010101122500c4500b08c0140c2600144001c1052003400852000c1b0520040c502500306900e5148903814070508 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 373465044 1250 373463794 373463801
    0x30a0e090603010e0c0d080f0d23040809150d09082d03040b06120706020c041401034106011a03070807050a09030807050d03061d040b100801090b0406 66
    0x40710312030ba04003103018407441d001265040b540b5000b110f020740c1030038280c13400b60b030f9030301500000901c070701030202e0070107801e140035004404c40800b02c40320300c2e01070b0703109844c1102442c1084da0050144c6800307002d989040c0c2413001c0c8103c2c040d21a02c10203070505024641d060196100114111205800450041c07661103454002e003030303c01d42820b450305c280c6007458414003040c003005001070b28224801c40419081c2c1c40d02c82e86840c4e0280080b054907510754403100069603900402030344600031481c20b540103080c10401c40040381038a030700402000100a900f0b841c02e0384605071402040e0200c400c0985846c0c45144200403488211040f0f018180640c502a0002c940209026051041c004c0400c10840155841101d26034090355a003400d07a20384814140c2120a41e0540d040103000d10800200341060000000714403c169456982c00e0101b0341d00c03030700c0341c0c420b0844c05405224032030103c4c80468002201c0149141d88000001c82c5c0d0106155100886801d5410342001582c0034090f071010b11081c40010700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 373466294 1250 373465044 373465051
    0x40311030f060705090609040b1807020d090f0e070203091206070212070b040209070519050415020307031b1b17010e0c0f091b030f010f1d010902031008030a0e09 71
    0x600803d01d02000b0292503841100e407198450100012003143c5951107600005090102801e0018203450b101009880c0790300030754044015200303003115544041e01c101e5400c0161501240d54001d1240b825444942058001e055581580010300400005480e40e440343c000d03001c20a4024070250901e81400390822005814a42c2482c1003006400d0216855100240c1c100303074141d900440e55580c00e10b0407902e6009040101c00002e1400d40110302a652240142080d1240c86c1c51125451010780d0040c0d030707070740700781c0303600501003841d2030b0350301d40c110f02c50300c9006a68500030001d1030360003642422f81d9107080c16940c03c8a02060074800d66141000d80074411000030082032001031054024420000307081c01d004004140c482d001780c40c0080d0401d0084084040200303420401136480b4101140b8415001d00d090007024404512110001070030318074a00345802c50704000c100702c05241d080680381030196000505020f071070141d1500000740c44e84200000d02c42014940da84283c040c6903c42040710900717018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 373467544 1250 373466294 373466323
    0x507080307080a1220070309080105090d0905090106080117010e01060e0a0b0901030b19090218161701150c0f060b0f0f0603070309140a0c060f0f230405030304031103 73
    0x70460f10701c4c942c01780c0051000e00340007109a50702c55010340f6048841c400316805c11162035003020140008000c00046111403658152100980c0c02e4881e018080804401d100d030310700203a07241c0c00400001405001c0012000800b100105880406401d201e0a50705c8a42c49082d403510940704006c03000c80c491292040e1080101d580000d903500d0b40d140d41c840284054040811401c3c600c0340d2608403645a03021410320b82e8050003801d40c25142c2c1c0881600d01b9011541c50f01951061040d0662407407045844c031b100c1480b503440506003070b400c0c03202c917206400f24400ca080070310140c0e03c000c5c004582c01c40104070419100c1e01000c01d1440a40e4280300103071485d5a00d4500507854150a00c4060b9240701c20f9075800b0038149400600c0350a0b07404c101d1410b9418141d08a2140101d219800030b11420300241c2c02602e60544800101c0000d176002141c3d501c2e4190b1071a000603100c5038002c040300511011500800034a6899036080a44a0300000d0841e40590700440c0c1c0c5514010031000c1a0a0a01842607005260b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 373468794 1250 373467544 373467551
    0x803130309050f0d020402031905090105160f02061f03050f0606150a090b031b030106020601060f0c0209040f02041b05030a0c0c03050d02090a03061a010207091a04090507080307080a12 81
    0x40f030003c100c2504404030001c2c8256000720018820104441c02580361f800c1000c814011410b24642c0107009150580d501001001c0005d50032900034012000c400c07583d035180c5e000300841caea60b031140385000301d0601c1d0701144210002080000401c80030004820000700d40300190825042c00c178104620120320944282c00408144001c180750303034101071303644c04690344200310654a40d103140d81b800103940c50694182007540007000210b0b141d9400240326041c0d6096407646506080f20034026a1645040d20000303503c0b03100c550002c1c0008181050a07001d091002d071001c05d070104400481000080c10b41c0d0400300040d404404c02c0f0070300407940180380500c03600342844400302400d600d00030300078801c091001c0c2149400152400c40c41d22040c54040003141c001d20100325840d1007992440a820f50310442e28010304c00c449001c81d0709440d17032050041220702d03c00b40c041d40344166401e1001400440005640c240200b0744009030b940760500080104030310400c0302c00c2e03440c410200d002e41021007112403c3d550618 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 373470044 1250 373468794 373468819
    0x80c0c030714101103040306061e0b09060a05070302012a180e0612030d0609060608061801090e0307060c02160609080c04020c031e0d0b040b030607051303080313030905 74
    0x4443c007094440d10700e94900202424090366040e480c6100725440103001078a040000100c1914490b00040e000e60342101500c0406da880455250b24011003034515031001c0100862440580220018510a40f190002084001b240300401c1c051042d403000e1034040140c0442082466a0710200c030039184a1780034a0542d0315414443c4042030150010041401010000700110b2202010410b40c0d40c4441e02e03048c00c3c00440d42703621003480589401e10484010071016408034080f8070300300300c04a06000000c0260380c03045c0c0c6410f40320000341142d400340900034007080120002241e024000d840150788250001c1880d460412159558154140d02c00e10800c000c81c1014468240041844002c51208881c05a2130702400b004190941c41043d1030003500000c0c90204100d0f8000050150001c0003002c0c404110940012090106645800010b954036802a90024540c58000c401400c420f1003240c107200c402030340300d5885107000e5105640f00c1c1d20308482921542c0805600101502c0a00070640f20000080c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 373471294 1250 373470044 373470049
    0x4050601050a0509190914030a0e0907020f0a080a050f030a200a080114060c100603110307061b11030613060501050d0b0a0507030b04150e07031401090b010c080c0c030714 75
    0x1e03504003045d400e5114600d5100b8005130403096030b4540c005030103803680c603481808040d0120b010b1030f004034011380440700060b85041c0049a2a07485040041c05402c56030811f03139030401580c2c045007c6005005044c080c211049401300c01442c842c00701c4280000e0000e0301141002040106425450f0443c4c0c002c101414072140d02003015811240081c644c0108540b43d20001800340c003680d0320310302c200c1c0b140c4240010403102580004084a001d061182c203002030316020f0680300c9030745004010100782008443d40c500a9403d81c0b420340c00340a040d40c20041e1403040300007400e0403416194a0030b81144121440180101446401d0046c107003141c0740030b09400950358a940b600310042103415401d84e1080000c40e814006d401804800000410400c005072503d131405514150724012130342c0c942c01c1307500011315840c041e1244550b9081c0c2e12180e07411a030710740522040a040e00241c1c4074100010300442c0c7d40001c40003005404840052400380c43c030002800705040c941b06180e40030f400b941e00c13461031040311074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 373472544 1250 373471294 373471321
    0x3031c02030921071e0803342a0b10181e020703090807060210060f0501081303031b050d0e061b0904090503070305030f01140102072c04050601050a0509 67
    0x440c1e1042d40700015075504a800f017400c1512901c0540802c200200b00002c800411182da02c14010141c41e81d250b0706d40307803070248124900d0b140682010400410340521100240e0b0202081c0030f07101c201201c0d00000c03e07552800ca0340001d44064032081e9850f04144404c00303205501d400c074002c5040d4100700d0000c00c01c80c40f0740000d06411210010981c001751502c249441171444402500f545000c40e0348482c2c2e039401c0250740d510319401d0108018680203000c644032031140302c120211107059507050002d031140403a83c403070703001807503001c3302450781d202c1448001d10700342c1841c10b03155401074850948880700400508240c44009540141d00d400460400500c807a01c800d00f465003101a010301a2200754940128004204019000c0e1a40c40041525010180d000000718130820058076588c08990307a42000039001010000e4190140e0081c00050021281d00f030210882d8002441d002000800c00e059454274050782602c1c2595150069070050040c1e0528590301030081809440c945014903042c1d40700b00c1c84 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 373473794 1250 373472544 373472557
    0x601140a0b0d02090307060815032a0303040e0a091104020a092601021909050d030206061e0d0501200427020405030d090801150e1503031c02030921 65
    0x88040c08100821495a0340d81031341c081000160840c1c0c20140c0710303d00074090b40403c544600a400c801141041642004100c400100c500d10083d00e1745c16101c409600218813010301c41c0394243c03005110001d040d290610036030740224144200080d130100c070760400d081e030202620402070260740100401444164840032000440d08250300d5050040d81505012801c0e83c0040a405415030012079007a02ca440d107040110140546c03901c4a03000785a60300d080c440700714020a0003030003580221001a446007041c2c00424007200402c2e2150300c0d416103490024140b01000c02049d41d2580d51503006049407400748891030302003141840c1540c1010310304015500c140c03101e00c200d6007050000121803104402c1e9501a10041c040050030f17100081c541d5400240fa0020380e1180482e2503080000782c01d84213001c0b900340d1b41034964450b0030000a554051b8100c103209031001e112601480304003c2c140c40220140094903028008a102503170340e041180a442c42d005181d55200c0b81d06612024410f0701070400421600c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 373475044 1250 373473794 373473809
    0xe130509061512070b13080708030f0c070e090d020609010618110405090c03160507030509010f0e031f0e0601080304030201260a05010302040f0e0d110c040903030e0601140a 76
    0x103010002404183e21100502e040d40f150700caa1440454960152009098841d000075600c05000740c2d281c400c2940c0300b20070300c9001c00b01d400801100e890b590b031503001401200110b074101e944141d034034003680701d0005085801c40c1154101c41c28140019a06003e82c0b6000305c6520000d00c200d9081403007408110003505030319151076544100d0741403500e400c00c042d20700070322005040800d84d04d050028a41c0c1d9a20466051107080c24110440000d00d01170340030795202c681c06641e170b0740c200501d000040d900106200c0d070500c1840801500040d0595040241c1c0c240035000208002c04242c500035520103403101d0b215100c00541003a4010300c0040000000c1c2c40460750246020a2a050042104120480d084201d40391604403141000041c803465004181224800d441c100440620300c3d01c0e06045520f01001c0c584581c1201905261a501c130f0710700c0c900000a41030580f104090150001402c8584018080f00482c2c0c9800441c10401c0d002e1141c10300601b11a20710864408901d80050b02c00100b6000b0301d003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 373476294 1250 373475044 373475071
    0x30a2306041218031209081504030e04020c030d05011502240c130f030305090a05092511030c0109060b010507331a040c09030b01050d0f120e13050906 66
    0x31403240d20040703c00c000c640000d0501a040d070b041c0f50080c0b061110b4001e9040d2449500c01e940507100041104512454041e81d415020625004c20880a5800080c80c00054130040c8903540c007a504503c01d481c001d00c1c0c0312140c1003802c1d0300b03054040c2c18582c4504468140039541c40361114145014855141c0c040105d2500340d545201c0358442c281c442005811294040180070004420183c10000501c0411000c8030305084c1c0c203070b55408200c404203081b0344242c01c655800c12242e6198030700e000301304002840d50824001480d0031500151540e0401401900140c1d140e1310b66406015840c4124035940b00d088c40c01516260741a11103010f100c5892250388a0105043c0c4d8520884c0c000034039042c1401c10b5400d050080d0b500c03c55540c1200c012903044140f0a038506111800202d000e0241942205c0e40f20f464090315070300e82820003d94080030141a81d800340c1c102c401d8030000308812401210b0300e500c0c5e1030b81c1c1c81e907110840502182d80c04031036034001e1036841c02082c800104000220b4907400f030500d050b80d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 373477544 1250 373476294 373476317
    0xa050a150603140708070e070507060902010203271309020907050a0c23151005010c110415080606010c030e0d0f02040e150901152102030a23060412 65
    0x200c0050100342c1c8080c2c610460303880310092221020449a084915000c00c84000075103030300d074584181d40c055038030402040b0108405000200d06811298a0a0050060341d0501d06403a003014a40808a4a031140510300c002d248000c900e000c0c90600f0b00d01c2c500e21010840900c3c690f000c035070301490190003a0203201d000f16100c401e41e0b2141e1400388056901aa408c00c082084e024411402c1a0b05440c608090041c2e0388a4a017440c07040030103601c107603080e504000010707203410015180c0040d50303030050f142d0030300d10780d0795403816241c5020f01c00840482c45c00d803940ca1490b01c0340b5141400e40c05441141000409401d18000c65407200003000d4421040b218a51325078468902510f151541480c0207400c2400c00036a0050001c3c0886d141c2031404c1202e4104d90b541d505d2900c405e080b20401c80a0980c078845c004003d010000310309102c0c1180c2510200e191179130107865000680f910303140d0030b0119814031000501c3c802000c203e29030020b008140c90000c142a04103a80d40606036501d61044600708510300f80070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 373478794 1250 373477544 373477583
    0xb0f03040c09090f06140405061f080105010b04050a0b030f0a0f021e0d0614030d05130b0708040302040606170601031a041b0801120309090b130e0c120a050a 69
    0x4100040a4a020030802d20f0080c1c82d0481040ea40400103403002407500d44401000107450064503c203540c02809440d1559070400202c031050301220034040440000d203804180800e00f4803585010304030f40350842380c50300d190004026848a060700588040d01d8280244107501c840c460078207800c81803000020611156010b0820000c0c000c0c07050450402804800030010501040b00034210101c850206114482d01c5140701d2015884078040c080d0150b110000c012012885400900007070200c00040b0700701d855440c1d02d030b910190000142500c0d100c00018040085142c940f1800c0000c282608009014180b41160802200001000203040c140c8810040440c1000300101070300d5100c0080c02080180ca40104ac0c081e040325100010380414000e40020a401ca00415031300301c0b199041d0b40f40b80040e82402c2845010700003181219810083c3c00600201d00c0005024552500d140c520040409030041d000b040120031003980111442c1d000390b054a0007044002ca1206021070300050300c0c3c250b6500745a030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 373480044 1250 373478794 373478813
    0x9032d090d03090f08150c07140f032106030d11190b010906060318111314060109050415090b0613081011031302090a0905011109031002040b0f0304 65
    0x20200e500003008201c1c4010182c210b10214140c1c2d800c0c00500d0309080d00e41c1e41c1d003591040f0324011004c14400490001c2d02c136150442c020020188101c2d50a4660b2200c00f0402d0318040c0041c2140d4050313040032488048c415800300b500040d0507121242040181000c0012a85071980103034524200500c16800d00110007041000150b442d101c1c40c442441c2020714241607034110400c3c041d110b4001e040c2200052801d102e405896074cc0000c003100010105000d6440d003904078800511940c10190010190182000780c1c82248202c0d4482041001c840c60407030001405c0c140c807900b0540c8140e10389086070380c004074000c1c05036043c0c0f40292400101c0076090300000f03c2d1030158075102c1e01503078030045001c600f040010640003170a403d401d909000a600c814100c80d9240800c4800091244c04440c12320098902404415003100d43d8440000d04105203845031420345c2c003030814442041d0000540300c42141000c104048400001c04021400c0600300207203034801d84101c8014501c40321012010505001f164403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 373481294 1250 373480044 373480057
    0x7060903030b0915040f0605060313030c050a080a2303011a040f1401081b0304030507020402070b0a0b1023030402011e030605040509160501030515030f0601090509032d 74
    0x140341d4560341ca88034403005290000b0500040c0071703074182a4001420f5071300f0300841e419036000030869400c603a0b82c1c1200c2a2503045000c1e080d420010f80c0c412407004520140720b0800002d010306885961142e80f01c5000c0d02071a0104541c0403100c100044031580181da85040c1c0741900c3c40206400258406108850b5440c0540e81200808c0d1100c41c40c00a0301080c60b40f20a08025402c0e00c40c61071725a5800e1076003064035000304106101d00c1e01000005c00280c031030402044214401032005013440e1454440c0c4001100407101c40340320070381d5491920b00d14079250128403132210321480e0051820580c1c00e40c1c40d42c41005507440301c82100c0d000c0003081c116030003590340010145080d41c851440c035005100003801340c06540b040e41d009600e0403011601114020a0031002d4401c2e02400119003490400110000e101c02840041510002503000c0303440c0e60709110755180c075885940200b140e54141103443c001c80e44054040e0340541c4c0304100340040c06440c0300b15000300d00c81d0780c2c441120002211019840c1d51007501c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 373482544 1250 373481294 373481299
    0x21813061d060c0301080106230d020409150906061e15170405010f110c030a08041e0f0218040b07050703090f08030319150308090a0906060c0308060f0607060903030b 73
    0x1820801da0b0f5903044051412541448000d0103190750b40c482400c0501d00d60700320200c40820501049605050800440c4501440503000040c40c81c51515001071508105200c580b80300d40704d40103502888210300070140034003007400c0f03e0401203800b2a4150f400706107621172100d2443c03800c65040c2c041401034009401440a0b4950f10304c0b540f0382854810700034085855098642441c041c0c0b0901c401d4030320010789100c0150b14004500d80302c1191401c1e11601402442141c41c0907450346075205108a12a25440e20791052281142240b124410070070317003941209000c180c200d401000c200c04620090405600414a810001d41d900401d00b8122101c490b40d40140c00c0014403110001044000040218855100701e506c900c0d0404d09a00c08100344c1c0c61100b4483c0000e48450b80600106a8000062540d81001420030f555240c1d6a00e038a415a2081e50207580400c075580c03440c0040c190001022988503e00b1210007400c00c1101002843c2e500030b024000d0095030b0340d1520303407003014041c2c0c0c49401d040e82c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 373483794 1250 373482544 373482553
    0x50f0d020409030c1a131b0b0a03200708070b041b0f030213060803030a020f091e01110a0b01170f070f0510090f15050f120103021813061d 61
    0xb0b401c000d481145042030413a00030600c9a101e4052080d0703404098081d00d0742c01121102020b09403103162807030b00c2490542201c00118500001d400040324018815803100b40c401150724031782c0f059800488565507041c4482d08504008000001d800b400890b21455442250b081140d110790401c0d00f002c0414075280c0b8500b022040740452502940046401100d208490540150320380a81c0003055840d43e22411030954801d202240c00080c2c2900a000f40c7c000c1e0302242c504200100000940d2203860b14150385c0381d103a0300304094540f964444811128400c2c50f00007003d031042590345c0d060f100b540500c1030085000925400713040340d010174400010012039400c112030352030b0b0b110300c1c016580608030703c241d43c030640800c081000d0352401400440121000461030b035041c00c0c0b40c118030381c00c00045c80c5598810440200250a03000c4445000707000014003200031141190704510500011030004452110000602000c001d120010180b40054095000d0404500010780c3d400c01c4c85001c250042d0304e0301c0d5008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 373485044 1250 373483794 373483811
    0x4110901111f0207110d021f050d02120a0606020f06061306030b10060e032d0114130203100207020d020111012d050604050402060403031110020412030f18050f0d0204 73
    0x4a070064139005014110303003250090010b08028041103c0c040c000e406c181d12010728585507000c014006c42c7c00320036040c02440c100400b0101c0040b0780c440c401c00c024140c04c0030140140558544240301c06005280014410303003011105c0240e40b40030003000d03d81304a42d111a003a4040c20300c0d0b0050070045610031403040390b50601803120000100300c2d0140c0c1d0009000454905c8207482c00180d1000316940c031545292a07007180e915865203079468110070203895901c91070700350a00c104690069208210031924026003001c244105030800c491200c5403401c15005005510141c0d0382c0000300004280d090034103c5038070046210f44d50241104480d5422a500d08507400d9810960140782c0090048d200401080240e0b10b02c0c08020481d00c003510007940006042c003007440041c0c09003950810328100041118000c41412410030300382d0f400342d0082443d40c03204142e03c00826800601d0258130100d642801e59079410b070038a400200481c18803038284108104c0e00c5880050700d81180201700c1075000740c0140304548 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 373486294 1250 373485044 373485103
    0x20a180303020309040f0204051e030c062212031b06140c0a08010801140c0d09020306010303050c0d030506010e1306030c03080702030601060503040209041217041506050411090111 79
    0x130041203003240694205840e80c1c004500da48212016540e0040c07801c0002c01c503a48c00c1c0c6e03000c80521480c8075050321511b1349540f00381e520074029151b003821881c00c084108150528540d56031149600c0300364084025000b00d40000c0d001061800b0b900041035001c40e0f600b03203500340f400160400b50000701c851114001401002c0c1e038060000d00001c20360b522005c00740d90366a40c40500b01c8101e81d01c03119840603540040341c04201004000c10300780c043d0007008510702401d80c00003402d00000703902c1200458070004144180c00c01c18444081400b4041c2020842ca1900c103002824182e150303202e10348100c40e0310501c15221103156120401560304900c002e40c0d020381700d240c8034060b64840c2c5400d0f03129110340000000c01314816000c4901c1181e0141c072810050f100c035500d2004102c032561095090210601226005011181c815881140100310b20310381210710340410350072200e080c0c00440c055400d0103890907e1513910b00c100d07481e009080ca002c009440c1c00030070090800c900c80090824150910149020300c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 373487544 1250 373486294 373486297
    0x120e1f02010c0905090703021b0d0801050f04050708010b0906040305010f0b0411250c1805150406050108041412030103080903100207020d12050d020d0501150f0203040306020a1803030203 82
    0x249a68008010815298900340d40b2005980700e01070b441020130001964241c4640c01915928540803c019030320405000350718280200e0105510000326200010032441c1b900410f0341d64001c0e400e4504100c11700702020018407801050054181c041c1001800b244144c4854080300c000f136400100801458440070750900245c0b10507081a0320072401e10102500109a15084031412140010300140c2a07101546031100420700107410342e2804500900059888120000d40c000d014a106000615251203101021030006003400e02d80942d10341181441181d81201c2084d0700075801c850740410010400340c40f00e2401e07844080c542051140807000004010195010b001010012420381d500002c80c54070300c1040b800381c024042d601003c030017409808116886200c00802100d441d0181c9040c0c0d84851403000e0364015100b5480c250703954801041410103405502c001001146070002c01c0900750000255030307000c1da000191502e42e00092302d000d4a8003503802610405200502840d5050b52420043d459 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 373488794 1250 373487544 373487599
    0x9060c0c0f030607050a03090213020d0f0501080f03070b0c0903011d0708120703031d071805060a0501051b011b08241c0503070c1710051003120e 64
    0x1900301810201c0491a002c070f5083e100e60829a03d850810554007000c9024003c10710050340c10a00c041e0b0001c0c940304190005141c240c91071032001c40d281c0e0003821000212141607020b040d86410021214804d00c2021003120071254000c40c2241703403a15903007814241c0c0d2042e00a0030740d0541c60312072140c1550403961200b004006445055540311651107a80701c1d100d4445606202d480c0608110b0080024000da002601d0400700d01001c0880200101c4070601d030410a4200c0644041c00e40251034842100c0d000d001e5000c5000d96010301c00c1440c0c180064418061038814810450580f140d0040b215001d60010b600450429003040f00d0f0400484054280441a034403a80c02100c2c2d05000700c2000060b0918050580e005000e01d40407004c409e01d403483c1051900c8007200c403808100325a10101d04e5482043c070190006002c0384080c4c900c5055514a0302000c1041d00001505000c200001340c55013501403011640c00448040410307001f10022111040c6aa000e242e122106c45c3c0140e0007071140c421040d10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 373490044 1250 373488794 373488799
    0x4050610050901060f18170d0c020a0509040533090d0e1207050a08010c0314010608060411070803130309050105070213020f1603020c040b0114070b04020609060c0c 72
    0x256848160412118000d14000e0755000400c0c1c1004101d05803103100400c145056038900246a4014036000c0500301c84c40d41d0251507950480005807030318103014131500004043c40d041007128180a680440d034480d800c0c1c03140710311650128000a003400020b11640003141c25031003005c001905001a8000000850300c1004040041e880005080a038005140e01c1050b01e039481d91180710382500c007082160210484c10b040c40b809500400030301d64030f41402043c0685203142c0003080062845800404441618078481980303002c2c90010000380b03800a060301c0d041001950003140008120a403c01e1a00c18060300030203480001003040004540c0c4c00e00300c450103109030365401e01e095a0b0001142d55001d0110040d50041d090700b0414666911075000b04018491003500c2c0b030406400b0b14600411000c015011340142e00100c44146036032600303201d4030400e0300702400c200d0f041e40d8150701c01500c0c1707014031000149040d000302c000c60195540d4006403500640010311302d030b5682c031020180f240c540e03001e20340300c60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 373491294 1250 373490044 373490053
    0x506071710080c0f1c03020c120c010c17070b01030305091203210405160305030a02060603070f030219090608100f0209030303040b0c090a060e011d010e060912030c060405 75
    0x18200d5045150501c21036482000070544120741e0f208110400f43c00b582660361010b01c07030b0031000c8003803450280008843e001c0d8024029104403101405101810030350b04191b1600020f003200d00aa8114120450841d0424001550343c8500c0c02818668818030300c0140070803060200000405a12000030300d1450005d64014183c11524040c2c80d80da8000c20340901350388201d0795503400301022211851a4000d010b0402c41c1c0f039040d0140a130400302c450302c1d0802d0305c0c280c0001500c0610f00d40c0400045410903030030b41c02014180d183c120240342c0320a0500000348600c81c80040780e00203003201175039413003d0203c0010030402507039161074480e51012202c0c8142405403c04403100f0740d80c5600e04c2a2040820040c01071465540c607079403079a04c0d115000b40803c620510911090ba40d940751805e1040260400d500d13181400341802d000034102200e4520101a038000355840e1441c5030740d1064440110300d100f40c40d2291180c803124005802075004031201c035154403010504030044034001400e40d000314060740654 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 373492544 1250 373491294 373491301
    0x180c01090605030c07170d0209090906040305040521010606030c02100213050f011e0807031d071401030b1c060c1e0815060307020a120302131a0705060717 68
    0x1912806800c1c4900004240c1c00c0c070000e48003804040082801d148030742e103c8040c0b08580c0420000a070801c503202e920340c0740d001c141d005080c109215801d400c114610014966864159001811445075001e00d41c0600c04100780002c40c1c010f10711649168206c100002d01c1050b450f001d00030700500300a85084018400e20484080c2c02403180f0844003074060700324201981030b0410050025404ca0540007504204000e01c016841d01d008814036112100c265641150343e080021000f000c0d00c080782c1c1004906401404401c01c00c4c0b10000b80310701220000b41a003900b100b40d28005034002d0407900301041c3c01401d90212810101504518810550b216040411000c80070b240100c1d812248615000704902450802004450080341031700d40c060750310b10314428031010300d2002c205190802d41d1180d0142e03110341269030030001061591010101649800c40c20801c0c200406041103500388596840804541012429200b86400300d516032508801260b0b202c0c01c04000081c2041101d0314502c00300032006011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 373493794 1250 373492544 373492547
    0xd020607030b0d02040b01090e150f0406050306040204200a1110020301060906031e020414150c1e0a080a080708010609050609130905010f0207050c09070f050c1005180c01 75
    0x103590100d03202502c3c040400d0300310b6080c00020044100c3c614148920342c1000100fa95113403072403602c82c0c170070010041d4010310500b082c0b0404040b1b20a10521584c1005003c3c01561400280168000d030100c40120700341c2a035298021a14051480980804100181c3e01e40c0e4035170021141c505c0e500000040740ca0f003002c81020502280400e002d00710026031110400c1200c64440c1d00003144400c0c04080d0041d1240242000004a911641c0440095100c00c98211107510744103201c00f5502e40c030510050306d4581034900094860b02c1142c1201508200120781000f844001c1000380b54003544141103595403100014042c00078001242c1c0000050a00300020801c0c92088241104960018105a080c074002e28108180500340520070f00382155200081d40101d04240034140c01e2034070a400040e550741a50400301d042c40800103140d8010701724207087c040c11707580c0081d454440d81d02920b40281c4610380482100d041180c600c0640f00880d041c54140701c410080d022200366010010003c64444c061640300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 373495044 1250 373493794 373493801
    0x5300f0f10090b070f11070f030501200f1b010f14010b0702130b010203211e0408121801062c04050d0e1c11010e0a030b2409090d02060703 61
    0x62216443c64003103450740e07018941c5030112162070b040020900c5007500d10f15180100d035500a884001d0030f0721040003405400c1c4107401d106d40541d6901d007010f610756004841d0900c601d001403024408001403a00b20140101d03244011909200024030200e9803920080300074010b401141d508801c849000080d1200b1b0f80011115240e6014161210004407042030900800700f003020b150540c0401c1284014010082170201c0c0c4001c1400c454019074104501c600070314151101280f47c0e6101c2003020702000c9813403001510310020703440039050140d40d51185200e41c4008806060700c0190300b401000f02e1005c9080d038a000000d41a07101038160090612580780d04c03103500b0f90303003d04240c000a503501c1c940707489003101d00707025440508106140003104001050789810740c0350664000c0c01c0002441c9003580d03c541c1868011508807400d01c021815622803602c12000034100411440c8001c0181c10400a0542146c1c1c006500802d0300d1132624000d000c0c00e40b6a060180f800300107016020001d1005d0780240b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 373496294 1250 373495044 373495061
    0x60905130809120a0602041e03031215080d020d0e010f05090405150607150506010503070503071d0a08011d070e071d060c0309030d03022104050a0c120507060302030105300f0f10 78
    0x684108000c05914003260040041f44074403090f5240540012070400000c11223b103501c40164000c0c00140703541e25009100d4500040454100031601012458040d03002e029650310700c808480000d41e584841850788000a200b80050b90008000300d1003600b4401c081d864080c24041d841d4050050b660381d078004440c00c0c8011a004800703d81c080c000b140c059446004018411301c29000c80040800140c400500d180010ba0700c84101a911000303880c1117582c6c840c104c0d180da01c207c2e9000b40203160a00000c05416940242880c2c20054001e440d032121003408001007402450207000b840d0341e1468441a13541380c0c0d100401e0207000e4465510320400c0d82c0c0c424800c03615075050340f8200c1e080741c0341050071100c82c3d41070140c03003038806108002c4d40034040340740081c0c45d03001400426641c0f8400300a61820a040181691190062600c188010000c90300e4400c0655030800c0f0b000c4103d04903a000c4541c5151340b10040300e01c03aa282c4580b03040200607900021f001819802c64004544a40c0340300504802510207a6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 373497544 1250 373496294 373496297
    0xa060e010e090a0605180c030703051f200315090103150f0207050712050607030504051902013f0501031707052a04060905130809120a0602041e0303 65
    0x6000400c8031807501d0740300c0c41c0c00c944500140c40c0414695200e03002501c6064039840e810403601151032007a280304201d944101402640a041030f1843c5484032901c070903030684400040c1108141c481644000340d40210201400c8a000c0418011419003116458004079882c010701200c42541503a68602840d000d4103caa00c415540c060039081280f40c0045c1a4101c602640103400784002c0000640500c400c9019142400041490f43c265007486481e00360041e1910042c507141c0710911010a0700880d01d0700c0050100400d200c40c070700e600d1004807050082041201080c1c2c44510901210041030052070003522a142c16030780350603035296000c8040b14402e2200420301240c000c0c2c2d80001d28480d102914621b0301a0f0203a4000d4001000c5645031a04000081480601d03144400300c0240707414466400070300084e01007040b051800000302506001c03084400b802220740440d1903a9680c2e100c04041010030060f00079a219514140b030568081d40040c0a0b10207030346c0c10764161030140345401d81400102c82d090b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 373498794 1250 373497544 373497569
    0x16140d09030e0301150b4510020604230d030f0b061c110f0703020703050111122725090c201014060906010801121b050909070e0a06 58
    0x108040521140e020f40c4420803c06580860707e082c040c904401e40d04c59480500100d009001080c0003103503030024803800307144200c0e0000000c00708258005442a8803a510101d0504440004c4024401112070f00a80704031601c01d400603901400c4c0e06803c400680c00104105028201d0080c1c02c0080d9401410341030513003a100c1c2d482c107600903903c503040030358140182540d140c5404c0a600110703400380c0c1310002c19405a070044804004004d024850607400005440300c0c2030400d40e0b040010025464050b1445a083d43d4cc0001d0010b0b041002a074180e41c1d40e405011a039400298907042801821850742c60758800300b1410002950b13114a00903003030203445542c0d60300f0410424110a07031241c064400401020322402c4d01d02c881a058600c9191641140340034011070b41e00e009400c0001d0524020f259604018406d40100300715540d20780c210754544e40c0018050f0700c800120312400d00713104055000c942c3c0084241c040c03003181540440d01c04181c0d0482284410b480e51112196001e4445900c280b400b248030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 373500044 1250 373498794 373498799
    0x3030d1109061b0706140a051b07060c140106080c09040c0509040614060f060412140d0807120203010f12050a120509040c030501080616140d09030e030115 68
    0x20503600c845003410304144240d08004009010036602d402c10b40c8403004030700c0030840220303201804100307400040c800b038034010900491009042e4440d004030038400b070500c030004c03e00010226443e5080780050700d070a802c80340c100b90750b00310040c1549221a0b051f6452041b884880d41000b0041c041d0209030303080540100340e043c14030020301900c0d040c000c1041e0350b1601110f40101d440e5858141c0e00340134601688008c6105d40400a0720b400328070014040510522080124260984691050314116018419102000055400d107040c1013002411107000c1400b5401007401200d0f0801e89070307400303441290b40304940229500c0c20442203100c00e000f051611101d01c1c108004030107029403804003882c4030b5026110038400581c0da00115890b0300451401040303012410441070304040c0f01d00c66001c41146418061540340c045810313103400c3c3c003800c100403c1450b8000d20603110301505540d8180e81b14400083e94407414591003000810384000c046000802000c40640d0b9031070140075051003c8480c10102c0f407040d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 373501294 1250 373500044 373500067
    0x6130506060d111306051215011b05030a0f0203120a1a060c03030f06031504080918070e01110d050f030603010b120604050706090e070c03090503010207151404210306030b070f030b0303090303 84
    0xc00c2c2c000070300c0c1007208650800640442b0b2850141d1038610410085490303c002c0840548030490a11503032007154400d109070542c110001d05555000094007100044141f801e14030104101000d0048581088000803032650102000000358468519003924119030b44644042644909070b010329050341d446203202040204503050024514076000400c20b8107200f01a401412104408840130300114440348030000302c0d0f5802103040020300d05110041d040301035803504044d0003405985216020302074080005036043d1801d511aa0500c2070013401840448600005c241e174036101210101d501e4020241e00240503401203134208261440d021800c030807513649110807100c0c86d1010009a0402c18030f0343c0d001501e61002c0c801001d07400c0c0a81504c0e5148104200c00c40305480300c0400c20b40d0407a442c6c0b400c12022a0300c60001001c14420852030300c81c65401001d080b0b010b000031740c10103404045540207002d0000d41181d11210041d0b41500c0900081841e0010107460313005000382582c00d90030800c403880421 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 373502544 1250 373501294 373501321
    0xa0e0f070f1803060902010f14120a2d0e0303060a05060304051005010f0602011505061e0409061205010b030714040c03090804090603030809010506130506060d1113060512 75
    0x41c840d500e051401c0300707091402c049060300a5401601c055550710642815940c0c00070f0300c1040520315040c0030319442020034800c61184a524990f0301c9980010300480c1480c03503503411105010f1114150510a1400c08404c081201c0010b09130052442c684002c418181038048180ca11604008203103800b13803450701d800d101295000400c00c54040c041e4201d803c02203c003d104460292004c10000018582800400703403c4030205014a00761000c3c3c0d04042140340d580c070b011140302c075407407114250150341d0003c2000518015030304044045400c10b1004034810a03240a8410454001c400074060b4045801c20315494000360b00079060b03086010059500da41c01e11b17401c0540015021304d00000c50ba02c150702c6002140c3c1160304280040c0743c07501010414160b12150540c2c002d070010000b0006810a040010710755500c0d401001d00c42d546031030000306250340340000d03204050f0300d01c401400a510032480c0c6030100d900c1840d8000c045018400d0115409118406032203c0b50040a040a007545941d02442200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 373503794 1250 373502544 373502567
    0x609080d0c03120b03070303020607030c170610110d05130b030f0f220f030f0f02060a0f1d010605010f05070309180209060a0503151005030a1505060c0c0a0e0f07 71
    0x1d44d031210b031188040d49080100b0f100440c06030b40509403600701010000c059501024610f810001c1f603d8000d400000d60b9280b190304614100c4042900725107020043c3c1e13110844c0d0300640303043e008800e18410b0b00e0390030200070000002c1c0000c0001400352a90692155804199801d28050107080e0000d6440e5110b0000d0715008450300e50329150040001c0300c0480150450380c0304071800c408003a017034810143c02025040754040c05041240d80210003000c020b645000c020800c140440d100c6440d1004040320394041402231546980c0340c000030100b40f0019002e0304092044500150b8014098075074903201c2e034140c841c0070340d00d80e03904e5604615060124280c141030312001c00c8059420400074001d903403801d004080d9040c960712038903141c0c6002600c0d131514003801a0054044e403202a82c07413815a90180407aa4801c070300740800502038100c0142d662000101d0340020b44c02c81c40000e2420010940001c40250380310089031244142903e41510001c520820f40d44c0e40303410072038031012504050161440401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 373505044 1250 373503794 373503827
    0x51207030b06070326041502070309050a1401121e0906060b0304030c0b06032e1e15050a03032a021804120804080301090e030906070501060609080d0c03 67
    0x2111440d110005a0780c1e071064404034081010340c1030a403000c07a070704102080d41003078041180041e4a00741e147e491401e030300c1351022201c45600260240415004801d0000a4003001c2c1480380c0303040c2c403040010078592044410a0200780385256002180180d4041c0300c01407030310340c15a07480c04c5000c0031146000e0101c03e4000c132512900c58401181492004000e14131442c040d0ba03446d80520340c182049028618050b0485e030181d08030108100b01030400285c48507048218005001c2d40843c81e00b0410010100c8109011500e070240200076140b900325000f000c0c1204003200f04002081c3c1d50410020919482d210090116000694507002045402110044031035420781c5114402c645900140d0000000c44228001c601c0b520140000d200c1001003490007070140c0c0c1400c440031f040c03079161f0741880e000c148190b140946d1070360f00c140d08542062082e50140600a08426151191841e040707012b840d503405608001882c80e040043c0881000582c07202001c110b0b02c038448001250b813070454081e04003481264 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 373506294 1250 373505044 373505051
    0x19061b080a05040513140402090a0212040819030b0315040c0f03030f08060f090a0e100f0204081203040807170f0d0b0f0607230a0f0c0e0609010605120703 68
    0x80803640c403400910180381c442d5181030b03440b810700c410002904502d0300c4469515240c040b2030030f124500d29003007580054040760400240d42d5100d9000010384100c3d00d02c14848201002400100005100a80300e03044200c2843c119282d1000c508074100e480000c6080d606510041e1507401c5a50064201608036008480030304801d510352030600000821a4401c4001401d40c0c081c044035550301c00e80703d5401543c1101c10400c80145c120020f491050003a004000140e904d1000c1058440200081004807203c4c0a050025110702140740000f500144a8541c680c01604201c2045100c0c88048910403a40407101c01d0034980d040c0c407501020700396480744101d151810003c0819412510020b008070288030b034000300f171005d024030501040724050b440303045c05540b003401401c0009500444565803130782250495003054028a42d021f140c4400b031540540f4075840406441f080c0000c00d541d110a0703494002510b11203803201c0041c000400024850000010410300198441d5124100c04a40007141403030040f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 373507544 1250 373506294 373506347
    0x30b070318030f030f0204080a1101020f1509070602010902030316031404030b0912030105181504060f09050f070c030804021305090102090a0803070203030f1b0d0f0e1906 75
    0x1550002207209402040d07441000002955250149007044040c10070150304040c03070441002d80e00c240c0e000c030007000440f5001e80040e49910030000e2403a2b841d1080f0440e1807403011400d1a030380c20351040d101a801c6004151703000c19030f50b0050040c450001e07130140c01140340481001075919402e031200801c508115040301c070704001120800c09803000d94002da007082000c0c00d2592100749440c060140748076030300b417050004010a40d1045035040c110f034a80d0051801c0c50380e803200400482204601c0240d4020b00c0c09030041018140d80d80b020007540c10b0b00a003000b881d00d8102040820108c1150520000b0b5440103808000130b01c100121071f001440a07291090382c0b0a010070000c141e6100301c0e1800813581d03012802c21054641102603500401c03590000c2d52401440350007094482c03007001d4180101000002da40c81c5000340c01c3d00d204410021600903208051810007004100b10492020030000421070303100412545448400440ca4150300d003581c91140e45842c00070307918a2000d0210703c80a18110190 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 373508794 1250 373507544 373507571
    0x408070510020903010f050114010c0314040303020c0a060311160201020319020f010b090402030709021c0c360501030c110105041a0f0415020f09040c020106050f1504030b0703 77
    0x101c030108a1980d07001da00d581e00b003418982180d0074900d200b22401d04140040041d00c0007182801c104901c01e185c2003c501c50301e400d0075517181410000000200c000085c0000606501017080c04088408550381c1003040c1d501d500031019611402200f0140358010060803441030400242100c445d403040c01546e0030710b80d80e4502c0350851040c5035400e0015812228045c59590340c20710940c039070795000300e0b01c04101c1d0500703801080d602e01c100d001300108141d000810007242148000303202c501c800030390006e0040e05002c0070004c140c004a000ca01c50381c00501d0100070000d14a80c0c00001400d04040e00347d00c44186007800440182035419210014400710510800b140da0f420b010303a034450b900444108000030720400802800450081001c541d00d00c0d81320501000070426030b03401506000d02440035032038184102c03103000c540c840c42c1070346a0f00c64a851600d41800da01034100104586049400000340200740d07080c440440001c21111081034000c00040c0000344038008480d8103c40705241c002003c2402840b03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 373510044 1250 373508794 373508803
    0x30105270f040501060b0711090601030e06090a0c0b04030819033207020c1e030724020c01110c040f0b10051c0204050d0f14030d02090a0509160804080705 68
    0x4049681c0c64040c010003040c00000d0080c0e00017400030904d060b15016191716902c0a041c00680c03040e21401c80031021403041ea00c00c0c1c100b180866115400e549907400d15a2445070307a40600a002c807480c00c2c0c980780c002034014a000c203482c1125007108800c2d240c07421000400b6441201d128949041c10fa48804c2c140352040ca00c656061071162004c104031902d40800c2c054010814001e08803000c5510401107030043c0c0d100c154140c1c144408408101c0c0100701d500001904101c0c980d0807210042004030380c0440c080394040c04807500d600081d000d441c80904a50011685012120107404840e030001d42074a250b070a00764081036103082e00040c006030b000000e0000404005070303c02510000b480c0450480f014002c8100c00758001c10702a5801c520702850700c0040350b0b003008000000343c4151f160940f104188100010716030403070707011182940d548100d465034100094000503440390154050280c08112130034070400d02801062061001034000158441c110742d50786000780102d40100003408a60300240b420030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 373511294 1250 373510044 373510051
    0xd02071b08070f0e0c0f131206050105040c02060103051b0a08010c05070203060a050103020319030c0f0c1e08340b030114100f0f1106040b04020405010b0f03010527 72
    0x4002d041c1c454900800445040740c950420380007000d006041c00754006244c0105e4070b1400780750340e0f00c64070b450080702424001c10140d0300020a4131014a400c03070820100da4000380c161032084504001541400d50126074500b0300b400020242d91000c00602c007541e80f811074101010100900048465803a001001c0c00d40359045486030200f01c01240c1d0104602c3d050224a900490703010b400c0005601d503400082e070b11042c00040b00804a41e1202003000c1c5440f0303441542100b0b40190b48180c1072007661901c12a0210380b131040707100240c200b40c01e51032074180c00181d0208640030700c1e00030b016601d1a50402c2c14058404298510b000f40f0b9080e070411890400240703200242a500d4940751a589041c1741207000d0392620903403034456804d010502d00b00682000003003140c0354541c50180090491443c0170780d10f40040c010954802d1040b0410841048030607180203114a00c00d171814003943e680c503d48144030f0b01500b040c2420030b074000c0c80140f01604082458030914844120903840180078001071418454054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 373512544 1250 373511294 373511309
    0xf040203281a0618060703030b1206010317090f04110405100905010315120605040c090e0a14070f03080702060d1a0316080d05090310050c070506060907050d02071b 72
    0x100034190b1602440361401000742400c0e14150718200c104102026000d4200c1a01032048001141b4601414880c0d48001c0342c03550301409140a49024002d0700f079440a09210455041d8480250103504010800c02c0d10408070010303180f2043c4128900c2004060100d201e11a482020184070001d0250b40b400104200c0e400e0b13a031600b01d00c15050200040030349050880c0c4440d42006543c0400481d101c1100c0b480595810040024864032a0314040302850741d554040305d011400d000040d5005000411205682032195203042401306103104108d84920380740c0710389070048030501d0342000803808100c001c0c40c84500c000c2ca40d501d041c1200b00d1800c21030702c0c25201c4060380d40b103900c0007902c1810200011101c460f585904d081d56644bc016920365200f1511030802c04014000c6103440c4946c9040042d00c01926042034203004a1030a450b007150244c111042c241c4151040801056140c00c2c6219854081c5603135070755091420340048100b50195000e848110303130325116803803520540002050340700041e1024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 373513794 1250 373512544 373512551
    0x120506030c150310050a03080d0c030902030d05040612110702010815040f09030e0a080c2206121703010b030406090f020306010f050114180118080d05030a18020f04020328 75
    0x50130a683c0b03a200745030001405245211410710115403008103503100d1b180e00b0080461754490119044000d8807800100a42520403030708026000d42d009000351050341d0f010380d6000241101e2503202c40c180c920b0142e6054445008006500255115003112075100e8181810343c1755002c0190082411524111401d40c50300303a481c3c00302d504041d40101308817811401100c090009d04e04154090703484110410b0140e00c94400300305002c140da111004210b214166000c4200115543e5a440b10b03238841100d03c1c112058890741d0307a076a0313200e801482602e050381c0c520003101d81542d55582e200380003007000c1281668014218042c11005a50403c0298042c00300c01c014500128540700014240c8080c810562021038018020441000c00c2108030b69103111092034440c0c0030110001807110300b224140c0011381a0b014040001030300c2e80d00400114000c0182c14403c0121001c441c600d0954285c98210007580f100c5210f9001d40700d454990040d58016443d0041c5103072085600640402810728812000800c03501d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 373515044 1250 373513794 373513801
    0x60e070b0f090a08011b0810090504062f041401050c1606031104121101090f1401020c0d0308060409140708010e070f0e010e070207090207080702090108030a120506030c1503 76
    0x3c0020303460000740103150080c01b04421982d400c030069030450710b40404000208000404007004a6512001003a010344100300300c1c01c2034104880607016480903044883d00b1406201d40c2000f10b001000041c460702d44101d4200b03400c0c903104e410a90000c446003410420700303108010081c4020700105422000380302c0001d0842d0b00c0c052014066482c0e0f500e041c0c1401d0000d1004200a400515500311642e0384822190010482440180c9038500b0940005000c12200303d804644180d00102560100e1001d808484841c2d0803181044000d600f80c090090000e0b8031130001c540d070707424150040884503125003109960040c0800030701d4940398440d40101c120341c2d141c050f001811203081c0700c07160141c6130300040f80c04041d0400e561340e14201018845d0366800000440003400d641e02c2445040302528040c0b806655405442c2042170b010303085941c003644941100c000004c2d0801c0d00104035800c000207a210204242c100320b00440080030010011a09800754086110b140e80e01d004103d8030307011280700c5858807400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 373516294 1250 373515044 373515049
    0x50706050705031603020f0c0607110f07031707020f03030a02210406050301060c06150e01060f021501093b0d051e0309011508030a0e0a03020a03060e070b0f09 70
    0x92014000303000b03000c41042444414004044180b4680a00e0308025075a5000c800b90f8440c544580c5000da02e45000b1039080c0441903034040c4048103001d24800c00c9404462810f80c0b095251401480028a403250b00c0500c00f491800d02c00140c01c80320300042482019200500c04a42154441080341005070860071006c01420314080c2c10341d03000030a01c031149080074104480503100c0e1006004520602c18030112110410940c1d0700300c0c900c1c0ca2504030000c0700709980c42c220284004000c2c05104042003180d100d0380c105030710004914a2080e4000f00c41c044c60703440d21b01c9400003060390300c0d90701d81c100310240028a00ca10f003071000d80c040d07102403503d1407071000c18084449041810842d01c071300c1080f1080028a0004207803294400480f011007884550b281c5030710b5200c0d80104030045158200441070f0b0070011b01300c203021014086090040c1c540c04071003211001040106505404020350120580900f4070120303085070300c041c0c551017804040b501015107078940c41c2c1c0f441d0400014a541c008000a0100450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 373517544 1250 373516294 373516301
    0x81e09100207050612040f0c0909020f0102010b0f0f060c0105160e09090a0204050a0207050d08090601080705030a06110c0f0123130b0c04051002010603060615090e07031b050706 78
    0x1090703202508001c0e082c4000541d280c42545901003c3d50820320100303090142c0300010b482c1392030748504215034040d999040b46001e0034142a050b441068000c000d0b240f59401800b550b1010a001407202e020f1481e81c0c03081110706000344000e80d401440034021945c0803102480748901032110118540c6009010800007815414041740d00b0740241410000d2006050000542d189215811500403905a4034420b030340c0001c3c001c041002c1c2c0148640640c000c0e029800c030329040d010f801c00c3d006441c030507078807020242d584103070301d105954141d4424500e840124010354044105100c1e02c400c12840c01c43c900d14918034001400050703031490b0b55240c072590301044a1400c00c2078056003c510203945440c01a102281c4404074600c098a0000a08000344005000c00111409414014080980c51040800080c001c005601044542d945040004508080c1500301526200c2150383d4035115a0f00300103034095040d5014002c6000c1c140c40d241000302c1031903803000240108144da500c1c1c45e116080381c18148142c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 373518794 1250 373517544 373517569
    0x3020a0609060503010b0a050f030403080601090e09030a0e040b180f1b0406180906060504080601120506041b0b03011701050a0902060d020f07021302070201020d02010b0a06030504081e09 82
    0x41c04803058082114580042c00e6a0441c2d070b50002e03031a1a0841404165054400d0f10b4149c020503074000f00b004101038020211038004c0d54281c0c0c442e242c0ca038441840b00d2901d04d007640e10701c003180e0040c020034890078414002c034800040d000e000810050b421402180312542c2c28407081b4031810a1008201da00100c41d04030507402030880303500702d4078140c054181c0c0d04244598000c540812041001522011411004000003094085010010b2075940c2c1070040441d00706015051840c041c04000043c03600d44050900c51264015005d0314440d100c99469030003500b1554440900c080e40e070312000500f004040041c60007880c1c0189261f008100b4500464212000184807000d61072034007240354056181e8000f610071060320b9120040e40e8401c1040c42c096140613641000354401c071074050090070035000ba0003030311025100b81c08896280c04006805d0f402d90f041d10300381681248081400b000020300c40c2d0003050300b2a02580501d450090350401003461282c20b004006400000010312010301c5c1407561002c1c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 373520044 1250 373518794 373518797
    0x30f061b0c0308060f220e07080f03090609130603060c0905011106240409050c090609250302190206010609080f030d050c091207050f060304050a0201230d0603020a06 73
    0x29440072550080c1031264003610440c080c80c001d140f900030b551199406a080305c2c0121208400c0540c00750400e1700a80941c2d0784001072400344400c0002e141c0000a10043e005201c8400746041c44000020f102c0d8941000b65890b80c00f4956600351140440544190006140104800310741c40149020250034140103038403442c1084002802c40558507008038483d0b0300440c8201b09242510a80502c038034400354010101756002d0f1611088100708240003c03145500c090540f031009481c0d90b030100704041d00c0b02c2242c411681d5600700d40c2c4034082d11101030040074117911505006042503085500b0403500d5454115000c0907900a0005102840d00f04170324400906012000301341000c130322640c044d00da000d81804030780100e440e6008110140d4010082d44d94441001d0040c601ca9203c07050301380d82e9840640308060003170b0301450407900b541c1410001c2340d206503088401025000e1f9540c1c0119060f2107103507110050b0514601301c1130cc0115002009101c1601c00304004a1841d0450041154000d440c3e4003200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 373521294 1250 373520044 373520057
    0x90b070302030d0504030324030b010602150a020d090b0112020a08032a070e09061501020c0616111e03060c03090c010c030c06021b0c0a0501140a030204030f061b 71
    0x400096002080f00c560740001c440104254071a072809502078038000400c80101c11000c1c012406124031401080201c902505001101e640d0342d2030166121039658003451041c036012000076a804400c0d80090001aa4a81e0006864205500d540e14004802e030058511509258115800e510306280c40741c0c00b406c0303400007651403da030f560318024118540e480840c0b9044406030510f107080c142400790b840246001551200e2502e84502c1c5c554031b407802144d06a01444028a1081c40e0394030000d1085051500940043d1505030f8581c1c654840c003074140c004503150800c0700707a40030316900c84080760203042d05c46c036154186c06403c4004160034454010700300c6280701000d10800881342c2002030f090404000c0ae081c01045a403560030f084420a04c40c900c05003140d0700002e13030246c000726010510180b030302d503840941360380c070380d06000f048096001c07440340c14005100351040001d81040c0c10001c0915520500380145000e03601d64421000a21082040d240107903a4080701c81c1c0750400c1071286241007958503204 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 373522544 1250 373521294 373521307
    0x6030902030c09010b091201060b07032c0f01051b01060305010b100315050402070507030602341505071124130b01060806040f1404051218040f110307020d090b 70
    0x43c6107401b8901701380303100303922001488103000020b51000740503000c1019407d03074440450a0250203014082480030400320007401c1f40313508940d01106a00f5031400100701e681c46181e180e0044586070800c1e20444610030525001010050b800d01c180401144107c0000c24403800d03200400910411140150081c5800c3c10600d04003d910340c250340068500461300103803550b003581000e519000464100078400c0d88002000b071840710b032404407040c0c002c681003501c1c8589100c841039604000103078080102000320984884000500c1d0f80c00c980c0e40001c091500340a4101402c140030b01d07014031034a00a0301042e0404204100c80c3c503807415582c6c451a994003c20030072045555402041c2d00510400c0c00300306420010420320f907150b820401d0781c256107003000c0c0050141b002400664000a5404403240d100390294919010841c606407140104144420304104200c102488058400145010a003d6581c840c103050400c0c1100554041c10b06036000340808072920001074110403c03500500710245060000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 373523794 1250 373522544 373522559
    0x6010b0c0a0f0309120c0302041a060702090603120d020c1c050a0c06020d0e030a02010b030f150c070503070804060315030b01150c08040b091314011e090606030902030c0901 76
    0x1480501c1d9800541e034118040c460400b120343c440140c010840c0c6000c0b582c0c600c17082c04024501902640c0c0201c41c10400e4501261280404901426045820420610007040585002c040156018002800b0ba0708410800518580c0711b600455020b01140d5011408050f1000c0401407103003040b842000b640c030407503150320f0090041d005241039407040110441c243c0d0200201601a0394120b00444401d00209001a203003544a03000590908015840e2286000440c03400142000c0001050070240c11031544000f11820500c078014040c2480c40030070440d800c0080c008000400180c0e000e00c61580e156820000001c1c1590300403602200c100000c08070a202103907103545102d0444600c40c9061469492800061350b0b500c1407400050f041842c00300c0c00240b0054103400400341c000c0d040b110034000c00140000f0700c003141c0c0c510f510120180503100061144002041456441e072408040c007a814540d98001c0f4000d45c1d020340c010380d0010b5180c840c40c9045080401003507a001ea0229050811036060010b03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 373525044 1250 373523794 373523803
    0xa050903071203020913020702040b15031f080f0c0a060809120d1e020306130e0303070c031206060216050904380f060f0303040b0f0d060905041406010b0c 68
    0xc0241000501d0302d962650b840c000d504031444140c01a200c00c40303040802164000941144000380d0081c1d0901c3d03843c01403071510501e141403c91000e11690b0441d1502010550001c400c540707401c0709242e04030382c04508850208642c11041c20100020f1900400c0101030003944007030b40c0e00484c04c1c49460f90911030300f100c01250074244500b822070000d0b29000e01c518540084e1000c0c1100c51181d080300080c413900103401341c004501c10381e01a0b0b019000207404540560490b101020142031540042c808900c9040c0316000300e101c010b020b8a4612030040a01107810111000ca51107940941c1c41204a00300440c4048040700082c00c1c00c03a210a06031805032900b140070385031000140705034940540d51824103030140c801250b80b50b1407200500064980213048103411042941c1c124440c1408603803070503840c83c2c00002c550550301c14182d9181441e00300024442c49800c03010b5450b0354940ca42c000403880c480507109891089005802484000d024014440e041603010303081521000c40c108448001d02c080040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 373526294 1250 373525044 373525057
    0xa08070e0612060c3a05251d060405060301170d0e180702030d0e011409070605040b25030305040b070503060d02060702180c0d150e040320011b080a050903 68
    0x8020f4902044d40d1741c03514001c0740002c0b2601042c1041c080004002e40c0aa500c9603202d1000180701e50ba000070461075600f10b0004510140c00040c040d000c0104451450301c02d080e40a11014050f503051030b880380005156a00241c0000d64601c07400225042c81d07200c10045040940445c0c107140824a03508c81c08103c143c3d82015010740d0461040b03010030061842081252002c4803054810070058034040b45044c080c0c038206400c5ca01801c0e5000100d0080c0c80c0c04100d01081710300603140c442c609860300c17904108940001480c0204101c0010101c2c5800103201202c0810b41c2c4079950010f075519007803030040040640a4103070360800c0010300800596440d8904071044203a0110341e81516012144002038403481d10782002d4020f024040d0a202c0700c041910041c2001a00c8103405006403002c001e82d0300031910b01841080d56880095001c0340203e406007050316802121401c4030114004452005030035074282e41004038480e04d440c8920b140556001940341d0700700b4501107003070000341007a0b4000f039940d0050380b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 373527544 1250 373526294 373526317
    0xb031506070201020f0d05040509010f08030301030b0907030c12020310110313050a02040f0b0307121101050702040209150301060e0d0203060703110c011a0a0b0307090b090a08070e0612060c 83
    0x288041c1568020012042d5504018048894440070000c0060850f00203108060090314248001305504004041000603a0030520056046a203562100241140040c009402d01d001d20b01000c030120f0703800d0302001c000c5d00c100407201c004100e640c414107151016602c844d03a100c501d45440003070a114214200ca8003c02c030380141c0e1451036210b090850405240c0b00c00290301900c4c20141c00560070007038200c51500c8c2411025100c4c503a98039841254104442c0d0f8004003e0f01e040c3c600703e0400c1d8091400380c400903001a10045c1000301c0320022903210100d01d0075005892901000400410303521540070070b0303110000d0740e0320220f00702c0640c00b00380d6070b02000e820401410b441d848041c0c0b0801051049d5003400210b07000034810720040220154081030803000d032a020b2000000003180805010b02124091009a07507011301c083d140c00301a0500f5000451400d0340284000400500050108207520103403034652030718151130a010f000c12482090322200d80e12207401c0031040202ca141018251802d44004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 373528794 1250 373527544 373527547
    0x313210f020102130b0c0c041a040615080a09080f0310090c020d140d0b0a0612050a020c0c19092d06080601030305070503041d0403030510080717190503130b031506 72
    0x1446c102c9405d010002c529280c005161581c10311031403805000300c500d5581c0c123031000c00c9120380300c40e081d041c0b15010310700b17500c0864019408114242a2a440f0000c0c05000d160800e01f090303c80c0c60208860790041e00c640391690903012003030107d4105031190b81c0c1045641d000610710391a04000141ca5918200c1c5444906140881c0741810203443d43c005d0240b4920040c00b002d2100d40703078003010f03104a080c0c0c009400300f43e2400000611000751031003214116801c250051059595960410500f203801030f000b030500c55003610001a840300030f40165082d100c40d40d10003e414089003255004200d2040f080c1d80300c03440c1880c00801c0801400f040c04c9064070b41526006d43c0c1d90034581041c51942c4903560040f100041c5101621041c04000c1c0300007070050b403080d9020310141d2944541152204420300903602240c0296030200314407106c0045160305921070343c080d40d00840c0d11a07003100c00401419006e0301d06400004e0038440c84020051440090498040300740e0071030038500080b885144018440d24005d020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 373530044 1250 373528794 373528807
    0xf22060e011508070612060b0f070f15141b030f0a060f09090b0a140c1b010501030524090a140c09010f090612110103020313210f020102130b 62
    0x1020b401452152a01800c0c0301e40490b50340250f00d0344c0b4141c80c4a00310010340800c4100300280c1c06030140304101d81104c001d071818041540380141107940045404c03203048112414420000b62591198001c204038804001410b100d00410b0b041040001405503158207041c08904c44011030f0002034940002c00c0842c00561076490075002d81c020501a0420080d60204010005202c0b41d240c1080b80854032620041e035603911898240402d6070007080c0568070300702c1507000241d00d0907262400307003034090441261145440c0303400c6607103401c41c1d10a0f003054a40f5000081804140d05409400c84ca0303428604c1480d09041c6010f82105480c0c10002e60000c10009480b5902c580083c0d007040b4401410a0050080d400c559440c0d440000c400b101d403203a40740150401400203208100110851211900001c1c80c1c001d00603110011802544018445c0c0d80c006804607844000c80d118014000c88017407401c510020f040c03084280644500c0700c024031a41168010001c0400c200c40590f025011980c00c1c82c40642c4460 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 373531294 1250 373530044 373530071
    0x40503041a0d1a040c0315030206130302040f0c030c020f0a110d0b160f021203040b100e0106030b010e120d140408100f06060804020108010e0a0902090c030f2206 71
    0x1040d44202050382d424010025100c0e4544903030a2454002210100710300c5d04070400503000d807120b40070080e41c4a072040a0030000b50820394018020440c0a400c0019560707243c3e800101100e507500e010a0340a03940340d90f2480e03c07a400d485025a4605540014080310300c0314400d482c5e541481d01c0d00100708044188080d811030f2039940c500812203500106851107403804002c0404000d40302250500080d612071460071040b8001300302e1600d65400844664616907640e00c40d242c0780302002e0100c0800f039034808000150364200300b02c0f45010f450503036170206003404c1100006007148000780c0d005101c0c030303042c00024030803590014503c03078141c0306ca00f0990701030304d02e030a01c00d5210f0095074003048550003000907035070700528550f10281035840003d0081081d1512102d046030400011100240407881d41c0c0d006010180c18200160b81c40b10300444080b07082c54856022661040c81038070b441441100100030f11061103c0085a42e80c41600309503800e0003000c010007916a1030005203800791445a8500c80c3c007901c0c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 373532544 1250 373531294 373531297
    0x3050901021501170d09080c01180803040815010b0f0405090709090507020a21080117011b05040e0708151009030b040f0c0b09030c013221040503041a 66
    0x19070b0880c29450156a40b1144501c1d41400140f40a0030f90242000c1ca00300940a02014010384500400034041e48070101c005468000801a4001c03404655180000d5070f803104000a001034140d0301c002c3c222107206a036141d0412901a044121901028003941040d4201e4038156802c99000b00c48442051f1101d400603144071581d0303080160708504101c1000b101c56000120583c20a02c51801c28450070150b10b4402c5082c04141c0c40c020000c1c62980041240040c849061074030301e03103a1400011400d0904050685d4070106070008008180c0c0824100b040c81074078011070b980041c042c2424900f510302040f40e4040c03580c520b0b24046c854128840d40c46c185a00c1240d400c0061907100e46080510704060504d84044862803204407504111460702041200d078103000d480b00001d000d00101280c0080800540b40d500980c0360100d2154250811200c59840c07090794100f80c4a00210000c1c0e583c0500e5410300641d407420042101e4500c00d0806110028500100301c80071038544c400c260b01c140d00340d4403141c0403d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 373533794 1250 373532544 373532563
    0xe0610050f0405250305070e0a050f0609060408070608060f010f0c0b090c0306010b09100c0c03030305310b070e090a23310b0703050a0204080304080f010b01030b0603040305090102 79
    0x304c0b01400d102c0100c0320b0305a404507000780f130b860321140c81110612007005440d0013580101f681200410b9105050360800c480501001c0e60300421090401d074541643e2480c0450640c0450000b80f440e90901500d0700b40307500742104090081c80e00350704203412080041d00d24000842c00500d03080d2404001024000c0502940102900042c11b483d11035035611820307041608048001442040c1055502c00c101e8000c48986480075441028406224a0354a0540c014040100140c0c4d250302c980c54044056014505490242c00c0700c0c2e0810b00b420105410401c1d0140300090042c018000410058003403541c4c1d03c403c40340d10112110020403e4003407200082c1d00318170070340c0c0c0c000040801c800a000701503621845105024044880d0015150b03403906d44003199602000000d8605c43c020303400b10b4415486900311961007009420054030f01641c419006107503030300541c403018440d0482004c901702c80000b03006544556409280034441c408491002035502c1c80007034001010b103c1b00162491280c6d0090107500c90 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 373535044 1250 373533794 373533841
    0xb0313060b27010b03060d0303111e03040b0106030636090f140c130b01090f0f030303060905220606050d0c090518032a01020d0e0610050f0405 63
    0xd10301c06000500031002d4004500b041a032030040012070102c0c803010950b40320b6100100b0580788840700340c505500a200c0900d2400600c482000345241400d0140411548904101030050b503a280c542401680340c2c3d01a0062000c042c02c01004008100400300300001c0b03851940056444000c1420bd1032030302d80e252140000c191412b108482040c055441d210304000e50282e449041c421003400922074541c02c003041c0043e0320608000740030800a51a03840303809030002c1030410700c80780703a194400203460580c641c0c400e28424a07201c1d402d1082603454042c07500201480c1c0010302c4182400c41580c4035209e8001c2030030030310007440340c0650140b150a030841c10042401415408400c090750408003100b2005024025055052030f0200342441c21101c548050800d441c00510708000040010300f095421540030b821030700c0700788554004100c000b8801002001c40e07840c40010002018503001f03082c80002000902c0041c0c1b902810080d035107070342014460062040760005180d0788c840314900001e07491800c0009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 373536294 1250 373535044 373535059
    0xa0e070512010f0501060e0a120302030a03180b270a0b13050718150501081306020306010c061404050d050408031903091b0302010e060403050c0d05190c05100305010b0313060b 77
    0x4440d9001f2060608421060359818461500c46c114500b500a20160042c0180d200304103108103a4800d81c8801c400e05c190802600f00c0d84902d803100403801c1030954214410941a40519a03490701c56260074000e1031040300a07003040c19258a640010240c010818100240800c41101c20004288100000750400c110303440d42407a0300b2502080200700710381401240280160012807658044c40d41280300304904c2200c1200c02d60700345da4590203508054001814002d01c0b00d9103c0020f0308500401c85510380c1001803817510301d46410301c0c5283c01400128441444070400040c40b9031440030049030103211041141c85560140308030b040f4001c104909d40500001102150b4212500c4030f00c036448200d80c001d80c2e1300c1c000c0c0348200d03003004043d200d540707c0100b003030303010112603900e9080030041911600d0050040e1005003104600c0404032117081882168491f24280c0c06001d0f51800e070405001c52040d9190820456040014058407440042d04034414440000c01c81810816290040310f9010340192044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 373537544 1250 373536294 373536299
    0xd020408060c03040506010b0c0d120b1003020c0105311112030a0306090e03070b0903040e0405061608040b010501360602011a030607180b070f05060a0e070512010f0501 74
    0x7401260004d030f03802c5549002e21000054155030741c07815680c01c82084000303003000350070219040e82e51481d080701c01c4c3e00054441c41045920707035500c282003040543c00e03100540d40c0d045086402d400c45070b00503c0640100c6460301c0501d50807002d0080a041800d02e83c10b03c188142250420740440b40008254540c003008054400030000c801001400c81e030a003584080c01940d44801e000c0c415540d800d0f4040d880c95201b40003480c0031903c1420600d400040c1e10003603074609510b641c900c1003402d40885040d50395600c180709203d690000c14522000b071a2051a01000504003943c91010540040c0300c0c050404c92085a01800701e009603180a081d444502a040790900858000d0482181184280307000b42d40b030b105c1403501810030079090201405005001d028203503a01101502d0004818001e40c0c1074440c0084089002c500301d500174281103000c0e001c00f0401410a140807894404c005002500782402c01d10180310350130000402d80c054031011200ca010400c8481c44460042800000c80703940c09080c203000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 373538794 1250 373537544 373537561
    0x6061321021207030506072609070614030103080702040c02100504050c03010606080c0406050a050c24150a030b09150a090c12080a05071401090b06041a01090b0d02040806 75
    0x94202035200356078507a040380110b5085501c54600d0f2002600b42d410000018007854030480300301c0c20392070488068000d034150460044900500440d0343c007440381e005002c140966034009401d1b2201503518045503144d0760669a030340ca002d0142000080c002c94a036140d0742c9909001f80074800f5038440401d020825407406081030b40e80e540c902141c4c40d019500e420070200302c6d14414004103108114840b202850326160503022242c2d13501500c488010000140000101184144500d0300c0000381001c8000f100700b00052001007841000d004009070040542c4c4a03811134135900020f0044070740100709031906689056a00f400c04a0549420490904620400c80b600d0101e0b40400a281d000c1e4004501e110f449400368040c125800d8805025503400348004810103124031700070222244207880840400d221011039900303568508904a4948078103604000d006c1c102407003110700040f900c15100381c10010076400641070b074020740108a0701140000c1c00c020003440940448000700310210483d100c034606242c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 373540044 1250 373538794 373538849
    0x4150f140d1a0301060302010806100315060302070507050a03020d0b0603011806060f0803092b02090a021c060501120b040204170a0501110424020f1e0c040212060613 73
    0x1800314a20440006042c00c5090520480c026203034182c480d140143c81d44010840c00a8601100780d0405031900c0d1341e1040c06c640160841c0c002d00d4961805a184c000900e840340c00c000081d0002d07402038042060800160f03803a0500c81f00300a41041c00700c03006031107850102e8050b00e1090810030440c64805854020814250b1003241180c501c0340e035200b1a40d44030410070b502e911031040c24a621410540e442c81e00c0ca0360203039202c00000340b0110410000307265035001c18400030048481300d40c1c895020591401e00709030100012540000e0348420010142400c0002c1c0a14016034903000d82956265400707603454440394100c07006800c03100f03107540c1640f046400103a603980064800315000c1d42408010000c558560080d5800c0d2074a05600303180b6800a0003104a8030403504500c0400c600c40c84400e181c00300400d000c902241007240100c442d410710f030003e001c0d01d002d251030071941c000d80c410072412104810f032082d0700f90890400ca9041e550340700c4040e12722402c100b17190401c00100d42400081c40e201090040b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 373541294 1250 373540044 373540061
    0x31506031503160311101707030b0f01020a02010207061b0213020715060b04120f1202070617190c1e0801061b030f110114010b0301030b010b04150f140d 67
    0x1801c43d00e0903214907602d036220b09003d00c070040400d04c0c5e4003030280003468030f42000d0303c07040c60a04e41012000c4110400b4002d88000b9180c101c0480c1d5544410400b42c148480c1000c204c80707081c0014129580990300007590b80440e840707804100708004001c41164240f803124a501181c0091000240283c4200a08025888001e040f10740c4480024144402c02c2e681c040c3c14112001c003001c86050510b08204601002d9002c60b0484450451059841c0041c0040c44003c1e078270110f590003015002e090140150502c0c01c540c49002c04584044e0421502341030b03259080200c202004400b1401d805550020381d100115210090b20b4030800c50140741d007060b40007505904840b819555800406c01c809c2e01c4d404183c144420150000b9040c0110228003405075006090210910000003007043c80e1a50504003110280c028110601001004100384148000c0050240980071500b6242c20310381052181060320f0480240140100c0345504a050307030241088070070411040b0303243e41d613501d9024404401400000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 373542544 1250 373541294 373541299
    0x3090c060f2503022a0402070b0a05090f0c10050405090f09010c09030b0609040305040801021810051314060d050a0b010f031e020c0c03150915040c05060315060315 72
    0xa2030034000c20b81445021001c681d42580217400040244032828a00300e0f07018060141082405d194a00d26890340c0c0b009101d29401090a10b48a04120b079100c42904e4014040c400e05900400c40c5409841000c00c0400d0f40f00002c0728004040e59008005850718020340c0d0029030300c000c842c01045249417011b0703607551060320584020081200c0e02d03c8259580d40350360001503c445600e0300011070508040304880e41003801f07410a2070070642d86000042c00da82c803030740d9010403800312440c0a0f043c6051000c03800441101c1d504000d17080181203187d401e01e143c050712415a42c560024040e080d9034407003104540c12000e555000b40042c0c85c100101b600030f45680c1708024001403000c146481014440e1060140c03030720b1501040d42010ba491080100603400c4001e4403810f6008031242d21800c0e0b0b4040111146840c030005d00c003c40b62030034004140c201442100482502054a01000300294020890000b41c1c0c4080750101d443e40c50b4405510b400002032044aa0000000014003131380b441c020703a075618041800c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 373543794 1250 373542544 373542577
    0x902090405070905070f09060813080c03040305100e061918110f010c0c09020d0612050c01180e0f04030c0c0806061203091c02060f07030e21060c03090c060f 69
    0x11448220351206c40c2d0321214000034089002840664401e08030320f5000035850b04068200c07951a10340914035405007040c8186030740002410000c01800340100707180040c00003000c00003081210380480e00d806000b0310700f00c2d103035001005900748082e40350701102c1d2401c3c041008120f940203a240c9503040d480d040142d82e10070329049011039040c0d0321601203444c0c0381d6403215603130708120b1a10745084047c1d040f1000744041c10b512420080b0b1600c81d14200034054034040c00041c0f403014040c00002d0610314541c604003108265a00b03040c003180301c42013495070f0418070041c2c02c8403042c1e4550600702c681d00d4403030b00e000b0200c4004400015055030000b6000340550f41c120f82094100d00d40e00003055072481405640d070b4006045d20b03107000e61191001890850180042c00742d40c81c2c0080943c080c00c00d980004822804204001c000c0c440c6070400030090440300118910054901c140d070001250307519170040c04030813034010000005608000038410706c441c00078090840d035220b05044103403000640000800302c03c0e6410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 373545044 1250 373543794 373543801
    0xc060f09010207021f111c0801050307030c0302010f090803030a06080c0307030b040f031709010e011107032001060b0408030319061d0c090a090902010f03060f12060902090405070905 80
    0x20103100b11541c5550060240442942480080c400d2170b050142c200b051064a0024070000c40040c40350821000c0340d01c020511000d40d00401500b02d01040c0c00c031602941c8440c00c1800004e841c02c00100030703643c090034034020f10b1040007401c0b9942109070300007448a00000c400e000c03108031241c100c0d030147c400a20a0b507501841c15020f066403901180701c00b814a4071304001260100da01c0d9401040e40030b00a10b020742c8400307940f45811055160076a49005c15030b42d02c0e02030b0034840c1020701c60951081c589404c0d8526043c241e480061a1030704180c0360a0000140d0348100031259400d6018500400c40c10034982c0c0c94554541c00c0c980c030390300200c80000b800307400d65240b94880da0003441100203595600d4001001c00000b0701c12072043c7d490040c050325034a501004007003403d6541c80c031460010300e00890007041c1c4020ba4030004007031543e240411414141498803c0c81040300050317948060754048400c02404003051f04152024000c0c0d904042e4201d100ca40600003032000204045040d611550300c24441b646 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 373546294 1250 373545044 373545061
    0x606030509190609060e0718020f0f0901020a0510020a0813050d05070602041d040614070e040b04020702041406030d0504050f09060d020a08010609060801020c0d030902150c060f 78
    0x12422609076403150400316a0b440a1008980310010345800b034400000c1145a980c0d899084812501400200b58011a4200301c550001091200051001300d429800e240000080c58080d004240e070940d032031140490b0b514620f0744200b00103184030b9005000c9865105204060000961054819100082c001000542c40a510124a40c0141e034004000c0c80a5008107401700da041e04500801c881d00303a020400050303d00e0341c010140664407014416503000c3d003480d1400c1d00031030788090044600b070040d2000b0003040540140307583c0400001901c02162400180c0d0015000b4402c0c01c070029801460600307904001785c41c40c0e051501c142e81c1035084600d07188100c01c1c04d55960146c0e100709a8898062581207905041000301203801c06000b0300100a4400d042c0d00146a240d0b103070300850a540e541c2d4600b0480d1a0180c000d000082c501c0b14005c51801c5100f2003225181e04d40000500185503c415441045488071a004a070345414184050f4544100c007003080d4071240306031540500d00f440140420b4110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 373547544 1250 373546294 373546301
    0x20414010201020c030d0504021309151812080a06030b1314070311041116202209050304050a090e100228090503010c050c0f070e01180f0e03030901060603 68
    0x40c94854025410140e5a911078406020008d03c1241c2092003065100222800d038098003101c28407030300f011403000540342d51040444120b05030b4071030103000034208070002c914012a021a8542140b42c1440c1b140e484400400c0600b142c0d60009080c02405410842d006203c60901c6105911501c90f1001116004610943c1d44416003c0646075044c619101c100d581380a44c80108042c20311000182000d100d011600310070321551409803002564a8001c6000e51409002c10b00000341c02c4503000802080040104040742c80750050f2107816640c1d0405009100d01002610000c1800400410101d52100c96072000351000040241c0244503814a60302980c80900a85060700d0413080c800f002001c1414100710944070041610301400070080000c03407152828041e8004004164564913950300d2031001d81c0d890200498402e02547d0899038003485181004400300341120312005403c810918654003000041c48211941c0d03100794a09002607000d800040007651081c4161002005032580d54541035054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 373548794 1250 373547544 373547557
    0x18090606130e1e0702101d0a030c06151203030e0d051914030109060e06101e171006020f1f0908040b041d160c02010c020d0c030602041401020102 64
    0x201000c81c03205102802c004460181c3c003944500c1c0c0d0000f030001401c0848a69003050302e01d01d006800c4030b0f011649910704e41c0074401c2006100340c441c9400c09040d03100180c5403004540002c080042500004013480007540061501c5e01d4007114452200c1c0d03079074120010311300020808402182c00c0003120b0f440300202107405074000190b601c51510700038200d61102c0ca0000803c1d2200103114004032641c5d00343c82c9007409140030713009400c4000303129814641c00312a080d40c0104030034170490090092150300c0303501000d2030741000c6084040880402200c8400d84603003000c040c90608202100040054003010501c0103021100242c007610a201c0300d90300410b031101c5800c060010001e1b1506006050901e20740d018141c0300e400b0b000c8480c10306481d00e403158055809503105a642045c0740707820498001d00e0600041e0400003c900c18581350003c1d03000074108540e4007401078103218030504c13030806540f99020321682c4141d20201940c1500e032a03142c524002e40090154680c800802e0042040c994014403c4412 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 373550044 1250 373548794 373548817
    0x111215090114062101141008070b04050613090c0c021201181502090d08090109120f0204110903160f15170c0702060c07090f061d0a020f18090606 64
    0xc0c0e50341e0f00710a114500c560001c0004440f01c03041d8914845010a1089180e0006200100c96050404907100f0b8040407194010800302e801407030302042100c10700380444088540550b007158680c420640035149494007a404004001d007000c14503161654000a15200e65208992113048036503240c0d081030880e21403a05079080550000c050801140c5001018002d221210a025142202200100e8100039103610101c1d810280410903800e81d68102030040f000c3d010280c108000c00800743c80d00c602400d0985c0019000e80d695071001150180b19100700e9218440140c11a8a04440ca0486842c001d0351489920000c01c44110040b48207100c5a0380c0d041c0c1c824440d074540c030300780035007103403500714a00701805d641002c003020089103005858907400780408034100000751510b28030345580c01050b56071004446000c81d14111040c44100f81c0d40506580c00d51220701003040039503544080384001e1140783d074a203142110102e0800b260240c2c8090389030041c0000e9502104a460b041c0600c04140606112101c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 373551294 1250 373550044 373550081
    0xf0b0c0606150d0e070302090c0901050412080d06061107080712080904060e160e0a06050a2102041211100c021e0a0f05010206070c0c050d1112150901 66
    0x40d03851401080b45049803020400d024a421050204401101d010207910030300e5421000c1d0400a600d0201001c681c083c02c2000c60610b05800d100000304548928052403481c01c49461504051200100517100060710315641040030351745508001e8404013590b5038180c8144901500800c0481c40490601e04507038007240c1b03420b0030151960720210f69410044801c2d030420359078240019000442c0f609e06004290740c0003038018031003d000005010440d1140541c0c000e44a024040190340c0d4810115180480c041c9002d018030101090301501031060030032040d190700e0000c00d001c103807502c6590184a082d032003100d4006a400d041e1050210044688440d200402d4061500001600306049000005c1a02034141d2088a918600081c15517003d608400603410306107106014558040000716000002800d244100c8000c17075849a141d0700650180d180110b00c05400c04040284540760310110010081982421107003c440d00742e61480c0c04900c00305080052000f240310050180304854840400408a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 373552544 1250 373551294 373551301
    0x50906010c020d0206071a01060318030f0203190315080109020f040c110114070e01020c0d030f02070b0c01051b1606051302060c0c01020f12090f010c1406010f0b0c06 73
    0x10341d4068420101641c00c41452084480103030746410040c011581700743c0002d80d0240e9500701d00a01240160442400d0500d40b0400076900744068455204595041c54103000034001100101d00354003034051040c0607100320908090120344c1681000b00425130801d02640d1140d900c5600f40e0982e040200042e410114a4a40b0210342c2050b4024040c641024141141100768440c6607a0031180d0540c41a0518942d00381803090141d441030820400358000d1005020320420800015060310100a009050003280003200101e00d0003408010300501e40350400b1500c038004009140e001e000c00315580100c0c9000300c500e603000031040500707540e9000c81001c1009035042c82903031844c004081c003030a51180c07005428503400c0141e54460052081d45e203910301410512540c0c1c40064035005c402d00800c1a26040254006a00b01d544030a40350701c1c000032500035090031040343c0182e88000710b89101a100000008006100c0040010194100c4a00c0f03c480b80c1ca41d1b031342e4215540c0902412071108030b07a41107107010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 373553794 1250 373552544 373552547
    0xd26060613030c2408010b120a0b15130f080d1209020a14040b03010b1e0d050a08030f0a09080406120e0706020714030114160302221403010605090601 66
    0x64408000203400304109a600c80d00d6400c840e05080c0d220813401c0c030381c500e41804050100408400c032074015007040751180d41002c9a0151901070b00c100101a03164100016410060700e03005203100c000064a00c0c8000686200140026030244241d01c100100d0814002003a4180500c58001c4420303000180404540c002c0c011115845420303103601d50b050300c8003a6940076031f03120b40c2001c7c020310030301d10806500c2650105000550703810040561080e458102e181a60b900d80301e621400320007148580901c890b400740c0010b0118030805801030802e121f109507450403c484140214000c401076200410655174142804c001c2e41d0f51b84200a00c1c40030700f40010080307035002d02000d16003c4220715011038010031000301a45400e00650140740103070700030314040011204004c645002d0b501c1c107600a01189078000034001c2541009070814407422800c2020151382c3c1c1c800d03419210a411050b80400540344a811a24089202402a5503000d4041c0242e40b00034036051180c1d408a81d80900302c9a0540c2e00c0400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 373555044 1250 373553794 373553797
    0x312040620060f010b07110a1d0702070e16050c010c0807020f060403230913150b0c0307080a0512070306060e0301090b0f0c07020301090803010905010f060206040b06010314090d260606 81
    0x494041c41f03000d00720310207641c881c3c070503502500e18a20710101c119110f51114440140c0a0304400c1035400507e0188000c2094000095000d06a01d03011000d6405801e821145e0344aa80185081546050008150f0790340c0010346602550099085805050711340714013030303121202039030014041071504d5031980140501c64040e120719181c1511481c01c00036003001248141202800c0c00820a941e56071140c8403032032100720071001e8881c0b003c04c00d04210150001d10b6882c031504501a04010005c11512005031094044034070210300c900002126041008020f4081d18890284901068260510100c20304051044883c1c6a40100e0f00505640701c0b90402c0f40b020801400820608034100320103000345e1001d0241800d49032050a0403544c07503240c803a00e041100d030f041e00f200c1ca00c1152261304102e000c0c4e00060040d00203070011000c0301a41c6403400103a00801500d1103440d03994030841e003044600b22020411603820281c40d01c6452450f281900d00799a01d04e5459000300c800395001020860601700700c030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 373556294 1250 373555044 373555057
    0xd0509060717070f0c1b0305010f0612110303040521010b1002100911060703110105060d0c140a05092508130b0402120f070f060c030c0605060312040620060f010b 71
    0x800d00349501241d1580c40745204101c03021103000106d18020010041c0905c01c0d0040d10300588410803030707a41014091041c0d4204c80c00054100700840c82040c080d0780c0c0030300896000b0b00c0014541685032400c144840d00d01141108906015480c005000c24142060421105030f1032556000c0d020031200c0712404030007001d101105880e80c40100b80814140c0c5c43d84802825403034000d85900ca14403804038145401e58000411007402040c2020b51400024034504400d415500566802000058104041103060b80039601c51640010010b05101c6090000c20449030a40790202e0441c030761441e01e030016591020180c1d2946a40003680306030801050320025544d810a2004003841e10200301101040d00d030030503d8581c4109a086424200240c41400440300020a201d00b001c1706c0311051914058010340c41500e000d0030040d01c03100051a1a40c05028107044515601d45481d207503a02c521000340340071881300f46d07001d40000408078016441000a0340500c0382140c14517600d0941c0c244a030600c40390b000f04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 373557544 1250 373556294 373556297
    0x305040510020c03030f1201080d082802040b070302061f15030e012c0a0803180a02091501030b150a0507081e030a0c110c0418080d0509060717070f 65
    0x3e030041950f06100400342a110341180c01e4841c0030f0062505420041a0711840c0c850b0322082d010707a09582c0000d245580919000041c80650302649840a0941c09158590328030b50b10009000c1a4024054090018140247c0c200c8a903a5654003030b240b01103c818190415003544010304000c680c4030000d0f901d04c0e9036154a0f01040951202801c907084d82c20710082044187c00d000180306c01c1088103000740702100907040040c9041b500329201d00c5000c0c0b06c040c180394052014580e86065203001048460215940507080c1e82151420000001601e0482c3c8101400a81071480c000213071f24140d8912074a010346400e02d54a402c3d00c044c000d071a40d5100383c03402c41d010b0b0401d1090b02910784000d240c40c505452201ca90a507280350070306809081300c05040c844002c0c01911a100003c0030000036010f100200160360000b00f90351555800344800d005000010243c00d00011298041c0c403094010341d00446412003292010748940c6025280c0000c080e4102c582c03d5001000a06210701c940202418035009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 373558794 1250 373557544 373557553
    0xf04020312090103020f0d051b1207030b0a0510090503010f0c270e0403020601030b06090f0601180b040603091202010e0d0302090a0b210612030a210c021605010804030504051002 78
    0x60806c502c4940c00c503e400c65026903032081000701154550841c19100c07050074812030303d8010b000c010026403410141c41c150030140c0c0c44408529540b030b00303010304018010040c0345285013010010010000d503498003d4034000c2d42400700809a42c0001e00034002100c4080d03d40c2200000010135603890701c1e06010380c144403560b817503100082d0542e5111031039000d607010b070740548515030641c1810f60b0b03650400b40010b4011490340d42044084084041060340218003440e10400941001c0000002041c00c1e800c18240d00000150001d085c1d5019409001c0d814070982c0d0b0100d80d503c150714103034222084507161000940010245c914024402e900904c5541c0c0b00420000b2299151071040c0340c01c0d00101240c03148a00d031401c04500d10314503e044140c0c082000c036019884180b224003c143c403402016428014410710703155503048540c03440d001d9054031140e003c040103c03480011000356140c2c0005289107403014955000304181d407094400703e100d9034140d00c07110320300391512061048500010007002d0441c000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 373560044 1250 373558794 373558807
    0x6061803031908010602011103010e0402040e010b040e0a031103070c0501080702030708070303090312050c1606060e07090e0114030303010308090301091a090d02010203012321070e0f0402031209010302 88
    0x200d04102c0350410340e82e5041c103250704001c1c1c06421100c4081c003c4103504401d0004000f00003100c03454940c019070540303002c04d000706800c00c1700303016010803c0200e6200b820b229610b0000d090004002d180d01e8069a10391030300c030100302980f80c0c032441600c03400b61550070303240d0040c09194007441505070804d8003807040f03926154190b160150207070440da20490020343c45d220f5000c24540c3c4504203a0000b0351300b0701c0401c060300707018500c545c0a1240e107800a00c03a40340d00f0200c10511901340d000d0b200600d150920030350301c0e10785250300a104d4885d6000b9140c840c5403102c00824040c41c182c001b41805c2001074011407840e400c54840d402a90003840403640c6c03641d00c6002c1040003440840c2c44101200c3c00380e020b40311601f422107450303080551110f056402c6a1052004101c0c0115140a010078030100f0b1100d04401c01c21180072540a40c81080c25580722410505481310525000407450102c4403031446c0407401d40c89440190552a40640d0040d40c50f034031154030b00c1e0443c8140f00044c0301080c01410010715042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 373561151 1107 373560044 373560067
    0x70312110901020c0913020402131a071101081008030c010906061d1b040b1204050712120f0e040c0e0f0a030816030c0f081803060606180303 62
    0x185c000d1005c91200507007141e42c1d050058001d402996603599180c900c6844e030750b040c415904504c48c2d4094881541611006584104d94048000c88180d8038035401103404007809045000d030f001c0e80010004500400300010540000100c00205011b011810300d0000c0300e0b4554814407440d160408075402c0000340c404072640c0b0030000741051020091220320380429000b9600282742050001401c0740c5903500400a1500c2607225208550070700f900c0703c1c03851040282e90781006040c86070012159030300901981013120961141e20308080480c030b07040c000505990122003020f002c20300304170140e1610b040c400440742c0c10350f0003030310796480c0035196658800d680d00ca44040c007180d100d102d00c0c4000c20188503032070324080c0a40065848030890840c0c1419581580708444d400d2000505151944080c2800303d09140304d000d0080c113007070404d402401c450f0301801e03103503203002d616000070010803078100c = true := by decide +kernel

theorem cover : BRFrame.Cov 373381294 373561151 := by
  have h0 := BRFrame.cov_init 373381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 373381294 ≤ n) (h2 : n < 373561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
