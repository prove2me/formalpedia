-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2076
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:11.157249+00:00
-- url     : https://prove2.me/submissions/ca92ae6e-5954-4091-ba06-f7dc01a03546

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 373201438 ≤ n < 373381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 373202688 1250 373201438 373201441
    0x7090614060a0306120602090103060b0901120e120d05100e0408030c030405030d051303180b04090e012a09080705010c02120124030c08010b1005131a07060c110303 72
    0x604110000b40403840403480e000030302d0380d01c2d44142c04408407201d2041d50b00326404600344c04156014071a44001e4442d04c0b108030308024505c00000c142c140140d1001940544980c885c0d04901c0c010000702480d008808942e68840460070380140003040c1c03c07030b200382c01c40b4000540065200320948c840c9016941001010786143d641c24040070043e0b0019104070b5040c07004100c03442601c4407601c2140c3c010800f41c45614205100c81c103004100b9016444500f8030122868000c021045404080360211051140c0101d05540000c030240e0042041140c50b400d09003200304601185006c811151801d40c085884200c10b05459402640c1e4070342c094041c2c036002c280c00710000c00140c5400761001400520100010540040140a82c9961342800c02c0d409403401c403c2c681031041003040e0781c1c0d0401400c114002000551094000550700364440388148081c0200042e81413400f0080380102400b07400002401518040580315501c0e032540000e0b8190354451a010b100b1078800e1040c04900a81c2030340038011800d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 373203938 1250 373202688 373202729
    0x60f0210050403020c0603091009081206010305150f0f040914070602030403030206070c0f0210050405031002071e081e0d0b01030506090703020d390f02030a0f030612050c03070906 79
    0x81c2d1f00c0036003009018851008990150040c0e4010001068070403841c941e03c9521454660000201c00b400303050515003018204400306846100b0160b0820f001c0360b105404810943c0803800c1594442d1500350813600b0140102c0a00511440c240c1704030074506c0c1221541569040300b2a103031f00480c04004c0040e0802004694883c0c400d41d09407e0490086803400e04a014590001c1d10a415180704a80400d1001c03038101704518040c00102c0703200300d40000541c0b410070240d84001e2400b050520ba0729090041c5c1310b80030244207c2d00e05540307400c070244011700d03a0809060188243d9801246ca19400a420400304015030b511900451b4003440c0040c003421540d448601080d4003035040401942d00d070035079400c5504126030a0a0040031000e04411401031100c2c04035075004e40303004002c0100001c0c44000340d0a124015400001c503980c410880c03809071252503c042088000d04003541c4011210b82c03040d02c518003800b0020561403a121400c17805c903504c41c0e40d65a80441991402e00ca858107031960860307100c14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 373205188 1250 373203938 373203949
    0xf0f010e0601120c020106090605010c0c151110090210110606010324031a060a0522021e1c05010b090402090d35040522060807060f0210050403020c 65
    0x7001041414091888103c0c20741c10ba0485a44144c40401030703441301802c01105145200e0000582800e1a00c08036056640d100c3c1b5400c87c82c60721a004105158002c0029114441c0e8840440006840706072a4955003a690101c05440384403401c0c6e1003540c000102c0c805e400d0080300782e00c900040c4440a01050340d21040150002c02c140514944101d406094803e18006103022001c0514410728040400501c8111716400542006004a0080700c03400b90070311142d034408640c81c2d4401d0f05010140010035145900d0000382c0104c00440c01c4950085040e0340855841802a181106c60f000d4200740403120504018103580342803094039003a9030704000395183c90405400801c8183c402a14a4920f19404ea580c2030b810760b40d010200001906100f60300171000b50f10840d4030250480070040328101403c020014031403250840c103262012809024400380d2440380d4210700c00030260141a101c4299983e01c000e420100d40003295401070280080340d08110810f445201e000d2a05680185400340f0783c007040c0003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 373206438 1250 373205188 373205191
    0x206160e0a0801020d0606120e030306061303020306040305090907030c082d07022404030905040216020a090b0310050c07120504090501090b040e0c0d120c0b1006080f0f010e 76
    0x9400c0200e8141c04201c0a03000d00007010752503002a80011041c0c90034000a044150f50001411200d08080300150300c40c10000030340c1e03040301e01210070303a42c3c0301c0c03071180d25211000c05503100a4242c040e4008010a2540000161501c114161021036071660341403800c6080318610011100420f98000205580d030b1002c4603844100d052542d200c5001051031b07040c11070008021980e0b000164007140c942c0400c42850800d4483c0c0e0a59411007020703d040980e000b9140902038010350303008a80c040758030b451043c003421881c880c02d90098032803810785444804032405071103815030190281c81204aa4001642240300d05882401c0405581c0e081800595592501a42854107035042103010700c004250303e90144581c44c0200760385000001c00c001890b061106035402d580600384182c03c0101400071640b038480301030301c21a60040d05890591819002a2040712642c1e03800390000c0709400400c202c2c414003546c1d82040c0e4500c0c0d01c1d0111a42e80c6d0300040e2811803c11101c082d210f50b90702004000c000000203025 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 373207688 1250 373206438 373206467
    0x5040e070c0c18090503032d01030b0f1b030f2a030a090218010e0103060c080601050a0f1b0803040204050c040602030f0304020d1415060613060c050c18070e01020616 73
    0xc02c07900002c5e16418915042544c4210405d100040181c141c0d090310060b44110380f402c0303000074150f585142ca4414003040b008105080317405409000680c0801021604680211040e510988904000d4030b66503600800701c1e14020300b8018010f0104074210300c003452000d0003105840f00c1f403965940c3e0110a0140204041c100d0300903590000d104ae0480c1181c1c0341038080c10201c0b00000340c0d5803440c206503003a1001c8030042400c0c03107110340c140320107640c1c404103c1e41000301e20f0800c61424a10f545040724403400e0036110a190080c2d210240081100365401103002e0b170300841e014455916050b0400e5071600c20340c03081c01e000d60700c1042040616034540000d198450b00040850b0a0b10126482e01d84064002103542d1084c0d070003480701c9544e01c1071103021450300074806544503410442e9035000818094402c1c0513540c188a0400b0041d010404100403001c2c1c034540150044440003001c0042200400081c1c9005020aa21241c4001594800601c9030b01c107403401420b450700111040700540b0401d00501c0e0b030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 373208938 1250 373207688 373207691
    0x129060906070c1d0609042d05030c01090c051801030b13020901033801060507061803020d120c08150310050702160503070807171c05040e070c0c18 65
    0x105400310310070782d03200e20051844d03d43c03413100c1380344103141c481d65070400030500381c80342804038107110100d0308045000c091803071400021030000c030032000b901c0542c00d00001d00030400c0c800003451000004041d040b220865104d03c1310302551517120010417649424403001c10b41c00359020001000407844184049030071811030790390400c014600c0d40200b8202d0009030030a580001d4100c1d072042450000914500015100400106032030707130088105400110180728245c10040b01003088414880b01e03510100034108054029060241d80f454065210241d02c0c02035400310b01e882c41c614840c0c3c001801004030406255541504950300d2540c500101001485410380500c1480e00c0a110182c1610601e401402c2c6500140071b444a50b500e41008136950f600701901907040098100003006000030307120b00790744645034114812400490130a290805051900da0000345486e0b80c0081c894120006005403109610340100a03902c01c041540d207550501c0e070050070b40c00110010004201c10380885108007203038160 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 373210188 1250 373208938 373208947
    0xe091b06132303030a08040b220b04020111030313020105070309230907020705130c0e030709090b180a0f0201020c1e03190c0303080712020a020c030129060906 70
    0x161a60742801e5820500d4922031668049000980c00c5449145402c4102d0040d8584051080000d01200380540010b040c0c001d02404103405061086148541c8111203000040e078001074200700c11080410b4906a01040711808480c1000314080116485001c403104880c1d81171240e5401110b40d036100c030506070704000e82801c02140310721844601c596100c0011220f2020036401108001c2826405007000043d58044039040042d912500b80c00c440010036888000340030703004118151600c05c10f001c0460b130302d0f010351a0007060f12603040d48181c000c1c5000781c00c61040b96480c0d02d40c42d404011141c0b610714083c2d002e481650700082c183d542c04441c861061050301c0010301d503000401c842452100145400e1071045128485909040255041000030203000040b102c84903124a4214400c90202500700541c0500244400c2c0c01102c401d000c5000b01c100466541c41185002911022289141071095003040c100003980c07000002811080401c00c8146140c0200307500411100c1d612000350f05410040900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 373211438 1250 373210188 373210207
    0x19180324050f060a090c020d03200309030d1404030c0b0703060503030d0f15061407030e060d0902040c020c01020706110703051203071803080706020702010c02120d090e091b06 77
    0x382030301449034850072010b00d042240410001380c440d80c1001c260285029811201c940e80001c00e0002d4401034100050129030303030400400c031002030313000d2a000c00c8800010301c000345000200400b2030300101c071000c00404003542040925070200740c801a00080000300000082036120b0701d5150400039a060010703165607210040fa041d81c02150304820315555601c44030b00d52011501070700303c02224081d40d503865141440800f60282008a4817020800800b00c2d41c1c004040c05200800c948030402010a510b0305011200100034100c6a4000c90040c4c3c20a6005030509d4000903140d036101c401600a41042c40c1440d404565103130240e82025068440d0300e9000010034030500a8041c80c142d541003030b40d5070340307040c110141003690940c1c0103d41041481404202180030a0141c440d200d902400240e075a410500041303035080b0002002950004641c0c0081d02c070810f000503108003510290304c0c1c000c080c0780c0c0c49258042515007203400a640ba0809000302c2480036140310310352101900180064240320645 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 373212688 1250 373211438 373211441
    0x1b121103010e0d200316030302070201110105010f05040b09271f020a0e01050304050a0803040c1d04030305090114061507080c010f05160f12020c030f19180324 70
    0x82004004c545506000c0f40e5514440203600c60300c1c94218025454110000b9840d444803425100250400d90b011800c2001c581c03040a030300300307a40040c10003440103507158000075641e8409449801c1c42189000c0c80c0d070440d81401e0420b01c0c8658107441c20a501040e0301408074040d107991103403800c42c602460391031004e140c400031007907600a05044001a21407160503409020f54009400c03003414000180200000208002075241101c0d500480c5240ca9031514074100940b2a0150801800180486008003440311403847c00e601c56802507600f40115122001918203e642418100b04007000440000f203039030401d038600c50742120305420000d11700074658880300c0d180d41080c1080e891a13512064400505d1044d8000c3c1500600d8800d02c03807011385d80c4040d000d0000000380340568240310080d044800d80c2a40c660590310003040f030400b40c1781d0303804c4d004038240e241d0707840340000155004009981501c007500c11800220b8800c0c6001ba004225411034480d0440c24000c0d0410113904190001c8172554500c49 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 373213938 1250 373212688 373212703
    0x30206160827040606020109020901030303110913020703030b0f06070209190203092a0907030506040f06060908070b030c041a1c05180d021209040e0a030801031b121103010e 76
    0x10482d014210480000422042e1030255004408581c1042c3c040c0007d43d581c4400c550449925041c001664050081c480000e401a03850003070384098104074111210402da00144042c612030f90b02003141c00440000c1001c2c0017224052690801d0052180d0001400d2100c52140c0041c6a005ca500d0240010030201c4180e9004952010660b000350708500c0c070504044032601c07042c600c0c24400528910407000400c40c118401002e0804250710740000c179805845503801800000d040307440601c0101d80b035540c041c20701c0407527100e01e030100c1c4a10100011494801d40980e0b001e9004040e0a52401e031501d40d0310307810741080c140d0240040304204040b030200348107030008101d6050150000300f0940b81246020780001c0405101c0b0615820060014845580c0030400f501c0c00000d854285480320307081c0c001710700200b000700102000b510a100e540d0090580011a66040300e20441e0f4940002c21f1000d03607408109014400c0341e00c84400d07001c50360001441140407002120001d400084c168801c0f1051502d01510f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 373215188 1250 373213938 373213987
    0x6060e061e04091407021902040207031707032003060a030201080402270a05090c03070608090c2d0a0b030c091206180c010207031a0907080f07050a09060302061608 72
    0x182d13003049040d900f15070000c5640c00000e9002810f0102c00c40c0c40000514500780d20024032450740014918101400740c000c1e1041040020000800f900d040b40026000f481d40907500204800300e14089402c561280c0d045a21070300d070151421162514603401512103a401603c100c1c5e000144502e1149051501820080500700029a0100358148408950b0807030324050a00b418540141c444a0440d4800040c8081220700d41d02e050b50440e95040c042e103041150003810143d00c05500340022400c0c50064000394417000c1080c3c0440506e4001c0001c000b00511180b298031400b40301407000503144184040a4410000c016202d41d103500801c202090074601e040340d00d0701c10b000f0041c129003185036082000442840080c0001c001d41802d607141c2d0b8140c0c0c0914500c1005c0d04841c10009a000d81c000c0c041c2c000148560383c2224680018502495201da280d1b014041c0074400704900081d0303503000c600403101103e03000b51072145070244000800420004c00300090300e84e07040402c54001186411500d940788c0c0c02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 373216438 1250 373215188 373215191
    0x6130513061802030c091e1809060c120a0c02031b060403080f0c0d0b0415080d021204060e040203040f050607030204030b0912030f1905010f08010e0106060e061e0409 73
    0x9003848009102c41d04200c40005007107205100304402603d0200483e070002ca0120b0340b901c0422809202e8810442e03c40c060190400d04140c80680c80c4021103080b103001318080b0007035414070340c1c681d420700d4003901900f2540f480c20f46818010407000c000590001c900d0056034410ba07440d1100702c01c4603400c25181c060064400b90b02813810841450b51003060280c00c4410528030200b54240901c4010390b500410407440041a507448402400b5a0341e030740500c05100384c0d02612900956240101500c64280c540b0400140c000d416625001040c49002c44082d5a103540320340d03c0c0d940a1005200094200a20132a01e62020140d10800b08104001c154481c0d2940e582c0540d49034190700d08030041c1e000140a000c0142c2c4200b1655802c0742081c020380381e020320f500000560030343d101030302032814955440c0240c00e20b80c900000841d001d2400c00c04031080e5181d900007480490707026190765003207440c64410340d00001d481030420130007413504400518120354900c0e201280c0c0f60603802c1da13414a41c480c0c2d000c40c0303855 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 373217688 1250 373216438 373216451
    0xf0b010311030f0c1201060306050c0918090d0f02160f0609050301090804031b0b0a090905090f12031009060f06110715080c0705030324030c060906130513 68
    0x30401c190003101c0c5203819000703420f0012010000c1507990640c0c2c61214802c2c11100400b60f203c10f030945c010030046410000511141c02c1074510076806501090003c0d0058002c201070750405121001002d0160f60060001c050508141078102d65940c44e00501340210b02480d07240c481141c5d140030600c0c02900c1c0800344015030314941030015040340040c2c3c0c42103001e82d0405d03441a011501e01010f66003140e03001098000ccc002c0c600096103000f10020380280210283c046061250326500c54054401d07100390080811964903135500e036030790f2210081c12885c09030b4011480e0b40c8401c06080041c2d6004044c0c0741386109180d0301d61100d8000c1c0c500c0740e0400301c6920b0700709000b0000d1540c0f00b51526220310014024200340350034064080d1070513980944000c144191a00466058090101124900d540100650382ca07810012402091444030001e40b07041c09400c0388096035285004a5264220403008041d1481c1500c5c4030144009070f0004c800c1d007085d26061000010b45519152500400101c0400001800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 373218938 1250 373217688 373217693
    0x4030e01080106110a140708030408030a0f0903110f040f060e15010c12030209030c09090d1106060102071707030203010c0f030501060503010b090f0d05011815090822030f0b0103 78
    0x11844164000800c0140050076028044400302d01709000541145910381d4020320f6103441403811031a9844900140300004000030320800110203410003184607610350102101d9114116801c2e001c0d4040580344801840c0310704040e207004c0c80300c01e101c0f803c0540042a82146060000116111035119910f114038020070032410741080903c80c10325644c01d08101e0408051a115600120301211343d1509265000802c801599010040420241d030700403d66122803a002000a172100400408a004500565044d1042c0c032404500c842c40b035072043e07004018032480d00c000020941084003400b081030047c0380020015031001e0245150203a4a500c5000104401c03c0c0001c007180c5050b440030b41080070600044c80031108140484840362001c40d04241e20482c2c0d40c0004400e40704c02580140710303601c1c120741840c1386400300707015151660040508201c213006030349120090390003482009043c550200b02c60b856003139401d018010042052902011003d4a95030380d4510300791403400a45009130800010004c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 373220188 1250 373218938 373218947
    0x2060d0603020301180f0f0c03060204061709010e0c101206030302010b01110c030606060f13091e11121902040612061d0403111504060b030609150105090c04090504030e01 75
    0x1191100107450000705c2101e4442c3c0c40c100c402142c00070040f045515011040c002444411000f40d0342040701150f485035108005064544401c0c100d411940c0d1040009058100601c035440c00715000401508000200408000c0f40d1405100c40c02c0c02c1c45250000b05410207528030404000c0c1d40b0a400018580010f107001520709401d000709201c42c1d602059045440303480c00324083d074000300156152601d40c8218414000d09006181901082c03840880e00040d00505030341011440f10301d04016050040c6071480403405954074070749050390a00b4100104c81e0079030503e80400b40e0203c242d07949100d1441c5042d49140030f80c0e1296019800240e0004003c41c5407001e9480350310010082c000401c6d5890707400884117020b4100080000c1c0512004091480075a402448110300050101480c0101031130f06140010041040d100c0240c0a031007050001022040700044e105100048a026421703660f281c5000c10040000c010554211702000b4031000501520728090580a54429201d08501240d010001803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 373221438 1250 373220188 373220201
    0x31606050c13140414040503090d0812100f05120c0d0203030c0a0b04020f090105010e131506020708011b0206190f140a0c0915110a05120c0f0c1e040902060d0603020301 74
    0x8000170080300520001440000c1124101681915a00042d0b1034a04243c08240030300b004c22404400d01004100007110306110000982d00c070380040010707081c0c441c028020f005103001c4800755240d1011100e07181d5413800809220351144001d046a15094840c08840c0c01c126414200b183c2c00c0720f041c01880300310300d89005a140350b0a0240e40c040c603030750b01d481c0000746113034080400306028140c441100448000d0130f410090380310b98000c0d2090a82d0340d68400c02503130380c00c0c203104003000b55103450404070301e80c2100b15000305510005ea0007080d090310b444850411882c0d0420304000404d541e0342030703103036914228003404c485ca88140c00c1c00002c40c6010101d54040e02c00c01c01c20030041007400c0c0000d101d11446c400d0800d2501e002850704281c8460740041c03251414103031141c09452441802084820b03c021080140741c0d813804241503e004a1024a54503034981ca0b944017203030b000300e01d00d044110f20180c031a0709104e60384001b4004211000e640d00880d07003540c4812541d0b03440a84030501401581024091103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 373222688 1250 373221438 373221461
    0x30406081501080f0a0b0405130512040f0605130e010906140f15070203030c0a0819030902060901030c0e04050a06050103060803090a0509090a0503032403031606050c131404 76
    0x8080c090070000003041e0010007807040140d86824070100d06007142641c44003001c1003000d00304201c0c1d800c201c450391500740035404c0d0031229403154080285451400c4401e4a0407a840d0070020203800c1d00f0210180d030345401000c1001c200301c014074800580c84818040321030003804160700c002507480c2881c03540c0c20a07140400255000d0880304080c48019101c680b9485003129284103ca5220251440060304510929190303aa8500c6110120428080040020400e10715440031100c0c0500b10081c06030161010144042d5011405101c078000550082d040a04c02c0308291424018a910300f42c002400c48109440c0d0704101581c42e40305112950700362003000080d1110400440c180160400007803684c585501a40e401243c44074082501e0103c100f1261580390b9000043d69240c0c80c1c607654018002802e030031500742034140002e4184d480e0601008480c1244d801d00e201015604864994a0260001402e41040c031402080038042070b007030403000e24015222401604585521b071004010640d50200c2a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 373223938 1250 373222688 373222711
    0xa0c031a090714030a05070312110607020c0105030c160b0103060c140409020a0215010608040615140f011b05060405010e010b011e030603060f02030403270e09160803040608 76
    0x2400949040081c0c0c8504031514000d81060f900140c0010074240342d00080024002e20501c00044100866400c45080c514055600c6495070701c0007212041e0f4428090f9122000341c2c0003283c001d843c03944108001c40e0f00001515a092408503107890040030345d001c000c0e056032121407850060080006a02a00017440001d00d80051014404003581c00079201d14421540c05035400a00c0181103030092050860648840d00241025a0345100280050108640441d4194074005039500048402442070082d00c426060ba0400d6415035030a02c6200100032164505000c0a021950f011110f48003844030003510620103040c440c2007601d400c9007920204070f0320301e004d6410428a01c0b5942d92119100708841d410208c110170745240194140c00526044d04003a00c2e180c00e0179181c8a5100f0541c000398000da10030394907500290700b03900310880400d044c2100301841e0445441c04000000d03104000d1a0802d0002d020750381640e40d505460f000040255001c030b08035400c04101000f0458000502c164044440c859 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 373225188 1250 373223938 373223941
    0x40f0b160225051c0b07020f0d02070b1c060302060316020606100c080307180b04030308090c130c360605040609031e140616030209090a0507110a0c031a 67
    0x2002c45141c400d00030b007401190280d605448140780c0480e00c01a0380d81148003055a401d20000094507003010700c144880c1441031019031080c10b44006880c108450032628210b082903c403e20102160400301d940b06071242c0c55020100260340d0342c030001c501511860342e004040e2a0100006810404001c1c441489429809800844650058007000c0f0550307005c000e603a030303070341d1a008103a44030b00714541c000f4010495a80080780c24070b410001401624081c9c2c0341c038030450f5200c00d00710b03590303160359a100c03034101ca060324642c0c0035030003541c108000420540c2041ca600b0039060b244018803542d019802c001603258940343c20480586904010040d00d9a0b141580c600340c2042c00152002c1d140b403000820007402c000b15800c07140c8100c84030381c00f91540800d1426000700b0319500d440e900e075001c0c1e034070400491200460b50401c1d402407081300c01491004c5c000d049141c1d1144c40c032800900d0020320b800188498000800365252051004400320303407041c2d0600c4291030542c2400c4015580031925107090281100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 373226438 1250 373225188 373225243
    0x3040201051e09040e060f06010c080c010c02070e090d0207140315150a0501170412031e05180c0d020409030905060c031c0b090604240b09031908030f040f0b1602 71
    0x7c0707110380e0105c42801c1c8040c5030b00c02d9161283c140e12458083d51119440d103820000f08036800300e060f104071500b190000481c3d807100140682c4075203042071090050382c8030010403c102c1440b238406400140c4003d09656000c0c2c8180450810274900716244c500d42d04100240740041d03d0b00c8400c20020308800c0c80d0014081d0884800045480b80280c00a811160702002091840b1b1103034000c9232044800442c54560000c03c0d50b080340151905803488401600010003038040c54000080c51101080e0041c02c2c00c2c020041e54003400010415110103030200704803440082510384401004040d480d44040003141e07918042c42c210101104a810700e03c4c4c8407400c0611410840e692800c1c860703004001128002010181c40810480d1021032486440c0c5048032101d0019480050101410074086d0036015680403c40b0031010914841d25554001d2145030140045600c540c1d0300c8034030641c0a4400c07058404005d510f920b17001c0103407608031004041e00f041484165000d03035041c490b08034401e8400700450400b00b80d18 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 373227688 1250 373226438 373226461
    0x201060f0e0c13140307062109080c030406020a0308090c010507080d0b030d09060e0d020117100f0902041e051518091f0b0a120203040201051e09040e06 67
    0x80c840c03441040c0c1c41d280411403101503201100c424800311500010800d640b003241d03455842c4a0b075001072080c003c0b203800041850103031003000c50300301200e0032503440082c003440480c00070840140241e0f1409003d01c0f84202041c0c00300000c00c090301c03440e0002c00b84070443d0b00d1300404108000306501801c5c0c11640c40702026980040a66240301c4d40003941e540c13286c00700d1031284001c00210000c1c0c0d40c54820042000011a0052038441c1941d09c0e5035104016001c22005001e54450b0040c0b000340018141400041200c0c56101c0154103d000d440d501c010403541d035115001107000a4100b43d04856001078104400d074403070380519036180050151015103500e048002035242d00704105500d9500c07400140c800060342c42c4c803064038491000401200050903ca101003043d4900e203e00c0010b0044a00300205084100ca0207484484995039031390344081c00c0008040b00603401c0900102e060000c24000d444801a0660460100041080c800340d20b40700d18030208001e503811020054816007000003481305c03c0c0f120 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 373228938 1250 373227688 373227719
    0x6061311091002011407030b194a0115020a052109060c030703020d08090c2101020706050a0501060509060f1b3c1903050c010e060a0c020106 62
    0x215104405210007001c26800741c5094a05c044200442e481000401905075003d062010350940c0d4282507940e01184caa000c000311400b44034000d82035810321801006214130403e1030614042e40c1c15042d1020004004440301020b031240162a030940010f00c4075410b4280c0d0901c62284500c000e019441d555100c05481e80342c20410049446480103803040178000b4001101d48a020240810399640e00c61880a034407500b08400c11001070050644650415202c0d0707060b00e0081d600c1c000549150303d8900200030080c000d40e080c124210042c40d407540030b0b200080c4050140c01e40100350129481c54045e07004021154140c10803024004113100e00340e059224102510000130404405542c0c0308100902401910001d1848542c8d9200b5030320001e00c6042c1010708410400c800c0320580203034450204200381c940e190310181906580c44403d00c4c41c851031200c210020072744d0007828034a01c0c1150205802c0d003954040702e1000c84541c8540244000c401c1e043c899400e51031024030007001400d09010310401700080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 373230188 1250 373228938 373228957
    0x1b090408090112020f04060507060e0327010c06140a05070503010f0e0a020405060a17060d0b0403030216060204121506060f05180901092f0a05070602040305010e06061311 75
    0x50f0a00480005989604995603a5504038586031915aa400c00031b100b9403001008503116418074080b00c501c40c1000003500d008007002d05540301100792078049440c50050b41001c142c1000f4887c07080c040440c50f1481a01c0d038003070085008110f646030081c0140d0a03214007412800400c4010401008504200c484640503580c803c21030100544803008120041d00031034000c198461000180c038440e5903003107041c03030442c840403000400096036500b00f040310750502d0510240c402d0300e0400005001a00c00d600030003640f01ca1080114202403241c40b031034100e0b0015000915505209070105080c0a034212006903030a5241c0c00500c029814042c0080601c0e0b0200303202c0040c02000f203020480b40e0040101c0c42280c400103420100c50b0340e56500c2883c01780c8070021414034452a00400b2401200c1c05c4a5a0101b060080d240b10740380c54050003085990341d01c5440c06481503036080c4030120005100b8000d0020b955810030051155062803003c10010100104000e0586403401f007140c90000035040560782c0300306 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 373231438 1250 373230188 373230197
    0x90305030a0c03020c03031303030207080f03090621010b090111160608100b03040302010f1a030a0b06010507020301110c0606030d091401050c2506020c0d020f0402070b091b0904080901 81
    0x16410729044e450805602141649030001061904040002a4002040324060f50844100175510020740d51a404076820118568204020850700c23400c0c1304009040c0300d94030080140c10507051a5000781c000401381c0007618030341c100041e040420342e441075018920101c40070203000c04200362803240c000251148146001d002c6c0340d600081069454403aa00000c21010300555668500b074070f0024020026130000619035460001540b1107642c000c1d01c10311281401800030b0070058040c3d1102005924005d02c040c2c100802000040e0058030300780039070750a00201250854441c280c6503462420070a0003400680070307520001c00c90750540d500131701070320803a5000c80c50000328039081c000484040c031500191154610803000754a50b81c1000180002400136400703400920103840f800c0803038441d841032810a5010b404c040700d40c0003501c2c2108400d0100d100c018001131070b2603015030b516180c151b13085403d906150090800d42c1003180014446c501402c0c41142c41c031040d45030070780d01e401c414051081c2940c10807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 373232688 1250 373231438 373231457
    0x111620150d0e071a190906020a030e120a0b0405070519120f021c020f0109140103050a1407080a0f0507141b07080c15040602060412030204030606091a01090305030a 72
    0x79101400300c44041e04000307540008512102511302801e5200302041c130400d00d0074201e216002441118030205480480d4003034124410a030710201c2e440d00c41100032660050307032a0551800b4010801405802c14443d10600101d481c1a0034100d0405206600603405010303090012030503890110b500702c042c0d07a1440c030345070100c203528148610980d141c03000003074001d950100b0300510b80c681c2c040c29221341c91007140c0f5460401c440740300440e04d2141900c00d0040c80d03415180002083e60107038004a9015074144d0300083e1018407501d00041d118070648220b40070071404020b0203000c81580c090042d1303007004c1010500c41c2d41000d41d001000d0b0141481711401c00300700469811241c1c0c6410107c00c0f241051402200c00031605d90f2000c940754511403c940f0301c504103c2d1902d1042c101c82800755405c4448503000303400a43d450780c840c44480c0c040d400783e03a410103500b0040440010020b1090002816501100240c0745055100d000d4005401074030b40c6061006034a01000010030010445014289616021912 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 373233938 1250 373232688 373232711
    0x7020d020904111302090f04151703071203020405090a060e15060706060b180d0209040f05070f0602030414041a011b0606030503310306111620150d 65
    0x514141c041d0f0158002000e510140141c08242c002c1d00b0f4a0b0310403240e007031111305a1410481200c00001505584014120f01005081103280240400d640c09006603454105035960390341c3d0032141809002e0101b82d0104d01400a420700510700ca44c0881c2c0700700104002403e010246c0c1c20800002d000805400d405040f5050b80d03103c003015100c2d11907002030300388030264aaa01d0100a0742001d4550111a000405680c0291030080002061190007070714203482925a44c807450b1019940140644142c030860f10005031184850403440020603290303010703641726820490700c00c4412208050301445241810808000c80082ba407a12003245400d091003200b04500416030034184002142c041e040910b0b0010020501c0341c0400100302d180501841d00301e84084030000200d0309450760006c040081189041400040d44d0395204605213404149281c0c100202040b20706504401c0c0c0c2c4086170107203d5543c000324402c20000b141c0700710010840d4030307815681d400340c8600100c0c041c03010480b40d02c0b42c64000c2d4948 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 373235188 1250 373233938 373233953
    0x120c0509061c050717010302151b060708010e04080d050a0e010608100617030d0b03070f030f0b010605180415030507060c0b0f04030e010e0a0513090302011107020d020904 75
    0x5444502030840e0361140c0b031002100421400c0070b10051805410080000d24203031207104800301155220590700c0c85a4299000c0c0503030510120318640302c0c1017040100c51400a40301150306100003000000340140d00c0d0240c3c000f0908803040c2c0c050b040e6074041d2030501000070401c0381901d01c07040f020080000c00b03a440c254100042c0c004042c3c0301160754604513020031303811800700341c104911120034024032110360350703003610066007403125440c20b25900144898a030011050700f211700070f06002001ca60020303071541121409182c0c1070707108546140c0541281000c0017099a100e03401068982403550400503101d4108003c8040c4202507803080d80e5a412920011164203896406140c1040868030706644548018101001d403600658040c2d81c0c2c0000914084040c4030194841d603495036840034011000c200549904142050700c0303074007011081002c02d4035111a05001942030754044041959a9036040203030031185c2034049d40094807000c000150168544401c0040120340c181c441c84816512800c0200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 373236438 1250 373235188 373235197
    0xe04050a1407050f100e220f0b01200601060f02101d28060209060903010c050a1b050606062515050105030613080306060903030c01090303060b0406120c05 68
    0x3000d212a0081d50401007400186000c241e42056030303625130810081d810840c0201000303050000040500301c030801c607820521290403261400004c0108105082074440c001c1e04c0c4140c0c1c038151440d6860350307601032569200640a403c0c801c040c00000601018032080750711842c0500503002444107400c0c02440c62072080101d09865800550100700c1c986241c00c56690928040041c2020b40c0708086000c51000801c3e851200300340010f800c1510808525540c1e40083d400401c096a401607041c000295551002c4c0521135484041780e4a40d9611803035020050500b0681d07800e082c40244451007840c00140c40000d0941d0072001c11a00e590329204032098220b4940c0c0351048404103201c010f400ca508220454410b00125058244140f10700da8a803c00d165880100312805110001c2d00400c0390085100900107580082018010b5807920740100003180c50b6602228504603241e5444080c00c0c01d2651600c04c2001619810640514143c6041b10090a40346189000380e20300303030b44401d44900c150141c002c84 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 373237688 1250 373236438 373236443
    0x11a011b1a1e010905011a0c060a1d1005060a150806060d020720010201050a0e2a04060b03041209120b090c0a06030e0606030d02030a080606130b0a270e04050a 70
    0x1e07040d6031101c03039040c051701080c480da070004112510100f002505d03042c281d034500520180140440d6032007000c128080c040075001101d4801107402c41012004050068030030b03030440c0d24800310345401d0210a0191286540e0711038005c4075010740615401940c00403800e500001c044900c25103486c0036281c00f500a01c01d600000700180580a0030b40025200a054240c034500260000c11180c0d0f1001e095034281d03088841080382503003200c1c081c00d00b06c0421420100300b25120342d04480290400202040860300243c2004140c0d51000c0104000c018060005130800340031441c140074960300e04032006a615030f10850061006080000240306500c0c100035880b0342003c010180e0a4950380c0c0c143c064014040914004154012680000c0041c140000c0c0c0c0460764189500562904009a100b00c428142c0900b140368812000c010140c40318182c0556030000c1c14207252215a0f50000e80409000400c00300041441c90380e00101d40c903060300f0381c0050b61045443c0d020180c0426a242d141950800c10f408200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 373238938 1250 373237688 373237741
    0x212010204030b010e0901020424030e010e011a040e0303072604030309050607140f0c1204030305120f4302010c02010c0203030c0a030b01050705011a011b1a 69
    0x100b40040c602043d812603c004510b8809a112110040c0c284e01ca01e0003619405140292004410030f20706815105051040c50009040b0b01e000c030030390f42902c800001318103440e0b444410340e0066109a5102910007681120204185030391101d1954032404010101024011152010342406403103010642480c503440100c4a15454507240240040144070b405488500c20407000401d520301540010001560181c1c0c00d90030403e800107405816404001c0d120014000d000944d01415200301c00380010b1486a2201a1611501c3c48a43c03030004006001d1003600003001d081c403008402c207108281840084c1174100002e5060b40300340800451511488403c041c90f50b444c0e03c000d8581c1907101d404603200d00d60090007602c0d04400e080340d41c0d000a49241c600400c007045010840d600940c4203075000b4406041150030041251034150848070508034012041c0044104000e15603480103203402076090625860025142e0b9840d0206441001d90488a001c3e001e8004218044458041505202d2000c480d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 373240188 1250 373238938 373238947
    0x703020a0c060c03270209060f01050724050708070c12091509090c020c03120706090b0103080d0b040501061707210603021305040302030a0c080915030601020708030f0f030402120102 80
    0x4002c0013848003007290b2002c485e07440305090501c0034050b01c07000c031326070010500d14880c0c803420100008842800d0701181401010000280015591450040b4808010011050400c01c0d00245010b8400007010345007006420030030040d000b80c0210781c034510141c01964084d160301b181c00050b11140e4041c0c02061507183c81c000000b0043c0c2d400541401035132010841400607003c1b600c010b80e03030b45045446040c0d150b0040949186460340e400c1c0036005890103410003050b04002a00c441300c003040207070001d9551410004480c0d4000009000c2c10321141000d0300d0400141d0f141507c014a81e010103003508841011030400f00e0800e9201d1b41500c002000400e007040005d1500c400c200004010b54801240580308910042c45082e0b0180b05882c8548c1c1c041c2c02940c80c02c6a0351000700c032020744402c01100c461000344070b00540b60300d400a40b0300c1040f200c0381c1d0190f84c9040810001e0702d402d02652080070726620810000500c10580b45c10b603204425198016a12500c903480001c0550184d84254101740d880440e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 373241438 1250 373240188 373240211
    0x2010906240906230f040516030c0c120819180b01050a03030c150f0f05010819030906140408010c032322080904061412030c060703020a0c06 62
    0x241009102050340041e6504981e0302c00404098581c2889603210f05040ca051500b8030480030120b401540e18010400100b044a443c0000e04550003550b80c0b088075495000c04000342a0180310790115070031075042c640740107091035070740362402c8003802c4080081080c0d07400424403440fa42c5144000c40c20202c4403d0040602c00221100f800040040a03205206460300000c0c15040c8540b000c001d60750140c1c1c60034050280b07900c68500b1841d07000b2034940d840b561030785845909002440b0302c4c6201d107d028008241035141c810124a00010340090781c810580c3c252030303071000a4200c1848000c44040e41894000044501008010390042d5800301184c4c0d420400c00c9007175580d01d41e011000015400c100c0c0310f6000d041142d41041035a04440511a200740d00e040c001c04040b1001d00011003e00c078010322450140702201203400e9850030740c002c00b243c404a043c600c55504c1d000702c8004a507042000118100550154843d645000282c008001d042e80081d409508610407546420410f80100c002d000001594 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 373242688 1250 373241438 373241471
    0x9020a080c0a060509031002070503070507090504150c1d040e07080d09060c0f0f060b060d090302060619030f05120f0d0c0905010f080c040503161a0c12090102010906 73
    0x4074891403003291421404100350b4081d40c10745005103405001000307040d80002c0039800a5114000c140c901d0b00c4188500030015000700a41c001401b24400701007020b080c149040605500034a6800078400d007410410719100c0d40c468845404804078900e80d0241808440c042070081100c01c803a004140601c010200740786400141024400c106a520b405815503503000c111800c580c43c84000303045402e000d2104000c9020007105220040c000c02001a8001c220400a1210752203518030042c0310303031200044070505406121903035200905071a11210f0300c8001c0051006621070340801880500e21168840070b02004000e074000746d0301c640009980c0ca030000113a20b4016003105064401c03050500c01070842c01845001700030110792041e101d0304c140720341002c01928a400d00409500d90810103010004d00d0f903400b0801b9050004103501c00c0b040142c205001d00300030401e10003464004201c01c10802d08411800540b840300c0e01d54200c8116111440b40004034050110f03080090804d078106050b500a9071b03100e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 373243938 1250 373242688 373242703
    0x1b090911090603303007030b0f09090a050604030c05190c0306051f0f0f0b030105030c1002121207020613050705040c031401060201050727150309020a08 67
    0x100d91922a0340c2d03901c42059a1840c0990020b6480d03101600d41c03400340001ca148900488012004541c18080120901d001501e911940c6550001403074042038140c04900890503000091403400303000c0c140001d4041041c4c219802441d03801100c10000080d240c44052246154885d44102964440e04003420002d0402c411004180c50314000c15400305111155100c3c03100b003055000600020162840e00c0d490b0051400500c5490010b9604804082404110901501030801011041002c0703040c034800c1c2c4081382c0d440d013051484c2081000180280d0b41d0000e1210300b4528105c80c01c40110100c00b5089084c1500618504090040031a8000401d9500e0045510450f10399003192441c1d0703141c10801c0480c491608024280da04043c5041c8400d0400d501300c01c01c0c0308454280401c4000302d0752840c07000082d0907800100181d5456081c001d03410b40c442c2c2c0e0144c55060200318500d9042036255a90350303d441078451450700036040561402c0403070203a0030490340580c00034030810b4016500c545507603c4807030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 373245188 1250 373243938 373243973
    0x19061103181c081602010e0a200103020403051005060a09050a0b0f0603071d060702061b0f030a0e0108071202070302010c02010c02011829101418041b0909 68
    0x200d00062040310b074100c401000000b0141d4036a04a0b40b2a41e50000c0c85142c10082041155280c00050000400c1001081034061042401160b450304e80c440c12281d00ba14070104a041500422003000400c00008443d201d40d41e02c80d10014498484a0000e106480c890b40001421410801000000070b00d0364030240c2d2410050303c91880c00c0b40100d0800200d440100d4103c404600f901c18241d0a129498507549548070f0054901ca241c036000380c0004c0c1040d041155061b80c181704411145481d000f00303000b2102c26a2441006500300002c2070f10181c108600b040e000760410040c03400040c40188100d9140140240010003156a8405030400038041c1c203038111020007560820303510600da50700c14414041c0701c02d44000444040303403c5a80b0044241c1c446074080b048c001c0160301c40c4040798800c05000d80183da500c80403020742071500c41e410b0b807400300070a8094420000d607400d00c109600c0c2884201c2d17205a2141c0104065401000c15840600c6103412100c0e50620b440035100401100d60b0311a0100803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 373246438 1250 373245188 373245193
    0x32c030d020a020f01141207020708030c030c070e011203030e07091e05011e03030c05030c01050106080712020304120318171e0304050d0804050a050d0903031206081906110318 77
    0x140c03002d00654803951b18040b4071441ca801000101317541c030f24070b80000e5041000d034410740b0049650303002c0c80c2c0e01c1e43d0004400034a2a401c0020380f0243d602c001c00c1030900070600c0d020140c2840d03150810000d210940c0c0c1e20041c1c2410780711040c004240038240b01035005019421800c000650940d810490914174100c9042d900b1490040042100702e040407401e09181e80b0104d0610116045070b804a41c0038001002c201d070385120070711507242c0c00700c0c00f030150324064011039441d00031528000e2001050054850a00801d40e4810400c0c08041260194860407480391801d000c507225111103482031041c403c1200c05450030034001000340c240c032a00d0b002000d10280903c608a0380a0442091200c2c910007a00c004116900c15070700021910300030008140e100e8011010b441d802070441d2140b5040451703440d141e00010b80340704000e00030150081401d90560140600400941e408c180c40e060303460030030300302d460100c0891000500821250b6001540100b5003d14075980b64141800203c0c1155440c00c40b10f1840e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 373247688 1250 373246438 373246459
    0x6020406030e0a02030d0e04060302060412050717030706111303080a09050f10031113030b061c0f030e06040306020d020306011b0308010e040215160b010909032c030d020a02 76
    0xc000054141e003584e80007009012007041d000f2041c0c68001010031410b400c551205000405684e402c00500020403c03200d403501554494a800350410541c1c0c0c2120601c00150b564841c500d680004c1036902c0c059004d14005000c4400b041c0300340040c040c128001901c107101c82000f008214482d03020b0211030b15030782c83d1502123545800420045008226040340c000801c0c0384903003c2140b02c0e42151610b18503d0310400c1ca00540b410325021103407a107400030382d82014400144000c42c100301e001d40d540c4500d0307512040c10411540c1c2c3c9601d45100c011002808100c00241e110115075280d200315002140e100b8401c540c2e038441005260065002103581c1408506920780055182110001c10a00c0c503178103036140710550382030540200410101030000e9070841c140c0c034480008103030b445004002c00b4104d51502e00b4600c100c3d140032802480160010840035003003000400009401203003103141d801108040c0440e10120814400364644a50100d0398503212710b2003040c44c45900829400940c9009403203c0a0b41c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 373248938 1250 373247688 373247711
    0x6120c05091b0d020a0e190e06060f09040906150914010602030309121e03010306150b0a0207030f1110050406140a1b0501110a12140103080f070507120602040603 71
    0x14072442c0b01c01141501042514000803d980c02400c5e911081d051541040714100c0c00300e2056900b4280320000d21644207800e0004840e4410103507488101220468540f2003e04151603042c0039202409026507215100b607810810250803906442c4241100c0c21000b903920704a1001410240383c0c4140d8242a9100100301a0303c04021240304008400041c000c40000b00d042c03084035072021040b40310381d41036840b07003002000e0304600660084d13025100c08101c4403030001b85414000c0d100c0d80822062030301008440215900401c10004a80d002440220b020081d8208038190300f0054611a50180d0112503503c0c0803a082400391050390740075170340ca03402d5402c1c9080c200118411020604003092010908107000c00d02c203e010030302c440c8910700100f0144a200003400a6802010413480444c5059290b2003610f035080c811001d142c4c9000f1001402945540c0381c00c03100d8814440055842040085c4240500c42d00700000f10081420706003c0342c4901c940c0c01c04074000c3d00103000f40030009051180d01403c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 373250188 1250 373248938 373248961
    0xf11090109090b031930110f0c0409030309050303010f0314030a0806090c120f16090e060607020a08100c03050105010806211009150e030313080d06120c0509 69
    0x3d5500c1c064001e0114809034003248284926001085807925015200741c034a02d0b980e54070522000030110002403010700240c1c0b01078026402d80c0464002a481407210011864001a420018800940e800540701c00c090a00310064404641c2c0a005448000000200902c0c01c034080c0c1e04030303802080001198004102c44644921400e60303004001280100414024030700900001e800032040c80e44546481e2040100b210910006c444d410391800712101000440c0081c0900740c480c6038091301d000300102e0304100c0105110440944054060400841c0500031500c0d11070308031015204010485516180c6100c4c110050034a43d203040c000a41058000540c65000302c1080c0c0c0100c2d4000c0c1800280b6801344038004600c501d6500c0ca500ba8824a0b0041c801a50144100a075103401007070a100038104000790002916004801284190300400800215481c0a4035031651990b012130060fa840340002c0b99080548a2038104440f8088120318100c1006401e1004800712207040d12084034640d9002c40c2c1c580e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 373251438 1250 373250188 373250201
    0x301050f190e13051009020910030c0b0c0111030406020a091202060d0c051b1c1103040605090307051e030c2b1a0103080c10090c180f1109010909 64
    0x181041103030903040c03100b009596010765120000c2d02d0392210010b4a6103981d80341c00071900c07000500c145e44d0403004055007001d40d030443e07100600303400343d0005500d150390b602d000444074407409c4d641352000315146107042030a4008607080d24003104e80340d850341041c0c18100c0003940101603400200c1c511300e000180b502024600042030700d8004200034106810b01800f1400f802112402c2c208110341040032091012035044404000804140200001e502005841440040c2d03080c0030b409001c860221044150000012902079502038680f0984410b040e901092520010b900308035446500c440c034034400010b408814403075682046046441081c140c405100100003240d13489e2002c545092880c8100c00d005102d10303c406841011028800e281902d03150150307403405c5e0400c481e1070340c00180804102c034040000310301e1142945820444d60400e0341e0b41ca407814002d403046500c50b03011000e2950020107598080c942039100f000703083c04003032206400b604040c2e00c04203145010130b0000f80e0105640d0100d100d8203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 373252688 1250 373251438 373251469
    0x150f0e15030a0209040905030c150f06030604030c050109080d090218060109120f080f0304150507020705090403030f06060207051008010f03140a060c0201021206060a0c080a021603080301050f 84
    0xca20755114002035501030340c86040c0c4140c006071540101c8000820030401800034034100710103040001c0c141461106020005802086481a62408d0244039500811850341245c0d1600b010031103900103140080c05840c0e0300d24058100c3d2400f03d10203590f0f070500c2d04603484a900c00c813405600c03440010030100e1900e02c00c0e1106400130381d00c210248800701a4102a400305401810003a034201c2c2d2580d500915a40030880c2540750034004003e1100b0440b1050550700540c2e01190140b10714500880d00030746c0c1703441ca44906441758010a01107018940039500242c8800c0403414103008150319800043d581300002d205803030081000300124083c591182105505840c4030423020500d003484c40c3c580488181c25610310500c01d000d500d402200260342c501ca400d00b006a01d03000035845aa8420000340034a10040c921030107684200222051658040242d01015910a4000340c60f10300d00c88080b45411403a000c100b074102c2c00c520010085c80510805181241d100311405508140c0d0042800946503003a082c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 373253938 1250 373252688 373252729
    0xf330708072f2112041205070b040b090d0306180905030f0406090302030c090903030a05100b04240c0807111302040e160305130201080c04150f0e 64
    0x1003186244124210a80c9100058400c402e0076900250a800ca9914010b010641d07480310669410420940344540b92642144142909106043e0b040c1914004014001015420040030055100e0300800075a0f0501d40c100b01030540503c0d161928110802050f5290f142910607108101e41c1c1074407034051007044c4d82e600d0880c21081102c030507121020705011308080390f45000a02c106001d604008000c1c10040c00550b503110111031850041c141812104084207010310708160030070402840000443c1e402822058000130141d95003c81482c40c2503030fa03041205103d400250008600c0158000c41c034021020042452008a54400903190f100c031503440140451000d116050100304c0c1c0402442420101400b46088807409140079802c03a807123900310220a41c204024800c07002003001c0d100d4650750b85401c0030060b03030800c149040e11f0540640c00003410032000300005100c0908280541e001020f084403851540032100c40040c1400c1c0780d401c02040000c3c41101500c04c18941160360000007a0420381 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 373255188 1250 373253938 373253941
    0xe0304060c1b09141501031109010503100515071b03050a080705101803030c020d27170303040201081e01060f030b0a0608160c110108090f330708 64
    0xc840320b80070400d02021038480100d6078009065100c0f8081d0303101c00451051004200e1403c105070100580018500d20704043c07421003403c18034601d500481c0d5242e002400c03c20f480756501080144440031507004541c104080e8103640b20b02007596030242c0f20891060001450301c121000e604514048c041c880030340a1790100c0d0452011641040052031a2406802621a01408910f1b040240c60a907c0030104540c10341118400381035140c81030245000c454400f50021880090380285281c2681141c3d4140000c9a02c8006d641e00b9040e820f540140310800c2d060341d0040f1401101a200d4204171401d9001c01c05103000141604546500014a81161081000181d0901408907040060302d040d2200707040da10744c1d001103982e840311a104000e24541d03442c1c981519100c0b60031080521881000c2040c07000d040010700004140406503540914280b80c00120350381d41d008032a02d0081001c0d070340c907c6809050f0820202c0b40c0740030300148404e40100d00c036502d031500d43d400e42411510115501000101c0c50340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 373256438 1250 373255188 373255193
    0x61b080d050702210d060803180111010902030604080705061008030d180b190b04091703090307150f050c03190c0908030f0324010c0f0305071a0a0e0304060c 69
    0x740040e4100c5210710450740540b0181c0012820322400200141e1202e40c00f0501c40c5080b44603000e86400f07440c00c08065810b10b8030500008140306c110f01d1071141440f58864007012585000d610245501e6002400ca444a0900b4101b146183d846003109441038080d4800040c1c0c001e00100050040700d003035800452800c0c40000030306000b400c505400041201c140805030001c2541c06008070b016007010000f41c411301400301e107a48103c4407141c0b0007502aa00303282c140d07404200a411503a40c290469003540e96030355182d0b41d0640c114402c80c0c800828450801c0c900104180301507020710000d4203808c108100c2600c0b0070728802d6940c002299901c811802030513a02c1200c04060304100c041c0351550a000340c01c9500c4509031070540c3c0003261030484003140802041510031441210032580b030b2040a42c05403100314000000c18440c4540b00103415042c4c2c94580c41e04240c0300704211a5682c1c5c00211950b01080c110700d40300260b00c1d065403001a01c03424019008440b80740441114100e030019101d4164420f00345c1e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 373257688 1250 373256438 373256441
    0x606050103021e0d1d03030a05011e06120b03010c0f020c040b0d1101032a0201200301170304030812010311150a12020d05040f030f0c0b06220c050301061b080d 70
    0x942100d1341090b1204030703079400c2c0c8241c0c1181d48803809109010b543c580c5004503e80b002c4480590111401141c1610b100083c07010900040066030a03e18001d405510b640c90100090402c055002d60103619000c84004403a40c07110254610380c209500391032004800804101c25281d528104a903c031102585500c001594000c90b004000d0301810041607045c1201070f801107400100d000401095041000040f0a945c2841000c2c01c00b42d8003041d9080d401100d41d20014940414010306c1e900200541c02183c010404100307030390003107034081c140303581d2050131000fa03100c00c001c28070003190f00245060740c64406103814481001e030040000740d414182101c0c070b5011941d0400c01c10010b00901d130708100c04150702c1d5180c05028440c0d406940103c461001034500140005c680d19a4081000100b01c21000084c040b600019003200b011221605803215038620742c51300e10380c1850801c12282ca80044214900d4001000c0c1d4122542d545400f02410b419148251510030300800c0200210002c00094207001d4a9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 373258938 1250 373257688 373257697
    0x51f080f280e010f020c1014060609011b0501021206010309031e0c0605040506090d021203060d020631060309050c06030a020f0c030c101a13020d02040605070606050103021e 76
    0x2074200100301000c5803400503007107440d840e41280050b90009805070103c24100302e803200000501c90f04000c080c1c1c4120300822000d0016101a01c80c8800082450481e0300c80c1c00701d40350021000c150f040d940030030741c1ba00074000c1d400714080082e60002031000485540c001d10079020401c1c0c1684402c0d0a42080e1807845403d0001010b1040034011101e12a0004c11070501c51144103600c00d000a1000d41018403400e0314040340303140c40100315481a01d03010203030320400c4181d942041043d203503c002c40a4910001d280c900410b411802c000301444600f44188081070503410711605118000f400c05038a6040460540e2004900940281e200c144586071905000c001154400e0340d01c100141042e0340c00b070940900350f12043c3c109a0582c804640010488400d01800082c40c0c03420b0400c00168000c0709042c03d8400c0900034007807059818080d0354005d020f07140c044801c181c22015046554540742ea0000d40b0715080304100356145440d02c48013040700d500900c2120481091103420072821030172100d08041c20341c007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 373260188 1250 373258938 373259011
    0x9050a1a0112150801020c0a0605010b03040c090b240d06050a121103011d030a020c0901050904080304050f1006030506011707120f050703030305060f030c010f1404051f080f 76
    0x207807070f10001000c0b002031000e4a801d4014202820f01d001e0380307040180648006811036104503004000781300000c1c030700b503070040d0071500e0340d1801182940b44600060b00115110a04804090351803200440c3c402c02000140325260b606c10381080441d03107440521221038414000c44094001c2da4070b000e40825291941e0600d04480280040340c01c0c10145030302d0284c0801104080019400801d00340711503a014814440404020b40340105550715040020742c5000c80500013034602d03840040442e050150510401d4003400c2c00c0811249551945070038039008141e82d2005841502441c400420006002c07008a80d100c001c0d500141651400d20181401100d000c00c001c452640b2031625400c00108203000840041d070003624002039610300601800402e420b92100c0c5842030f0405511602140e801404111450100b85850103141c8000b0040100e107116a80000358491101c41c1002640e000441c852641e01c483c1c0c1c1e480c50415103586a40c50b10101e415103464010180100034044124042800207040382d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 373261438 1250 373260188 373260221
    0x10f0320063708091b031c05070b090c041805072c01030b060f0301020705102301080a03140c070b0703090b12010311010e01020a08091909050a1a0112 66
    0x1c0002d01ca440d0924a680e294400710700160100141010144440348400080354040c4040ca100400001e803a858101d40843c0a402d1107140309030388510034002d40b40510f0340000f00404a080c2892030035a80c00001d00b803603101d103040040302000c0940003031469208941c0309005044841c103110800001c11040082a03035041140a054503011280442c014001d40c05052070b2072441c00d2860a1001011000c03416600036030041100000280000440c600034041070310f400070380d5003004925050010010311380002450b02c072070700102e0899004903a1745902c2d40303e07440781c1352180c4003052400c2041c05074411040341600030400400030803900c4402010428880e01e400c04820342c40f186010741a810031104500c8031315080d001402000a81c030210000d100f4242481508900b101000070740c0d804082c03100801c1c0c0c5030041a200f00d81d80740da50300d443c0c0342d2614120401c4002e445225900040004039000c80080741801101e6000c2001580302100346441a5180205c0070b8994a800018000031002c0b4000e03030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 373262688 1250 373261438 373261507
    0x1201090f08210f01261507020f01060306021c140a050406020906070b0708010614091c050a05240c07061e05100608010803040506070210050c06010f032006 68
    0xc0d40d401414034440d0752081030620786541000c0039498800382010392021041d03001408214507500008149034900c108044586c40c550f120340c822070611503625001e810b03a60034144007008010180d000782045d003040145079085101051148c40583e0100241c040e002c06e10200858500c469a4008580c001c2c082c82002d4941104800843c009a21002040e549680d14500344001c00c0d42c800e40d2140103040b00d10b04041d03041070f25454006170340301d41160743c0d02c80c00308000d02d1401380006900c503000890b04001551120b40d01805c1007510340300d50b1482c0b0701e100201e04100030361001007116128050788001e04400d007090f0403503446400501c16080c404801d280f01007200c0124200c28041c507480340b143c82c00040305042c40e040c0007070410340040e002a269a001444144440d445800594140540444052100c1c502c51482540e4500c9055000401d501810700041524000000c821017142d21415000c40c50300501c5120034040c4016942807540440e08112150124184640c5140c000e0000125800354 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 373263938 1250 373262688 373262737
    0x10081b03010b04140d051b0307030204140f0a020a090603050c0c0d0908010b060c1504080408010204260610090f0209030a14010c140d1109090709051201090f08 70
    0x5500260b00c40941044009810f20030b0720040b080d114034501c01502e5071084180c44d07a440070f481c1c41c5900c0d000707100951a1300c086161a0340070040b9000030b64019004015016030200203100c080e02c00c036480340a01c0c84400c0814159681ba1003203032510407450b540c180506003040c1007280a0903014204c1145075900740010040e00100380030182d05500c56459030001039143c0415203095940c001c1500e4072400060250300c0241c10003241c007416840c511070011403a50307a503160a001c83c0c0070326005141d903588007280c089240c501040b00346002d11520501050a02c10341400d490707640108480b5241d5207542c14070b00300075400700e1b9080340c49138508158001d8248415400824a89525440161401c955010142d18520000e00c070300303690b040091601070703154030b004000e811311480f0f6850745a0303085603526640040180c1150541d085090010080322507030070007031401441403445006039440303a9490a650440c00005100e00d0212540c02500340034140000e8886a801d42c201c2c1c43c60806503c0240e4100b2403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 373265188 1250 373263938 373263991
    0x1703060406090f0b0102280f2a08150103080a0e060903010903031d060709030f03450810020d090b01030b0a0b0901060e060307020a1704060212091008 66
    0x52503844150b0004e01d0a440c00002445c1058840c2c044031100d083c1800d4440c041c1440c00c20302040c0d50001c0318144001602c0ca80101d500300480729a16690600c80500703496516450240700495945000700c030008024500c0c0500c0c6d944013032000800d030080130407410020a010300e554860512008003528200342c10103021900755200e44070220300203641d500451003c08602015106613004020050403503150000b000f0f00a03641602015002500b08010035003054815410443c165a5039024a0103a880101c005020b0090a610160501d0303052038146c0c80390400c1180072012592190000e0040d080d6402c1c03440020f501440008210b07c2c7c54120000214502c5080b050007144a0020b1b00098070f42403600e24101e448208a09101d4040c1000401c00140d0191503c210800200d65181c0e5a45a80034207a190100242e402042c8039280109107903800c0d00320001c4c00032260960256181481c0c41000c0490a10400f90f02560101101c0184c08110703104000c419404111410b40542c51160b4500411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 373266438 1250 373265188 373265201
    0x2303010501060509281206020408070b07020102061f590103120305150a061806030e0d05130e0108070504140f010e0606040504050a050106081003170306040609 70
    0x400718a00103070070a040e050a14601c0c40d845c400450506185540405a01d5684094816a880c480304465404144a020390459006141d0381044078a010b0399035904080e65009044281d0160107881c000815440418544254092681c1900b008072030030403035503140004906903943c80000c0c0d5907403a24294241d6080c0201c040301c00282010100702c910189944065084c005002ca408252004200040084502042c000f4141c200841c503940c8076013107101800701500105600c5a900321001500e15004401c4c1c4c9000410441007140d9151203590940654a00020700103895200301d4000c10300340c1c0b182001d080c03c02c000002000e07140e5600ea40c1c54040400a811170071071500440e104001500e0548205141010340c5030301e88074035240100c140240440305116541d40885d0700800940d0540e03e03070301200c0184c18028006c004504103d10b9007801401c0900170180842e295101003000c100040110004581d403144010120780702802c600d85480d00064040c1d600301d0389900c808610b5060a00592 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 373267688 1250 373266438 373266449
    0x2120c0c030d020312070f050d090b0403030b04060f1a09090c03070815090412021c0c1211030a180312030c17010f0b0919080f1b01092303010501 64
    0x1000e1403030240c820982059801140c410555204024a04410a000c040294414400d081c56040721000c2d2200303039214410541c2c4440c1c4240b5107800742c8100240b00b00a41c2c0201e00a98080007041f4103c01400308540a40c01960b500c810580030802184c9824005034003030b440c21071412810300714004042212240305a4103002910300c04000c00582a900c102c0d183e40c420440580f990711005103001103181940c0242c405007034886021030302c510480c000c0011070101c0b0540703a005a40444101d01c0248031505c032640480da184101281c54022920900c0b001010300c1808001d1880d00780c4402c3c054601c07850720780304024452100c9800002056a018060307160103140d807070101d0700416101000b090302003980b07131003118003620b903005111110300c9060346010354150200090707461500700f0003e44041e0000d13105500c0d004504001042d0480003040d80f00080c0120021a180350072400c945942502100120034001044040304001c0881e415641c06100084080070000d2010f05101080c2910801d8004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 373268938 1250 373267688 373267693
    0x60702150703021b10091e150201061d01030507060c0c050a1716060f120b21100204050916030e0a060203100f0315020f040b040e1603050f0109050702120c 68
    0x800320240043c40d0740c1c03c1358011281c40700e440f5400540034007668030034001c2c0c507030900c800c045c00b10480c4040c20081003c1c00c040e00d1034400e001c0049100901a0506004400600c480302031210f40b04015104450705803a40240508505400c0c0340e011074881e507801c01d050348c0c00c0e8035000d00001c3ca0744929655401904644212800e54811041000e10340b9104103c032020a200c3c0010800c042a1b0000715001800b5440c03520302c411030b00581e2903502900d41c2c17554043d0b00c100060034075103640154260380d07000003a541c0140c4522440b1821420101c3c011072103004d8005030401c0002e5083c01405c0c070144199002c9003400115110324454644c5440700b4040100c603041c1d800001e0040b220036989600c8001c10000c00068000d50840c2da07604000d000c200b82c0b082c40150003003500142c0d000ca6034295005040784074000c589543d0b48945003001c9010503514085207410b0740c040858118840e005071449040c02c0170981d0f046900c0d01300400010a4001c1c103040440c00b40c2000c4907040982180100001c2040c0d100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 373270188 1250 373268938 373268953
    0x80d0506010e060703120506040e01060b0430022b0c050a27050a180302210702100c0813081501050117041e14010203090f030a0203040506070215070302 67
    0x341c0b049038542d0300107104803c2840481c0019501c4100c0c5484026481c0c0003081c0c0c0d803680e5021a0103000d1030b05000d8019420b0040c04109100244007410403980044051010001400301005490302c014810b6000c101a4105a401505004040c0f0b10305550b054041038440e80398115402d18411140b204aa409030f4030442008039180c001070000184c071402c1c85a062030802102140c443c00c0801d05003445094540c00005c0c0e0030300d41c070b5110443c5905030744010360072001c0c0b500d0000c1d2556401e60042070403039001c130101440d40030000f00b90b418483d03001d480034048041150301680c201542e50030803241d48904201a18500c000e403001203004208000041c03074003455002842c506844140c00150401c80182d2000001101c000c5445411582003a824028012849108101060240c070040c12502100107405189001540190721400c0341400740c030402041000540e8a0340714481a6000503803040c44140903524040008001740c0740300801a1004205070080d1200c00d801c502810f0340540c00600717 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 373271438 1250 373270188 373270201
    0x4210f020c061c0908070204090f060e060105060a0c05101107020406050411091302040519030614010b03160201091403040305070f0302030316081204061b02031e0306010507080d05 79
    0x1d00380207100311402070504002e400300110762201c0006584101d40c5070200c1c00300340038011048441058000d0300a211070a124140b500300412040e00031900307145000c4907038400920101d040c0e410ba0b0310041c2030300d1914030f082404592160480d0810342d07643c0034410040c4d4a2524511682070130071034480340c250315112140100411548a07600c01800780c1c3c10701000080c0075038040704607610304100700c45495107402c065220703030000c0c010f030340126410000888008041001e600203070f10403070b440b9580a1092501c1c1103c21480d68900f88030720b400e1400140003252001c00eaa01440c43e80904510000513410040d0304d5264208003c140c4000c2542c10000c2e06009000003032000e000034040440c03040c80381e1499039011940e240704039000c0c1c3c02501c10081040c42080008811180810302690b0010210301706402c2000c01010f1051540c07010748001003816902c1800032050b5426410703a00b099514400601448050a500081940d810014200824400079580d800500102042e03000001450f1800c4d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 373272688 1250 373271438 373271443
    0x30908010c02030310060507080f0f040306061d0a0f110f030114010f0c061503061410090c05121e010e0601140f1c06050d0818090f0f04210f02 63
    0x4031000700c00c542041041020300314050b00c084080b00c01900d4103c0da44c0030682003c08a6024200700d4410301180010320550203540103000e0000d136030141304100700b0103540c2e03207050624401c8402d00020000e4003d00007000c0300d44070782c0f00e038003210400d200215200324480200445a449000c11890766130303001c030050140a0078519201700c42003080c20910307620440c100e07010340311025001000b0811606c803868000c0b07000c5098181001168000420301800b0700d56a01041203140450701c004110254100006070303001c2a001e4074215180c15282c5a2900043c04502d41006400030054080503480c280d080c401c01d00c889009034020f03c3c2e025407e40c80c900703142c4001060440c94192182028006000503904001f82c98116a42c00c2d1481c400701d87c000050712000d80c0075281507441030354400302188030381050201040c018440240707000281c0c2c500c0e0000b1420804103000a85244010184140004082c02003840075990400d0040a518280c81101e40000841c800d20706010000544070b1000c515115404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 373273938 1250 373272688 373272701
    0x30e0c0a180605030d0219081603030912030506062208060f070212091e0f0a1203090e1e070e090a0c0809061b09060f040b12090715030c020c0a0303090801 68
    0xb00c014060303070400708070000e51f91801d080c840e0700915403403200d030408c20800d00c04881e148039003580482c0703129003513060240052002c048141c524041554a420501d4402c2c400d19100343c800030991801c080c3d086190000d549070640c0c1d503414111403000081840d0f02c0400007144110101142d4005074903000c00300034148550500450390461003440080042c2e85d520b20b008201141d00e0a80d0314280c0850300005121300051507420750440c40a0b280440c0316400005601505402515441c201613a00d0398940d4510208903412400c441d01c60807a44074800c013480d8801e820112038a40a8540408400003a1040c4400d481d4039201c1e503513400020004580042e0090f501040c0d0070301801061400d048100c00c2500b08014501d200d0800040d60141540c420381981c070450001d902150f2644d0312411005060761100800d424540f030243c000402c030b0040011842c0c191940310f07076500010b05c408034040c0e02801e4078110703000941c015580c0ea20385a0b290b00e0800d2340114081d56030805802d00c1c04620781e00b141d28 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 373275188 1250 373273938 373273949
    0x18070503060a2403020306041515090e19052e0203010b04090c02010b09061002070308040b0d060807150c0602121306270b0703091205071707050d030e0c0a1806 70
    0x18030f00100090317a408a089907020343c112251400807501d20482000511025050a0b0b0b041d00c2c006020551034081d0b0300044c121100401228000d0300404003044031810340440080c140d07401049041d56400f050300c030320078150340c060044819006804c119441682c101340c0007031070130b150085010000c1e08018021a0003083d4180000c02030070500102203400d0010050800f40201c4064412500c140e00c204460401145c100c0d0165460b9030712655556102d5005003050031685081042c0800c40712000304100c012a009040c1010700d06810700801e942d039604048003035030020390a0140d1104068044030040c82031800342460500e001c9107281c048200d404040c2212203001c400d0040e8102c2d403141d0007141404c0c54200d0b103540125500c06500b24040d080d04c0400500b060848030100c000d0f03503044009441300c02d00c50b802002e90300b603140112400034040c803000984a940316000300204140251f000d0081c1044003c00e50301080302d0300c4c010940d001c0040d03205181c1c0802c64002d0650391652031262001422 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 373276438 1250 373275188 373275251
    0x807090911090705030f041103190212030a05070b060d06020a0c060501170304061209060c0807020705031506040f20091302030609010312050c0105160807030507050318070503060a 79
    0x181a08020100c0c0001440c211b071161405010406000a2010340032211130b0003811203d40320022021402d20070a016012030242c4080c00c00518520000702c180d415040325a916642400c905440e0030744413240185c00303030f0381210f00d408000c00801c0303542c00281500310b01a207400d003060f202850304034100c0e44140c5c42030000844080300041003440c0801128110f82e01444e14142e80041e40410030028091464020846440c04002800707132a0810a40c03880340744a078080d500300c00d03920b100b4180c480e100101c00049030740440d0001100c5251075400041241d60700703080041c5103030400c801c840c1c01d000304842103160000041041d100768902800c00203400003400b10700b94218249040411441441030100604824a106242060034840c6041e1040411480001e1040d8146850304500384010f00d00d40740c000922a2001031a854002d000d80d0340100160b030f0f21603145030f55400d06000a058201c84501340d40c09411000100f0b90b40810801e070140d4921a400614501c00000c400007202c2d029503100c0c01031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 373277688 1250 373276438 373276441
    0x30f08010b0406030c02010b0a08010606080901110a110a0c08010b030118050d0c03050d0c03020702041812140c0313081c09090f0e06070e0103230c0c010204080709091109 75
    0x20315281d040da01152418140403852965a40007071707002d004240c86141c0c006400700400520000150032040c1110403c0d203e41d40702c2d880f00c4441c1420b850303003802c210315801407c06c440030f8070b90720074125031a1186001c81541c1016040346d48171400e00110ba84954003a139115030004000303103001e1180840d0254804c0d9928a921039a5807055162880c2c92008030600c2001010380041c14050310440d0f40008840314200500d0600c046c000e0001e40080304260300492a0800070090488e69040180c4060f0b0000f0500d5205038207a0001c8440390718500070642c104000f406025840e01d020006030191f44071071008000300504080050f458008811405240719032203200c840b40e6241c0002c0d5a0065520300b40000c03e05074a680159405044044001305e06403144404004407168010054010b91200344c3c0c1c02e01140c803d0402c0ba211103c0180c11501016013100080795451246900903d4510250b00000d401c241e41e035602503042520540c410007d16840d01d0107002001103009114015032011509e903080c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 373278938 1250 373277688 373277699
    0x1f021518120a0306050a0905040c06080609060f0120010605120312010b160b090a020901090c0e0103050a0b04060e01030b0106020d0509060904090602030c1e0412020d06180b04030f0801 81
    0xa840041d559041c80d0344000910503600c0c2d01c25004407003d03000142603400b8290342c44042c800141400c075002d46801490500100da5284240005401110000c2c0780c021640c46100070801d81c0044000e540c1e05002d01441d50003101000e401341603001c1c96101c1700004d0a14a4041480702410420000d489075800c1003158400300d0b422041401e044d5908070b030b00e65458030203001101c0368040303500388050803440c022020481390350000600c0160280c425100e4609030303640c942c0e042003664480010400400c40c150640358095120703611003580003a0320311000c01d44540783d01c04a0b0860f00c1942000d200c1c0303c1040b00510a01c00300845440c0100407502c001d1640420200d401002ca001e00b00c1c50702e115041c00104030082e030340ca07900008105c83d000a0210742d6410131840310301c81680101d107071080140090900380c5000803038070251b42c2210107105031240c4104030b40d8204400f01e80c01d9141201c03065940c0a48085402c45c030949452880c0c860502c0c070085040ca800d0181031500d013510084108010480140302 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 373280188 1250 373278938 373278943
    0x9171804021303350a0e01181e12030c120207050102070e0603100c0203090112020c07050418051c091401090605032701090b06100503151f021518 64
    0x80365007003900c14030f20f0302e800321030840c4000d80d0004000700c50139082e0500001030070f50030040c14425a25115070044001100056030008811140780c41c181c032185030100f10300d0040030358001c83e80680c41021028291a012044940310a1000a0f400200f41c4414001003004000f1113006c000000d000a003040c1340380c500000d5540e00c00b80102448188220082403850b02c0070090200c00304032000041c0000521700c10000c0d1342e60890000d442c0001c80c080302d01d44200807079200f21000700080002910f0114108011f12015008000081c42d4000b03c810035080800e40038032004245000015404a24020142d40101221220340004c48602d404102002c0380d81e03080b426400440c0c0003414450380b80d954503415913504034182078a1320b02d030301c604020106e94060194806500c0c82d204003050101c81e200d00c4103128101034400d40b80c602007081000490401640c01c1100c80c51168010840320400c1e0b00202031030404880d46208a015a0140710100540078540406903408541c804450303e0190007a8010b55 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 373281438 1250 373280188 373280227
    0x920030412030f02030a1505010c1e11120a02040f050915060a0f18050a0b0a090f0609060303030b030607020309030a02040207050c06040815060a06090611010917180402 74
    0xd000081010a2400c50342c040c1d000355202d041c05800071502d900d8440310010103080c440510704c415060700c08002c1441e6000d0010402200c7d0010401e101140787c501d850302e1210410b10b42558028803111805846507a04050380749560005400b40405040380c0c418403081da0242d103400e03600d050601e0100400d104000640308400d9801c601c00000c55100e034808241d0482c503d07001080d5080048501080d121200284419241400c010411460303031040c2c0705800701e41405d1811039108185c1c101c1001004a1908056400140980009105503440c40624101c03001ea61003200402d4660401144510b02030100c10782c0000940003641c5130455880000341c0310306070211700030300c00c1d5400300300c20061200401c01d030515940082c120581d03c6440e134600710790b5072000c45640b004540381400060203504004100004544c12030301c038103020310704000b0180c0781d882e9101c690294540d83d4241160214554079076103803051002c00c4082d0383e031302800c5120040300d203603203400d050040c2c0c0104181145000402e8106 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 373282688 1250 373281438 373281443
    0x131421120a0506181e13050705010804061b030b1309020a0b0f07020402400b0c0c100f030b03150a110d0e010b0117310512030109200304 60
    0x42c1c6a4404000403c00389651a00180720000501000f0b210006502015a807090100601d0543d13581c010744141d8031021140300503c9600019000c200d554002c240c400e82052050401244d03155078104007607641600143c1040000740ca13000401d0f16404e0a100681141c458400144040c0181c1c0e00890700c03804003841404844d0308002580a0000c10700c100759210140d00070000e6591300c130208081c40c50034840d000140b0010f41c501c0d4a2000350f00d401c1200342c1079140007200004502d8a07040e00581940c02c001c041000038020040b003d2100e640e611440d42a4030283e484070f03004c0341241e40c001400c40e203400075800d000c2d40c00704010482c001c10301c240c2c4651102020601066815800708540c80c280160003c42c030141d800d0549007901541c064001031011038080c0d8a03001d804103809401c3c804604151082c0e0411403d02e10072100ea10164290791001da03c2d110141407480d00705035141440c105a24142c80c8900d0404001813002507000e000c0c0c81c4d050100c10b87c800644418100310740e0f00b1480043c000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 373283938 1250 373282688 373282691
    0xa02060c0d0e0102030108030307090b03010f14120a14070803040e0105100c020a090e010f0203040b070e22060e010b04081c090906120506060312070b131421120a 71
    0x1100c9210007075000412100441c500039034895a40e2561269690000d0780e6a001188060760040751098610098034101c49010819501d80e6203004418042a010801031070740090000c1c800ca10000010404005100d2140f41404e82c01010009400c0c02c00d007042d042014030382c0040108205049031004500e054a10071103d9104401511005036020310246900a401035800c02c17001440d442d040c0c1c4005002c40040c0024003032030700803c48020882c0b008030b400801c2c1c049180d011420041c8141074818803820003909240900303480b840240303c07080300011302e01c00140c2c4501050082da035141c460f036401804080280c0c0d04043c100707a10141c0300c514030b5090a0701e91040050020f1107a2248661400500c40c0c440c00b00405900d40340384440011451005485074400e84010a09030708001410b42000c42c03907040d882d401d0007503a95481c0920f42025100001440305294081d003c40d4503a09543d00b20080e980082a4091000c1e4403d41101001143c006485c0028400b0014003540484642d0780490100340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 373285188 1250 373283938 373283947
    0x14181002060123040917030106020706030203010609140f030615040e060c1903020d060609030203062a0a020c030d020a1e08030c0f071a2e050907120e0706080106050a02060c 76
    0x1290040028117006050208410801c0312007001e0ba40096050b504507500b950200350b00c0752826016440280705100c001b410a000801103151808540701d0108001012000350343c0190f03001a2800d042a200c581407912503000d4805980b405204001c14404000050601440c004a143d2218004d0107107902d640c1c081c00f2030801c034441c4203604036044075800c1c5204000300c5895202c002d00b0b07142c0e10b01080b80a0301c240c03004103451542c038041282c034905010721b010281001700b400c00103258120103060010740c410002e2001440c0c1e41400030090640e01c503402030003241400d00303003c009000c10241d40304c00c11300c140d01b0407408207201d0380803258402c94032030b1003507540c0e1241d205080d054440d03544003a005401810007140c0b03c071900760300b0501a1300511446041c05070300c400d40784144030a0505580625005c0c0c0c0c0304216608041e51115881810b905041d8031422031050f81c142901d0001c5400d1185070006081440080c0e003090a17280944640e00e8124181014101d0196461f4000750800b08506800709 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 373286438 1250 373285188 373285259
    0x5090304030c03030e040507170c0a0e040f050610050f09063a050106020f150606130305030a0f0f1704230f010c02010902030319141810020601 63
    0x484005591080c84100c01503601e00b40203003c003014070034851007039040101051030a4409c010640751111001c0b5032510756140c0c0c25110340c1c150300030a121424440089410720700c6541d0f41c070981c404032440d003001003603601c0c08030100459000800c40ea001448010701c02410080d94540558065030343c2904c080e039403400032884441d02d0032124682c0d00040e50112803022050f950160b1000c0c50051030000c2881540d89808c4117a84880d4400403419071580068048940b070140d001c034080d00032001800c2d45250440c030105d0040c00100c150400d0711107900000e0781491844d8040c18000b554401c2d45001a4450300c0e10b10000d2641c10301411850002e00b8080c0440d00b40210101c4482e248041d485640c0d4214a41e00d94007519004881c0015032079510b040c0204c034040340103000709440c03aa80200a58903010700e0158508100340c0040122040000c41b03000750188960050040c43e0b1707045280320740340f00b03013242d03d04000d610610b00200307008540162004208001c080d402070b5000300341c410724050000c0b9070103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 373287688 1250 373286438 373286443
    0xf0303031308030a15330f050315062205040501030f0807021f030e0613080a1103160305070b0703091104090609020d1a090a050303010e0601030e06040b07260a0509 72
    0x5407001100c00c0c4141c1c4001607515441b80c1e440f54540440e0258030a41051803403036062901c0c006154030041500c0043c02181e0700c2c4a20015917011809000168845030302801086141e00700380c0310340d01090082c0c50141004282c01c54a0801044111414003440d815a5038030b0035a44c0c0c000714014070880b008a220011540c1e05491104101e1512180540758112510300402401c0340f900c546040d0b010341c0d80030801401802104983c0f1a801401c42403a1260700e04c0d08172001211044000ea10740014480307803030b42e460020f10950661b07009031344642d19400c01e070801d00090751000d82580c0c00d1600d0503c1e00d1000455203443d50550072012200003600da1198100340c2c02910603c0310003903002c921020640704205145060020318142c50007400c002c3d5840c4415980d40e0100880054503c1d403090004110025a0011699014006250202e4502586056245400c505940407240f107160311b4200004a0703844265604191a80c0300c05110314200d07142c3d11841018050f1a11070441e8540c00014420304c400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 373288938 1250 373287688 373287701
    0xc0807050a0213151a071e0804060c060507210f021b01050121110d03140d0b030f0d051c0b0d0b06100503070f120e16050f0303031308030a 61
    0x1c0c104903484540483e00070020a484103a2100980e902c00e00410a9075600b070011000b0782d115050b0620300701c000c0d15008030030040b031864008014000240d81c00096030000181000700055101d10440481e20300d40030054801c024001c400700aa030510075000c100c5806003100ea03000c0070000000e611010950190084d100f00b18407050403400b100e01030489110b05501482c101d400c0840c60424140c007051600c521000c40c508054106010018100c0e150318118407101b01c080c4c464104507000170050022020513410607688002000d5490900c90514101804100420301505000d0f1551000072035029150b80100d1400682100310030440c000f0340100c0fa4070221114200070902c1450017075503e080b03009480b084501c03c0c040c0c640f1a240e100034600070381c280c0b801515161144d807a0f100e0114021a07030b19003d20a00c1d0100e50f100c82080300ca0850921003081500b05d00144890a11304103028000711408a1440741d010360b0081003000110302155803119241507002e1400c59990315115444400b4054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 373290188 1250 373288938 373288943
    0x714010219020304051003110304110f2d1203072402070506010f1a040e04050115170f0a050303061e090709090b040605010f0c0f0c0605090316060c0807050a 69
    0x41c004420841c079400001a00442e00c00b161080c40c04140340400728280d6041e50703010070070440305202150002c2d4082e8140000340d440a800000c0c2c40f9214000507000020a80d500710303902c40101744602011914454a0540407000c0d60380441118180d0050fa6a9200303c56024000c4d00420b01c400c110540f8041c0100b036000910f4805544031041c0c0e00300301c1d8035a2001c0c481e030071362001c0c0c444001868000c10801c50301030b00d55401995007000d01d0f00503074415522001340704032138956850780300c2101e02e03240030441806070020050140b50001c00d0b50469161107110384d00040c1e5a404044088000307500042101d5110000340c90a210a8501c0070b03200e001c0c0c03488080c900e40e01010380c0080085041e400788590044038030440c02401002d59a505010031a511402068009080c0040c01941c090145070100d0009108980d4031800e1981515080420b2286400c00400240c2c0052407003c14941000025807480c610920b80308200e10b462030140c4a07012002000f40315120120307420b020b01c4002c0c40b000c84200d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 373291438 1250 373290188 373290217
    0x601020c1f1701060819110a080603100501030c1409060a050f01021e06060103060914220f1a071107062f060601032d1503020a03080a020106051507140102 68
    0x141c481501501807203003107a44a400006490030b0701c00c60041400307400d894811f8041d09034501112130f00f007292281c030028205d540511607181840d00f003500901c15035000390301a0301e80c40405400c044c503400e0703a030101c0c1506034410100d00c014414280d8540c2c41c94000c403401103405040c03400200d00141d091404481c00d40030f02c14100c3c00c9941110340046241886200d09a038200b04150300e5012620071580e549441d842c0c0260158006a031845070000c4e4440c00c5501e510a000f2450f41e00d42e20006408840402200c13650000c10100603c07164100120741c0081c4282080100030480c1030400e030365560544190020010242505007904003c131203500111060340c40c140c8078004020510599480341611040d000a00d44550b2032601e29664084030154201a00210319000c089103011021300403940c0c040440320034040c00040184d5176061108011481007050390b45074201c2110180c21907540e940520b00a02e040098101c04d114080111145954440303803a40c1401d5004031010300a026400503980d091 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 373292688 1250 373291438 373291441
    0xe060a090b160b101211030c150d050f04050a0f110604061d01020d12050910090302070f09050c0a0c0f061503140304120f1415010503060601020c1f17 66
    0x5804050480300300340e005000916090719a03034489003400c0c10300e1103002d071703040c07100c401c00d4002642010526000040c0101201d5401c180440060181c0002c04045001104009025004821103026590b03005040121040f800d20f45500c501e40c40d804a418000c005400f80c100002c1044041403a800b070080c406000c1c1a01c036501d8200140400100000d8014250311035074a00d480c5601c00240c0e500c0009059030b441000c20302540e1090054100030700020914094106c1900300c1d0905c0e88207000a4900950040804528000745503c03240142e42010800724249000c005410f01c40318100c4c1e0407410369251a4107032881d00e0518014034038405070005c0c0441d040181c0301c5014480c055046003921b00594208128100c0ca00b43d0907900d100c1da11864440380a40218180441c19401c1c075080c03058003c0021181e12030170400b1860070004110185040c0e10b203400018002d6007003c10500e03500071400e00040040c00030030b40004400414844418080c070b0010039610000c1c0d8455084038815451120044909 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 373293938 1250 373292688 373292707
    0xa0e120a053c0403050f0a02031b010c0501020307200109082502120303010815060307051207090608070f0905060f06090301060e0c1801020712170c0f010f06050409030e060a090b 78
    0x315803044c031056407a4410b40240845c003190229005040e2a40280244610f46282070159036910a5288030381c103014068807070705c0211b0000c1c00114402c400581c0c400740c205c00c81c9408500e1001c1c0703048402c1100da14140d90140040c03405002c03584550b0100d44002003040c1d021641d80c0c0b0620645c500250005190800b1908610001000e903060f181e4100c00d5409001074030440b100c4001007110001c0e4075a000300010402d42c180320180c6279090240f4003c0da211180c0701c1c0503982c15642280c3c001c600740d07840144100002d00c803211510010306000f030010302c1700d4186940061841c840c40190184182c80010380242c1a640c01d6012000130064285200818a081ca164a91540206100d81c0151102004c4801690301c0424650261f0f03040d00000c5800000d039881750020a00500b07180d02c0c44003820884007850750700400000c1102100c03040086440681907c0b0300d03090300d0190b4040740c05181413211610000b034004046a01c46070342907608544035003820b80c1c1121000d0095000d0440d4490001e032640d41d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 373295188 1250 373293938 373294057
    0x15080105040f020f0f0a020f06100303090e160815041e110c0703080306131404030210020901050405010309060902101205070f0503040201260a0e120a05 67
    0x125482280e0401082c10714103100001d910641d14280caa0b6070041003040304030b058820240840641c039104039020040340000203881d0003000e403400c1a21400752017003001056804a030b2507014054020781440c86040c514000b01c04c02d800741307203440c043c40751040005011108403480058403940090091224904500c00c1780710765a045030300c24105d60b05203140c00070607041120889091044034001000000d1464651002a0300058001039001c845201035410030307162030103045195041ca58442c400303420b0a02c1d0203460094503140e00c144450040c0503c441c641e8120302903408640003800d011070a044035240210082c00c68880007507002d40c440c14a060501c0d8002154a41c0043d105410401501c80b110180c403005100c2e000e0703500140c1308200017801948664208040c03074403000e00d00b1040030b89144a1500201003210100941d40c0d5179096005511410409452040503220b2100e1600b44001f0000b8043c1c8115071006600045120520009013000c1040708844d0340e00000481150f080040b1145 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 373296438 1250 373295188 373295191
    0x80a260909060d0203010c031d03090916140703050405030c0901050f0f0a0305030d051603050103050a06110c010c08070219020904060c0203040816060f0206100e0901020c10020705070812180a1508 86
    0x2004c9c80740203244180907100c0001120100c0100508400d0300780d507001450b80c4040700454148040210034003400c50045403141c003401c2901c0c441d45901da00c3e10f090005061414501c83d10742d52080003082d004003c1900c9174051484e4151050302c20b10040448200030505013100c070b5000614510000901c44902d04480d03100c14010000348800e412208144a012015140701303000240090300050300001c0010400d42c4001c9a1844410b065400c1c00505d84885003114203000b43c0c030000c185014200003005905114502c1400d03401d0004004004050700894480d4900502c0140804c1d0703034074405035405000b0000c2d10010f0000f4811120000d00412042719503070743c98840d5001003034522400f03044550000c1101841a01c24440514509251194103003c8200181c8282203e55007003100b2510a01c045c0a100303014030a041c40580da030009894082d02d0042c00e580a280f46030854101c40241004400c1214035000082c15074016541640d400911300003544c2d8420b41220340314080e0490b68507003044110f13 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 373297688 1250 373296438 373296461
    0x6090d050604030f1404060309111009030209060604030b0c0c01060e09030c1b09150f040207031d10051c0b1011010c030c14031b04080a260909060d0203010c03 70
    0x1842c0c1040040c4e0548244a49011a04a02100780401c2c00980e00c2540440d088074010802c00310504c4503000418102d1121502d03100015406010510a608041c4c2c0d525400640590b0494602881c6441e498141c1801070105a03103924000307400990b605094001201409501007801d2140c100418559a070741d000c2c1400c1d103518011744070300e100c0c005c43c1103008284020b00540b00d5030300c41d55900015070400810741e00890707200080b040307100c000e0788072403000d000158425100d80d0740340000a689035840007008048a881070783c0c1c00c0070034030010f58440c081e0703010701e80b8600200341c00e0305c6000c6101000d8071480b503032540c011540c5203900001d00c2d400060f03108118141030007042402c035940011003d8030f00220409001c1a00341050400000c0840d0045a00c255252590111024a00b044000d00d50042d445208154088a50001800a107105e0500c251800203c081d621115512040034103004a20031244035818141c0000c03002d840f200d0301e0131650755005000304402c8824070070141c018103120446 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 373298938 1250 373297688 373297697
    0x31312020105071416080d09170901090506070f0f0f030305090703020a052101050403051905040518130501050c03090f151506130b0d05060618040b06090d05060403 72
    0x1422919006101c0c0a0140a26030355000c03040354900c0d03800110f50310002c40c0c0421040ea169503080820413040103010360414980c0c1c040354800e80c3d414004a161164100b0142d554410400c101c0c1e160303000800c4008441c02607440e16104d440e1810322014645007403038050310000c140074a50703080025901d001705010707219840410050302c0d81c1210a42c0d80c031942c003000b500003000640502a0340b61214000002e035000058140c2a002c41d140100e003075400a443c100c01007040032404280c2440441500000071115180c180c0c2002c0c540720004444150800c1d4888002d44110041120f81801403100540b0315081002800141086030b000d00f01035204031000029409500010104070390046010007014540302041c040a8403404415002e2414001d1440e40c05a001c21a4102861502c0f40145c0141030000c2483d0302e605480388401c0a4031401000a44921401c2214450b9003d204400755150201910000380f603488100c01308442c3c1c81040c09095000207011103200c00c1190000e0740301c0c03160f4440e688 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 373300188 1250 373298938 373298963
    0x2512050126010e15060a080f07050102070e0c0a140427060b040513050a09051204060f09061b1b0e1503010207030c0b1b0708030a060b0903100207080d020313 69
    0x91035402c072641c03622500001d410201c04a008513800c2140701e9040400200303040c4100d0b544a0300c6919080d480c1c144074031b0a42100030100450360701440034100500034600d0240d80f920702500d1802443c403400301d002c000c0c0051a10070031000c40b0301c042580e000d0a2800543c0044401c140384903000890407c10513451903080420206a042042050b50102c9002610002171080c00c10500806801f0080020071130541e07407007401020510802145e11a8044041e100c0e0392581032140040415085000900a1006c1c80c18100a0150b00001e40382d885a840010074501d00110729080250121100c05080c07841d006c003901140b80645501c1e818010303815842e140001380714410606003070380218074002d0086203624a801e004110020405688040c01e00407080e1151400052041950003d40b008d5480540100400110381c504c0d03c518070107000340d103192504204040002176614140c10020003072843c0c000c1801c6e0b0070000703a5001d403804040f0300c15040d03481e0b19000d403801e0b44440014005a40e902008003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 373301438 1250 373300188 373300259
    0x140408031803011808091306060807030e011e0519020d0204050103151212120507030506122e0603061404050d0305060907050c15011511030325120501 66
    0x450558040e4486842c180b84044c16140c02d289908403088094104881141ba55100180e03031103108064801d40c0c503a02c0550130202e40042c00ca4800181c02840c981c500340441d8135110103003042c018150090760004c1860342e610440c001c001e0050403001d229450001c2001150042940c004d4000c0e5402030741c2c1008007901c0d15100c51420341803441424042c004800582c030125000c16030402d04195103040641042114500450846e1000c40b440c0000940e0386051227041d00c1e240f118900e400b0f90400041c41e074505100403403600120384048507104807032081ea4907001c04280e0f0300890000c68100c80f08202045401500c60301070310b011601100d135030040a8130300d5074080c060710a60380110805003446540d0780ea010740507070781548400100c192901c00c1000481d02412000555400780c40440321000031f01188076000341808091340000c0d40d154100740304003d21100040c1d820b83c511052591504081803038090250307100d2407142412884942003c0c0040f848101060141c81508845400c0310381d05034005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 373302688 1250 373301438 373301441
    0xc050310060e0105064b0a140306010c020d0506070305010b03070f0c2a0302030c01020d020a020d210f021c0e01120b0a030c0e090114040b0714040803180301 69
    0x60045050b03030300c86240180400c0c1401ca000d803825045a0180000d12500c01e4115001001e150718034448403445d80c1503180b085019041c503e00e807941100e4006013007806500e4040c2c03d10f6003c040e02d0503d12004000180d00780e100f400310340c41d040d070050001c135107510a40c10b190b80c8032401195941c0c0407a0034500002400c0800c5000c40c0d11540c980e903105506d1001d00b5804803056960b40009507403180c840c00300041c04100081250000c03421100c0c100d540c85145105143c10410b04039610307815900140802c034045500030924450707050f4101c4d04030200c107907603140c0703506405240901251345001700c11109400a41240150304044403903001c0380d400303164120030f012411058444200000c1e140c0c0604102a50080b545030f628072410b4200401c80102180204840c250340e83d0040e5680c840900041040420040f0065040112240244200b1035450654038401c01d01820003005014201d000548451140c18040a00c0e811200002c0e0349070340c5d035065140d69401c03007542c5450305980c1d1b4200100b5840d05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 373303938 1250 373302688 373302701
    0x11040e1516020712030917030702011806050409050a180302100b06041a0d0605060f090157110108060910050d02040f020a0512010816030b0406020904090c050310 71
    0x20b600a000e240c0c24600000d44019503100120b050040e03040001c600a4010aa0950411980707030045486610b00c2c0001040c1a04055081c00c500102e04818010617030702408550917100c1d510f801190b0b075110500c1d050000c20041d020050b07403d000080c4102003660200c1c2c1c2000c800e440002c140801c400903004c20050348180e01c6040b1403113868448010030710340d2100290130b81004070000051029561000708030700783c2c41381c2e2010038100c01c00542c1c14859a08a541e600f20340c0078584c0000180c40d0a028840c011600190400306c0344010010485d0300e1065181500a050440640745010070882e858001c502c11107a00c01e0324007088a642c0040c0990505001c401d00c22001c505602c0382c007a29020600240c1800200103a8105858010420300b40da0180003c2a0360170013540c40d9955101150000052540107800408182e000021842080116030182e0800c0d6a0010504811a100d5280c180002d10800024640060801036040c0c14008010511021104181c0a45042c4c000f101d803000d085801c1d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 373305188 1250 373303938 373303981
    0x210a020903101a09041e0311101b050c070909051b060c0a240203010e010e0912030a0209130c0306030b160c0b0903070c0b070c060801050108040f11040e15 68
    0x410510031a010314120613244d80040c05850781034200c08000c0c802030b09200001c102540414104100c200340200d0801c00c0ca281c1c848181401c002d030380120010a4500741e488041502080000714846e40201c07000c1c00204001c00028108001c0c1a645d0b140ca1a00d0311401204103550b042640000301c1c2906101d811a8462210f0502130b01200f0f10313964400c200c0078070840541182c40403038035011041401c54802107010b8604809452070b030b51324046111038148001460600640c000800b280803403a1a042543e4210141200258440440401145541c1e404407018404581085901d42c0415055440880ad9a0050080c40641e03990980502000700003c1e04810020340301410041c0800c1c006030406800c609004141d038607002d59511401035401d8190818281c00b0000100e0034200b018885000b00144094200044250300d000300103010380d4002000030f4950743c13421b515038040180c200028040d02000800030810000c40301190f41c0d840906070a03d043d908601c0000c00c0c583d10004181100e984e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 373306438 1250 373305188 373305221
    0x601030b010e041a10030203090f0c150d18030e0108010b040b0f07050c0a060908070e0c1b121801030b041802010c08040f0611010c090e010b210a02090310 68
    0x40c240000e110081c06004e007001d00703140a0b902c2948441d51104201000d09001c0d80c3e0250300c030b041c03603681142400c2907140317aa04290302080c001d610588602681c6048194035000b415101c4210183c503801601c1c06e00404840d070740b00c2c2d00c540302c01c2640010600700c3e8100c0a0b620039846030780720314040410b803246000390b0341d004100b8005030b001412850010b19829124405480c10380740c4040108080300762076000380002c610b06040911580300108114001402d41449000305820402c1c110034203441600001c2c02d41c0c01c6021048044000300308000c200030000044001e13540c03540c0d00e48842c0100048180c46001034241b994414040c0f0380380c0030b401840b074801103034512403000070360041d00c140e138088a04031542602803000040d28244454400010091038486403409203002403000d0844a08001070030a004200c1002d00c080d9205002007410340307400d400718a40e56030180c9120034200b00511500ca032102d00c0041080304082e06a00540714a8005138100ca01010603400317110203807840c5c1107960421342c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 373307688 1250 373306438 373306457
    0x303131a07140d020d14010e070c0c05010f020a23100605060f1c110a1b0b0610110303150a0509070206060409060e0f010b0a090e033009150601030b01 66
    0x224910002c000c00742d5003400040c17410341c20007069019a4104c00342c0101017242e1500401000300507450081d4030094500d0070320301c80c9000b6a9401c014041d2401041d040090840700000c03987e008100c080300c00e540004010341c1c500e440d0080f401a0840c50f000c10781d0140640a03900308242c101d4043c400c292500203001a0420004206c140c03000d40161141007012100d0440c0e84101c1c540c103216000060100208240e0f9910142e6806051a500000c00d105411a20072011000c62400b00c030003a0884411279102c0202000c0310300031500201c9020380802c1c0e41c0000804d11503810800c10085240d80e506540c0c01036099038a03070801070311103421140c1034090307084003000990510f045d0f809810302e50711927100000c500c8040d0104a141605050380c1c211079a5503800798402c0c43c0341c81045880200500b60003400038071519880ca94423800b848c88013003120a8040c0c00003006002d1524007080621259095410504d41000001da5841c80e02e801c60707031108909800316503179511a0107400d040000607190750501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 373308938 1250 373307688 373307717
    0x110a051c0b0a150605090316150f0212040602070806060405041a0705130b0315031b01030209130908040f090b010c021309060c03060e01140f0d03020f0303131a07 71
    0xc400024420b040b0300d65541c103225410000409144050441ca80c0e51035140d507165400d15242c070043c400c0080c80280032000c10010b414460555904144540c0f0741103203074080720b0710b007680b80070740855140c3d0208401080c0403a1040d8000782100807501c401c0b08a03400c5450700418003003160b105540103403041b418607490150b200d0604440a070000480d141c11481c0100303424043c8008aa1074201640c0a4000400d21500444da43c09030342d2203c000700c0c0900410421001c4d60806a001245071905158011a4020140d50364040c40e140c19151000241302c908800d2034081c83c13507400f6006202049080354130100d80e480592098811160068495400c80f449907000c105040004a82006a181d02d0340345c8007000954134000d080070b202403910302141841c10a03940d80726440050b007141c440c18000380c140c0040c44d5600d402200c0207003000d5400301e03140d084901f41282400300540d00d000c5648400400d201071848000701020b0814040c030061300000041010030001e44074183e40040c0080d44d4207480070b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 373310188 1250 373308938 373308953
    0x9060d0302070504020406051810091a04050402030702030403051006030c060804020301150f050f06030906010e0c04080703030c03030501060309051c0314010915081207080a050d0207110a051c 84
    0x28103029004540071150b0b258001000d0f42e1043c2c11450010780e000c0b4400e139440f0110880080b0b2144200c0b041e049003040107600802c560086d10440c80882d00d005100d5948030300b40e0341120302600c00070b407040d50b4914240c2e60207996540280702c11600c82c810b041500100d01040d00c46c840640ba070003c4480d126518114080f40c6022002c1c0c000e0760325540e240d00c0c00c4c190040540000e40100700c12081a0151850002007003a884820030415000700c400300208000143c0224801e1f06450880038026a02e40780c4120282c010301480c0c100c03003190b1103591002701c12305402c082e1301420b40b0306c01d607020b10443e03880b08000c800ba25501e030700080c000da0000c402032134120001d010100118540303160004050300594001c0c0010882a446210190340e0f41d10880321a901c240f11680c040c1040e88014680e0320310740319081c801841071200103884d818010444824152180007101c112900c1050255210322143c1040041d203140d4424049c031902c454a000109810036602d0454400f9040313950041141007512086c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 373311438 1250 373310188 373310209
    0xe010804051b0f040c03060f05060c121e040306060509010b0c03030403111c0507050f030a0503010b07020f09041410060501020d0c05070e0f04031d06180103060315290906 75
    0x40e8000c2a400b4104840d844078403815078001003d540c0422480c0c45d200061212188c1504018010742c3c0410101c02801e0300040e29401080c101e118884e9203007585515503206031304490821034113030b000080000030300c4459044102600c004850001007641d0b2090f0110b1640b01c1e070050914142c00920006001c2401428207504066495098402d080e69071004070410311031104400010540200340801440000c00218050150340c5000354504101001c0203070541c00140f040d090b444000040050854603640c05400101501420143d51828a8580324200341c51450001e8814458103252100022440c01000204c0e801a00580b034003000e8014100d805d1180300700c040e11304ac0301c0e46500040b103d16030b15900d8171418a41a918030541000d141c0204500341c0d22441c074020301da500011601c0d9648541c112000889448403603e01c00300054016805401d00d6030000d04041c1080340c4400d90005aa0814404001401a07000303d0b0008013241b051481890000d40307401032108070008099003050389411 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 373312688 1250 373311438 373311493
    0xf06080601030f06060f0212070b04120203120c0a020f070e1b0c030705030a180807060c05100f020d0f020715200a020304090c0203310803120105010e01080405 70
    0x1140e8080320b40f03003000c15142150301003030020341c3d030529400b115941407040f0421307115070fa55520715050140d1510a00c0001c090006004078504a6409074014020012030342400c0081140c2c2c2160300e82a007824140f0f801880c4104050b00907100100388091001c5a40c02c29100301002803049a181d1840b9000c484201d400c031040421400c1110840e00f10041003d8041144100c3c0103680d0340c0b444940042141c41000e80d540c0106030745500a0107150808151042904e48924020f45110744500b00381d481c143c03010007020080342ca443c046000800c0642c000301000004120b0600160008800450803407044136401b501c1c40344840c3c0100510400c41d0480350f1440e089508031031288598004043c260350080c000c0c81c3c056400004e0800c0600003501603201c8025460020750700f010845c0790351640c10307500c00f108403200c1124484012004009111f14001030507a90003141c1c2c5a0300744803429402000d0078040c0c01c1c045030448030701d45207039031284542c01d2042e03600c4400b8102156800300054a81540040d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 373313938 1250 373312688 373312691
    0x30f0c090a0302031b0103061a03060d06020904140708010b090102030d0903210e06010b04120213060b0a03020c01050105030c03120a02011806050402090106050f0a140405091e070203040f0608060103 87
    0xb0140e0350401138214100c0f101840910b56130146000034089428641c003105000c081300c400d00c0f800a901c0c0055a41c001c00c20745008441003198601741c030092040c41c22080c0c1c4985059006600900d8400d0307607a00c200700075107a05a241e600c840801c1d10500448158600582c801c0088048055140c1c000c081d4480c0b0900385440a101c00c0b1000c04c0001c4424095000b14507980d80311566548010868240103081e0050b05c140341905000a80b840100400c00c041d004041d03150219440d101c0b181d0200d03009100c01c504050302d03006113510041c0079500a40d804960b540c2080008a16803074003080011003080c00134000c0119a00d0790626504d00d0300940307118415950782e0a0000411030700c1c02d14081d89076128010029452034684108081100c042e042182000380a0220340c154503070600840300300c18500c4c1405984044079140780c040700d1107144c00c002d41104441c0c0901050340e00845015800843c0080018100e544040007281c1e6805107210305007494020750310401689014046054000c0010707d030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 373315188 1250 373313938 373313959
    0x15040b30030301080a05100b010f0507020f060412051507080402090a0b150a0f02010b06040b090a120803041421030c19080601020c0103050105131d012906030f0c09 72
    0x305040d50000d90005480350408030400c0101300c0c0610001c580f001c04040100007103000c010008092031403400c0050f040c0708000403c40c00303540d101072191a80203001000d5540d15a00c2344417494207100d807941d04032210b102e42607010002040302c882044c1b00300060781d50180c40c0e41c0c450b0200202200f01400c0c1504c4540d503400303d840a907d64440b810f10b09080720a0b07280c0d47c0c0650000c0103015189141c400030441e454604e2180f40c0355107143c212402c81d12030302c45040d111340e14040005c00c008c94a501c20711800400d204520304108289010b10f10850007082d0f455035100c60911001d40f00c01548502d802015102d0341c181007404101e102031900000a20031050404100c0060103030303024402682180480c41031401c0010729030b410041e02264507003c1c41d00b270080c0d5141c00d020030b68400303003214014810f03500d0b8035580c20305c8040c076920040d500c810741c4000e1214040c00501c08074055040600540580e04030b840c806e040b13003081c400300c80c0503c01340340110305a542d8819268401ea00016401c03075000c0110f50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 373316438 1250 373315188 373315279
    0xd02030619090c1403220f1704260d050a0210060e0411030d020a320a061b0905060304080f130e0a0203090a0f051006030b010503010b0307060210090206041d15040b 72
    0x651070600c0c0c1075843c802d555641440092030030f01407641c81c4080b0b2b29188511801241102040c3c18540b154181480c0307460b554034070010790500664450a1010750b00e080b000050071400300301c500780601c0c0107840e40707038034420761740203060b00e521499440e00007603803004690a0000e6240000d443e40420215010181e003044040c2000f10110210825040355105c0070500041c899240300321010680c021141e9404402d0300c0c81d018140d00100d105851003841c010000400b0720500400700c8401031052440540da0b400083e405042200a40c0180e4034002030b40c100154520080e4401c9a001700400d6000704180034a0f80d68000c0303582c0c00148200c0e518012400f17a4181e820960240346c01661050104001540c14a02811f0841d040c01c44800d10030307413101c0001c009094011421500c481250a0007085840c11070020817120f1103103912102d0031110a440e48820b00129003041030242044100030188144450204403ea032200082c2c0d075400400c141c14401940000558440c040d0f00340040081c80381e080382c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 373317688 1250 373316438 373316453
    0x1803120103050d0806090610080c1204050714240c070306020a020106080c09060607150b0d0303020306010e04060b18040b040c0c1a0108030d02030619090c1403220f 72
    0x281d100b120789600800d42c862240e90484c0a107a442a0143c4810f2001d00e452400a0b925424180301e9009200d8014045200400301e0800c07601903650021141c22113003000c0c60500e507207460300c1c4115000c10f07209a2b8112254501408090f03000d43c0389220b41c2409103028840c40728250700c03c1c000301c8014811041d0000c001840da00142c108180d10ba000082d050f45042d8009060016196816124084c4d1008001c1c2650300c041c140d03091075821843e0308100002c4507051600516140708401d6000c09450503c904065241c0c00452041030281c0c2d581000740500300500c419204540100045084244104590087d5001808101079001030010441524000114080302c59019160b80090040035005040c40000f00e41c2d5642c40c0d14140d071900b002c0d890410b01c2902ca004440000b552981c0003c045a029502d20402c03120704036510b590725202c00d541e65400c000910b00404450301080c691000c29001d503e0000c2501d21400d11404600f840c190042c6001d080b0a000c010304880380e00201c1940d0700402d180303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 373318938 1250 373317688 373317691
    0x6090b210a1d010905060f1308030109090c0e04050c010e01090e0901020c0118031205060d2a0911041514070302010506010206161b02061e07020f030703020306180312 73
    0x8840d000500b03030700b06084400040360058810b05690703040c0303945040001d80005d040b50b8050400744c41c02005407141c03c01c010140c00c08a4020b4980d9a0100001c0765080c2160301c40d40310f041c031492007001e401d0b40c2d4031450304034480200d4010f4501d410160001004d9401100100403000c5c051420950301c075111000041d2013102512700c901e0310b80d40801c102082e814244a4200341010319020080741840a03035000b4000d6002020b4080c200b900c0d07402040c12070703e600c040102c41319401180803038902ca030111000c4424042c0e81c0070018180b6000d0000941000078407408082d068003402c41da180c2420020220b000e000300486440170041c0103883e40051418240207007014501ca030b8004525418400002854205c01400840c0b03444010505918520380007400d80301101013144566015000700d0000030600d000340c045400070400f5090983c0c3c100c41400c4010180d5900c2120f4041c44c1c1740f41d4078145940c0d0141800002c0d0581d11020100e512120f940b0b141e01000782e201c20031a490404098074640b100d210 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 373320188 1250 373318938 373318951
    0x30501060807060201020f030a09020f1806010206100f1403030412030504080138010e1002010b0111032a3c060c0a0309020307050315061906090b21 65
    0x5542109014141c0c041c001d500041c14188000d508121002408800354131014002c0011550750700c070707094119140c403c1c00c02080f00c0001c22501c40d1184030700710788242c0402110901c2c01401444005103e1070364488201095915404916a000f828080007140510302c1c2e060300d561510060200151007803503d003038424690710a81e40c80d40c540b490f00c0c6100b802d40e40e1401340380c8401e002200c000d040b40030b9884821100e0109424065a2107000d407030050b555562901d0700c060308100e8260b150248282c054010039890802a07a80028110a200c5419140c0c0200881d080069800303a4590328400708103211180c0450a1506a41190800b100039602c0416800c0c01600c001c07a2984904400c1c2031160700042e0200088000740002d0728000c1c0444256102e02c200100900d5541c1f0034080035034034100180740192202500f04d94803452040001b50310004c00b04d400314445c034681c1c01d04801050024100c002210803503102c1540150415407102a25084600049a906040030349941d80d82c000c0d4440358024003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 373321438 1250 373320188 373320191
    0x1608030406060303090602060c0d021602120705010f020613060902013c03141603020705100525020d1b05011503060b0402090303030f0603010e070305030a0806180f07090b04030501 79
    0x380f81d4500a440802154824019500040c080180c0c0c100700c84121581c0c00080c10006a458201080101912014202c040d4100b032070b401283c4210540017810406032082602d03500f04864041030106d907500300407a28640c180d09c103600407a0004120390010549207105041c05090500044042112001d650040280f1503121040181c1c000740401958800300d88986824401003800b40013040313000c903000e480c0740c0c2440c02113215071600a00c2541500c3c8480d40c400140d80400b4800c1c0454409440c0540d481c82500c1400240c4e07801415000c4100307910b80c51a07401034007600c010000b05444610800c2c1c800741401e9926884440012030078811126840340c01a0010881811820710300c08841130090b038280901e204120700a82c0b9940007091300e030300c42e00f190325460441e0f4541d00403e0140c2408503a8000c144aa600d002c000c000d4044050803520391590b0341c10345035586490400c83c403180a00090320407000c40c4004184a04281d0345400d900070254103010781400c1d039443c0344600310751107907105480d680d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 373322688 1250 373321438 373321451
    0x50f0f0903060c0409110f1c1518050606091003050c070b0a0911040c140903070801050c03012102100c020d0212030d050c0a020d120b031b04140106050f1608030406 72
    0x4003840c1c40340301d607281c4482c104203040041c0300400100a05c102c90f4812000d080c0440142c403088e9543d000354040740d0074400c52507400c036990270300961041040c68465420f6404c0030000b48250401100755540860000c0800d0440440580143d00501c4080c091500d1140c00b000b00f080400c03044103003c0c1c06411551800940786100d0f08101342420080d080716031080f410a40c00f41040b40e0302c114034a18410040e07808695482680002a00d4402c4650288500303509200c2042a81c20001010b14100d90000307080c0718072a24000315103642c03640804e40080d4000400220407407464460003589000a2001e4880c60200c3c103650001181131002d418a02c00640c800150300480c42c10a024544d041443c80310104d04040c0182c00c06034882600011030000c0200b400303111440101c040d003082c00940c130f0140954442100080a58100c85403402c25a4004c1c1e042241c1003c0032000b40b0364140c12903030036580341d60406500ba2900703401c0d54080100200396a0039480079034041001100218080c5200c0c500020341c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 373323938 1250 373322688 373322699
    0x10902041506030b040b030304090b0315090f12071e030c0611040614090f0d24020301050f06030603070e09150a090203070f06050d09150e07030c15050f0f0903060c04 73
    0x1ea1304042ca6080c091410721003842d4075502c002041e5015689500b0001c81c3c12450000404c0ca010112002d0010614008013400416800401c0101801c080b00003680c68054040921081610840d0801031601502041c1940924107644180060720310034a1720756002c940380d40380d4500740d68826040440f03040c40010100516900510004080c20781035807081d0421580c140000c1800301d10314901401003032209024420400180490030389402825542e4031000000d119000082d002409058060034040c44032205502d4220241e03071040310000c00521280b4100388618004140141c4000c0d21071040911102170a40c0c100c2859200c4d40e00f91000140c040d0860041500d06080c0b540151102025240248801d650003422a01e0807240328002082e2942180b520340313004010086002e0300b040c0340c040c01003861400843c01c441200d028004000031941c40301d010341c0c4500302d840c40c4100408c00410004510b21856009401c03004003949000b0f0400d070600000c00c0c10604100c500c000d5403140003074107011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 373325188 1250 373323938 373323941
    0x1a09040618050603161a07110901080109021309050d140c190606050603240a031a0a0c091206090f050610090e0a0209070e0d12031e1503080a0201090204150603 70
    0x32111700c840030030302603035207007100380814401c50b9007004403800f0001543c0000c0c0b15600340086540b980151290130303c0d40e524042280200984403049100e0050707103503038120f20002405809915900000904102580c181e020307107610b04a00b100500440c07041c082011100014031420455a4140b10b50034040c8665181a0044a0740b0f9002244121001d0060055001e410414254010310800c040a08545540d0000380704042da030380004c011040490703002c82c1d1009004591070080300f00080500c0100c000180680c0ea40d00c15001342c400003140b1900b644c1c00b050003a0000d680b860b014401c00f003002201900c5d0300d42810301c1142d400f40103600c20101002011814441c0e21520301011011b0034214855a001545003180505000100604003800311001c2d5500000036403800d034483d0600d072615407901e10240113020a1070b0440e2040003001c10044101d1031034040d0f020000e145840c100c016a085958041e40e9270407444050045640ea840c140b00180c585101e802000c254104d0703043c0d542ca00e090350060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 373326438 1250 373325188 373325203
    0x7090b03060907081911030706050a0f03200f0409050907051203070314091f0f020d1103040504050c0d18060b0d150507030b0d08090306010f1a09040618050603 70
    0x110b03503030081100300003d0101091840c1c0e400d500c0a01c6142c800400c1c01c0426011a41c81000340c0d050065441c00181103170054003d114919003a10b8010300c058041d0400c4c2d0440310704c5192100000355117801c280d1a044090010004076800c10a610708140c2c4074250303102141d1080365903148640c00703c035051115103080c203c40d1035503200320002185043e1a641d8002d080d040400300300c02d010507011582c3c0d23005070740f08c902000000c910b6240d41c1d1080554100000c0c8a0006806620094000d41c160303406114403821404010303090150085182c1803400c8188401450010120117400500340f1030810f03021a036010f4040688404402503040c4110b41c00e00340c00b11204120b0340c03445400510804000544010221140e2014112002800fa07440340c80035006001034000300c5502890140403c1d08004500300335140052041d4212401aa01e440c0c5990041c05140130b00003401c0880d406550952071418000d0003d40d401800115465964281b0400d4581f58581d1004100b0b403900e0811000741420080ca0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 373327688 1250 373326438 373326451
    0x20708030f271c14070302010b0405090d0804110a050d0c180b1c020a0b070311060606030105031009030e06070b09060c030709061b020603010806070201050c1c0c0e0307090b0306 78
    0x9002501800880c5070f61249a120070b000040c0c1159040c40328180501030240d0750b12210100c4540d2035240d40b4000b4003e19852980324880c1d8904800719406080c001507405040500da19414401d0300c843d20761400103140000959800300c02c604000c01c968540c01d4201d04914810040d664955090034046007140585990300c1100503d014410036650780d903003204410107404100d41c2c0300141c4950021524800e000d0b00700c0038210340c00269900425900507030300c42c8015110b2098408a48801c0200480340c4800c0c400c16601d94030090202d041d03143c40d60300c90380c41107201e402d1500c1600602c80200341140c00803601610780f009400104092900140080c075030040c1e941c121a443c51401c41c0c0b02600c0c8150a005040800001080d010040080401810341d16500249138944030740e0b40d405040d03039a040c2200d0400065003480081a84d80c403000d010394010411030740d18905449601c0c22210028070812074442c0030024070a1480301d5030384080c0640005080041004140d810300f81c0181494020040c00c035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 373328938 1250 373327688 373327741
    0x15051b061620120711040b032512150f060602060703150b07080408120f091e1306050a0f050604092a02031207030902030d03050a020708030f 62
    0x8010a0900c00d1151001c00c44060401c1102c0d100b10103a03841c1a4400d0300b00002052107525050104408078502400100d44605000481309840a0030b103c15034045131003030398050780501a220070f101c8046040000c0c011008000c170100e03940d1040800980c0413261000d48625408080d040741ca8030803401000e241c00b103280c1060050610344040250749050082c105800c16a0303508146106100d4902008000c009000c099900c410782030400100d103600c14850300800d84900c00b645003103030620409035007010202074400c038200203640301403104100700b61a01e0784024610b80711030f0f82c50303966803442c2000e61643c9000000340281003100340582c031449a082030f00c0c041004c142c10400755035200704503000d5071807101c03020070820140d103041065850450f201c403101541c60700c003880d42c0584c00405049007c402c882c200c0407079255403a09404654010f00c0182d050f8001d8144a10344601980045422400300c14005142223141e8035100c929420990f88a0031074140766007032000003807000342040102c1240d00341 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 373330188 1250 373328938 373328941
    0x60305180102070f02010f1209141e100b0a03060f06080c040621020f0d03080709060c080702280311090114030607080903090a09020903101b080402040615051b06 71
    0x1d80184c48007414074000d040201c0540d644104912918200c0c2566521980a0103100c0c1d040c500b100100700140100b580e142701d45855803210f00c103c40d14100310300f96144040c1660100714140d20002d005c480c11400e80203c0e9000000002403010300c102c28403204180c2000600e02d05201101d414008491400c600c6107081c06002e12031968108030308059041882038a612989403440811010304c0040c401c554002004800340043c940c12902e0b0501ca8106581d400c00741c1500c0d03400507202800c21440c054445c21080c0852030041c2070801d020f0b45202a80341c0d898a52000c80d00c15020003042d1504111403081103804500394605102040030f0142002c1c080128004503508040380e601c1d60020702c06001c100513200400c441c0c160074401c032049900041c0090b10758946480390103010754403a400e118001e20400242c10341150321407190300620042c2e800c2d01480d030120b40004590041015000382da00c543d80d80c0700081c0c8104c0c41c0209070440c0d50152105a1600f80d00c408110030795260040c603224542150b030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 373331438 1250 373330188 373330193
    0x150a03150c02010c0f1d030f0a0813081212100e0108030a0305100501050f0d0b0303070f03020d080f190e010c09030506070e0a062a0506010f082a180106030518010207 73
    0x12900e42200d006d00c0c0320b2018500e1711310000789003035483c054007c04d0380034000e1030000b84801d81000b041807080c41200200c0c1156550300300b60752501070350030b4002c1001040c440d03800f0625101084640168601140c8140c003a00c0e1201c0c0103000101b80d0103502d40754030005035061541d8240c00341d15403000384a86021b8850b4a8600042c2c0b0510420140195000d4001514920301000d948090115980a801c4075203816031403900030321041800a0903005071080002503410a84035031b048a10a04092000305420f840d490038a20351200f070101020b0080303454126550480c042403107000308118455880d41e2020349507080160801001402400400800c4008010f554442c03144400440d0910315000001040c0810307441d03c0038032055404000c95058810340c0003440000901241644d0b801c00b001403115541e214555502c61f0320101e070b40780c00d08906070700c021800c6031039a000d004030101402a461800c1ca502c010100b0782400d801c0000402ea0343c03000d20020940c2c0341810f044098280c002103180c0803854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 373332688 1250 373331438 373331447
    0x1081b0f10050708030f0f15010e010f0908030c1608070b1c0f05040b0a1a0102060a09110904050f0607090302130b06160803040b0903070b150a03150c02010c0f 70
    0x35059805481e5580794016090311542c00c0b10f19007500b011210b0344a0415085075010000c0a41d8004c401d0404d8802050f441c0342c400b03120f41500001611004190054100152289020030b15444c0902005540000e15100c05100522a0902d002c02512803e48070100b002d0f110310094010603c9640444010b000e182c02100440f0404030741121104207d40f1072040e8900901066041802d44e2070901e000e200c1048258130080e4001c1605000a01002240d5070300420014140380c070043c01030f03200102041980302182e0215100502070580c9001540e5102c0110300061000d5604680c250701c11440291982014840b25411420074588001d0a41c90354000804440603103021400391903446400041c3c650b030f242d00b19240849029100c03400030429003002d07806900101d40035a0031310304160028410f0440442202d2205a10402202e41c86e218069582c100c1c0007403512258000d0b694003c040b0103e09102c92569070245604404100191050002070030355486000d10030600028903001000e00307400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 373333938 1250 373332688 373332709
    0x103030302030a0209040207050c010801270504051c0203030a0b030604030804060c0905030d0306050120150a0f060e0105130c0f0e18010906061806020a1502070506090601081b 77
    0x5240168076500d0740e140c0b0b0380c0240310301742c130b40c5a10901c0029400d003004808580d810048000742c80760400c41c3c0e81e808605440b0000f011558480c00b80001d100f07174441050b5800560050300450807680800c0c00002032146e001d181c00d0b2400050f0384040100f10f454109801901a500419400303054079043c56607024002e44405407000301000c3e1504020700701d0600c98511640201001012608108000000a40107020500850b0300180c95206114058170304848549510460080140000048112078003848500a0200e442c51520354036290124200c1b8003880d409015080d12100c519403604081080007044404010340450030007400c080703103540015495012401c2030030210304892114000902d0315041400864110100100204d4002403e038400070039990145c6661b401815409071134081d0034101d104020060340090300c0c0a0000f803040102001001e05e5480150901a4599456040050850300c200303043c1e05c44001082042001c00400009010000d41084202a214003240c03041d5407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 373335188 1250 373333938 373333943
    0x3020c1207140607090906080c0a03060908120f0f0601020a0c1a220e0c0f071502210f0612070e0c0403050607030c0909110d0f06050d03030b0a0e0106080103 69
    0x115410741800035201d000c0803004a45410b8400720300c1c05000140100c16280555010385192010200b0900d50000d0301c001c0614000f042c1d202801d14544d94140544031440044070000c0c01403042c10030710582000480c0c003403070418000e91503074500780d6000c001d010002854541150700400780d490220350901ca80c581900c010354045c2c0b410411040418440340703e091007950025203280241285010000d5114041e034402c049854066107803a003500c006801401c1085200301006c00150000414080ca51f51844030803c10150a0413080390300c041c0f607517000e4030801d491003c000c03042204001c40450343e1540304604845840365505039915448d6074005d240642c00f4580d101c0c0000c501c00300314103010f9400650740b10b42112854a4240c40c01005080300703421a0000c9040804089802c0d0440e005402140080c443c1c440d00f05811002c00307002034210788036500300c1c46595150124403a140c01100d80d01e80750090710302052102c2d4031801d0140025055020300010b40148005100c8180e00403040f90460f42c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 373336438 1250 373335188 373335223
    0x606180302130906020c030f0c0c01050306060f0a09050d0501050a0f111c0b030102031806070804110603130c060c2015181e032a0d060207020a0b03041203020c 70
    0x3c800345801d100034403c14560300301a06c00810701881d9041000001c114441c10341003960246c104000040d58180000e030f82c101d600100500030828075200d00400b030140c50410f848c24030403140c1d0700e5002c50014030000304182c425035110010000409a0b600907841e4000240b071003005100015000f20640d40a5110741008030032a00306050588100303500401240e0b40d005000319030341d09059418448140040703031a0401401400300041e119802030203c140710315001001841d203495036004201841c0e00042c060610001507510b00e03408240309400034005441d0039201c4a625066506005043e200f5080a601c001c0e031100f042405261642e54004505800707040920303455200005010b144e030340b103c0d10110b0f00000b60019910070344100040000d6a40b0703041d0241d0340c00a07100e8180e0703001e030050800141c22443c00a0325000361343c00c0c49031818541c1070041000500301707d8035500240a00586c1da1000c06100004410f0000340a43e24001110080310303410214981302d503121540b0b0b00d4074154241c40040d034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 373337688 1250 373336438 373336451
    0x6010906030b2b02010801140306010e09160605130b160f0f05030a0c0b07020d020604110303130b0705190308040b190e0109050f1209042d060618030213 67
    0x7500c40c44885000c1803e50103160090798605000ca014100090100ba800501c10000018282881e204003c1841d980034018019076800c01c5400c00303140304003804141e00c03880340e14441a40820340340c00c4140941050707992255036064440031281c214001d500300c000007920810411261750a0010f601100741d0b840881e518804641d4100030010205c1d6100140903070000103005071a2035841407641c01064460240b11000d03440d0300000301d030b8582266074800e0150707220701d001c00c000c903500004400500d200142202d203019070b900c958034102c0070180d205e20205c005c0802c4520403c1020301030342020b00d0380514800c1c284842d64900800390a005040a88002c503000003090b0b40030341800031400d41442c0c0041c240107107640c079501c060007050310702801d8490b8010360302c00030000c81010074959107103070034a144542000465001c01000349040720a105205209a00403035450011202da44512160f0150008025180c2803000c0c1c08042d116008000d804800c01c02400180c0d01c20120840d000c1d02804001141d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 373338938 1250 373337688 373337711
    0x809030c21130810050c0306060a03200a09030b070f0906030902030309180f0604020f0a21110c010501060503070c0809122515020d12180c0306050f0601090603 70
    0x94491040c4031a48081d0307100d00031481c0f002c00608091003102541d810415039a48644c02042da0000396009079001c1020042154900c0c46508040d0404080d2a0030344660009000e130004c880d8082e0740321601040f10038001b0814010380d0400107a10103d141003074150240c104500400c014142d004090a156a800c40784043d9202001520060640074001e08a803d0088144084504088030320408001d6843c0000e490750074a4026618445814282642000e0302c0450680d11441050a00d0101559042512005204600072014140b50f40d40040341e540e04985105425104140c002d00d0034003004006001070513502c0081d84900c250010070060300da03214400010900809101c90b1074452103141c06001401c184014004d680710068030000d841c00e80d0310306842d50a900e981c900680560440b45c01c2c2c80000c0d005900444d428038941200141008020006220340040340c9001c0c0c80540d03404006004116052240c0d40d00301e001030180380701520304000000e041e43d00c1030060108040d164401e4003103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 373340188 1250 373338938 373339003
    0x10f08100803043c090b0f0303030a062303070501050c1e0d02070602010e06010314070f030b06120c030a170903070b0a0219080d02030c0c0102070f030809030c 70
    0x2824080c01542c1c2c0c0c565450940180b804044e00400d00c81c0780d0202000d100342c0c99034940e21100c1008125030180090300d00008034000f004140625604008240a076907216502071000f903110302148140041e0b000d05200400c04030101c2186000100d030b982c4524021655000642c0c0800c03035000f46403081e602c042880c042404c145880c1c0400f0101c0740403c0180c144402d000c40c82228095241d0b089138000c1c1e90b2000102d007a15424030903c1000c0c2c0000d070040c07002c1303104120348048a12501d41126000742d6030310000d180b1140c60350710580d10154400144419851f1085456800c2c103212001072601c0360314440013075166040900010310852031700c2e00d003c403003a1414041e1645100010242c54643c0d030780b40082c002a911203e010300c01805080e506490b106002c034a10030080c1e13080030341e250400300c208640380020761014000c2042d05105100d0540d031f2401c00d0000303154040c0304401e07004680c0520f24028101e004054103801c46500306124070140c014000030303084c209851421541c0d00c0d03200406807405 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 373341438 1250 373340188 373340221
    0x10f05190509040618031e0315230a08012405030d08060123030f0f07050f090301110418060602030a050d02031305060403020a031407030504050108060a090e1614010f08 74
    0x2519010075a1109140e002488440d244126011008946071810008c4088910700110103d00a0502c0c8050060101d101002000e80700f500184140d50401c88000501042195001d00c65983d1100c4600400071000641c00c41507268840d0011a010b0620700024ac48540d000317080c2d000c111092001841c036030710848144c0c9582c40400000a00c20340300200f8408540c1c001c540011511241402160301000d6180c5907601c5808556211030614003130300c00084903a408564842d42c035640301d0b035200314070b81c402400610041c5002c4442c03000b01d1520421840036104158000019500300740701d000c00590b000780485503094220040140e4a9a5128210040b2401c8480141030341c07044004002c01c00d600001e074a0340f142d010761200c0c0b480d00910300f24440e072449003040060002d901804100180d501a29100b40c001e00010b059285550301d81260004552600c0c1404400394031001280e4405101c5100c0d22020b00900d01a000100caa9040064035803002d405410040007048000150f90b082d01184a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 373342688 1250 373341438 373341461
    0x60315061d061305030f061b0313050615040c031116050106031406040c0e06130507110a05010c0f02060f0f1308030405070501030b010203030f041401091a010f051905090406 76
    0x81d143c5114540c040c20201d01c03406081e000703114035601c4c075171060301c0098158820410404c400c001e8080c46c0b0045142508080c14490340c005080000400051040c07002a1040724039409040403ca005400c20040d100012000c800381031400106042c1d05210b501110b0f034240c945000c11401914a241280c0189501c1e400038160b010250190845910702040c030038041c9024540c48599140c543c0d458006444007614041d84c800c00410b00b41c000d04009070031540d800002c9041c2002202e06802d40d103800c02e4881d540031226650348a00c9100341640143c119100c4a41e0b5100030421480c08010400d041ca101502008940720030743e0001d05001260004a60210340c0400007640741d01703040c6081640d902484c0103207400f190519001c51040d500c00820b0b01c1c86200ca1000c00000d5441e5512543e100400310105800f05549414103031000c50803c0c1401000003020301ca4012280d0b1400114100000042d0400c0d44240310384040c0030f00305400c40c03100c2400e9900071100030060b5151860500c00402c01003008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 373343938 1250 373342688 373342699
    0x203061309150b1819090b04030f090611071809080a0e040501090e0a060f1529040605180112050a0e0f01052208040801050405070906060315061d 64
    0x310401ca071035044608a040d040d0428400186010300f044088015160340d1403049213a2000139691075460022409540c0081c8400107000406442e02c000118084506402041039a200c802426522400c2c2c000209101c2c40c003031085c1411204183c1c0c444556220b00c3d035407502c0b84400c00b80e000000c1c2d40001e0324143c1c0254059642c40a41602518a60304442244d12440c540400099103c8060054102ca20f180c1d40240249007070315510030f80201000e1242c407445950714941c0c101441c1415800d2030140094006541510700c40c01061900000a840c28984142c2c081c0320800043d5040303801e0300e03c022070307a43c004041030b5900d80c012903c0038006c0c00700400f40b5080c0418004032002170b0744043d8400a13110141d0f94154140c5075003070b003078403004e4401d040203a81805801c3c1c00d03141296842950b8911419030145802e6032034060500752907081da0b0689003a00403860411040c403603440b54800414a505013449206c84108180e4500801445005c040c48500822040b171108494454601104000c2c035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 373345188 1250 373343938 373343951
    0x9100b0702040608060f0a0b030a02060d0f0b04050123030d0c0b04050c090a0b030c090709051e06031611060f0406110c0f100612080307111501080a21090902030613 72
    0x140c0b14105682030f1203a80302c281c5008c88c1d0300700da0700b404903200135825009040c032032814402e048880020000000300c0c4c14400ea80340e09044d42650365005250081240700e401410580b03403c050741030840d01400c15039219500ca03d10981c0300355004182101c0c010307040009600c13196514100142011503911040b0b9016031800c0c20000c0c441c210364800c813800201070b0f00f15805c150380b2701d003888040c00040d40c2143c04200d006c0010401031400c100845007243c1c04480c14241c0c5031101011410035001520f4603030840c44030490b00b20005601c111050812010384008050300c0c10042c505000000c0080d0000d800c079074640c1d005e0b881c403441802c01c441c0c5a440403000c44180a80200f40caa48030103450106600c2c4508100c000118903140c542d184507140c0e08070101c245181c40f040800d80f040d80c2d54950844a070700419404107444104682514000c0003000d010704403021181c41d001c18050b1100c44d03180300c048818549000c81c81e07130000c0c110060782c07902d500c0103030b80341c64a000251100030000c01000f0380e07a0410f50b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 373346438 1250 373345188 373345201
    0x1e030f080d0c02010e1e070518061804080a03050411030a0f030e0a0305120918240103141303050903030703120e0a02031c050f030c120609100b070204060806 69
    0x7444003003803242042240c1c03404014100e0a8505914422803035611144165240d002d0800e038400e4071180803000c5031aa6030f51100031808241070314441c03060039001e440400a4600b0440c0b0f079040103172890720003800c5503d4141e4500700c60b03004004c0c0120030182d941000030100003503e0066060107100a040f1100d0045502d003c10904035904001c400090084c0c031494ac06060418503582940e0303100024280084202c50010b40582220780150ba02562102170740a082142580b0f250003910002c100040301a001d440c0030184403039042809042603c1e01440030301100e020010700b17400c40c6030041a100103a2442c2001c0b102030240d03060b99030307140c04001000010143c1140803000600101c0da001d00184002c2c07150151200540000a5019080319900d1840b10500b020001c90081c0f0906002c0d040486d1052020082e0704201e80791008580c00190040c1c0d440130b10340c01103921680842c0c2e0b240181ca4046006218005a8403480200c20b402155034411503a03281c1012003e0800007040302c99500d44031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 373347688 1250 373346438 373346453
    0x504050309030d030c0e06030c19020318100806120106080102031503070f03080f0309070f060903200609060901050d020c1c03020a090b03060d15050703180c1e030f 72
    0x2a481e0320b110703108960810f94080d00074054020700c2406515101030148001d028005030707520003004030401c40d0381040f500c541d0108030114510110381c01d034001d688a0b260280007400102c10820305500c9821200391803008941d1141c4201c2c1d114001f6a04c40c0f1701e4031800c0c807845001d46419040215194004000c11141305c054201103041000100c0c03c854001c1d548007000c0700a45441e000203020140304100103107140d05500000d58111401e0703412207060650300d80c06600c083c3c078250030100001d4101e03881041440424000c0380c00749521086480b404c105894001001c62140e225514011100803c040341a6030088007038603158030130b0b05001e5640f140c0e0849010707181e80007451042101d110305042076940500c82e1082c1c8a2126031515140350031030400c0c00700d9016810040c882503001d0794203120b8000007208c040c4140c4400d8000760b400300b82410141000b5041e00d030524120384102c0c00c0c1c1c110107008541c503400c0c1c0000b100c0500704110007036044803c2c44003066a03203400290070b00a090102b02c1c01c10515 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 373348938 1250 373347688 373347697
    0x9020a0b1e03010e150a030b040c0e010510020a2405160228060506060904020705010e070506160213140103030903020f09070f0f120e061603060b2b05040503 69
    0x111911600020791580103500d46002c02c1c001c00c400c03915424001955502c11402e481001a0001c1a81108668903669200a4001101c045130020505007013005030301c25264030702780580400c46062258042d0520000e554805d9040083c09400ea02c02d002101c4e5118600d44207520114440140418a040c0a0105181d075604107000014820029680d8007400c40009188401c0441d0741d003100d5104c0d5030b89404015110150807198442c00c1080250455074032880107255244c444d00020803035072840110181817410a50201d40122001c02602c0b801e401050300c0540c0140d411104407400ca05107254241c002c1c803848000240e10030000c1c4c004820301da089041c0a0807039208030f4071030400400341c0c01030000d01a805c2d00c2220101c0c00e00c0400c004c005000f803030200e40e00380070740c034100101450402d000d0003a511020541482904178000b03000b104d10840fa450b120400c1e181c1410b01101d440c1000a001503c28807000c080410765134828624091030f401d00031294504050b00030301c19820b09050840d143d42c030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 373350188 1250 373348938 373348957
    0x303140601030203010e0109091509050618030f040905090c19030c14090a0b01020a020402130e06030a03200a080a050301060e03120a030c020c090c04050306090111070305070609020a0b 81
    0x14040040d446600c83d0003224141e500009803190107034a800740407400307030109501c121401e013060028810301c805188182009c0700e00448c000d002d14100003031200340801074880030240982003000030008030064a800c5404945007444000b501b03036140f40e03546017080595044036a000c80c407503200195001c160700822090780d001e03d40e0b10540b00d56039050842e0380703061100d19a810101c490300203070041840d64001d401ca000180150794412400d580010304030b912541c1400710108641c5c90a120f4203180c40310f607580c4100c05600030a0345074150788005c0c080d41c10405141e9005007040001c948140010b1010b21101c0f03a00c90001e40e180d031046000a481e0b40c209008840c00176002000c050403509d00003500c8140e850541c0381d41403803e48620421009010713038820075019440744480000f131548070000d00c9440f90707200180345900c035801c00c0205410f20b8005040201140c0c1003078100864000f112040b1100b80c0d43c1400d02680d00c00c40f910b04007010341461a0042d500c4500840002040c4640e00000c091880 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 373351438 1250 373350188 373350221
    0x2010917190305070e010302070f0b0f090d030e07171606020c01110d0c06020d020408070801020a110d0e01080714030f010810060e01030b0a06030b01030501020c01061505091e030a0303 81
    0x7900c0481101103440442d0403c0000f4406404404554020f90003004000d00850603080c02c101e0f1500e4090000c40b00356130030019508540c1c20064001c0d014401501c0c10340880c41c043c420004e20b9034201c1d50fa61464010040e11007419044480e60801c00c000c43c11020f00807481c0c040e40c0703642e21328020f52100301110919002c54018551000180408550801c0603005a00d84064000c0d031038451400039008100100041c0b5800c210105586200300400b500429901001507503800c980000100640d2207042c4480595000041c0f9080b0309030002d000201c2481c0a103007188055036013000c00c039000303103080d104020300300800000c0c090200709204041e4180c443d0b004c2150062400010514100d6000340715a8203003c1c0c491f8010300c00a0301300d10f905500324840d00c0c0f011170388a4803a180c4100f03081c0280d00444507a0350008602030191003e0060a0081078500216002d16009007c098000e10409074898400c00904424501e8a80d410a10741c406c0d54001d0200c668541d402d190283c000d007000b119279503401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 373352688 1250 373351438 373351477
    0x209040605150105030405031804060b1b280605040503190c03080723090406080d090906080c060d020d060e0c0d050f090c011407051504140a0201080606070302010917 73
    0x1c3d40554120780c00fa80e4040000d514100700b0f0104160702d618017148142c3c1c0b180d207414000403000c0300701e00641046490f0b0303d055111000035000141c5801e0142d42840030304c0e041400001e0143c090024086845134100760046010390341d03031030314a085114030a03005000c0700301440e00c0b100302c6d03a0041c4010195880f0303481c0c6041d141c940300401c0e034000c14002d040c00a000c80d10302a00c800050264041c1582e454050f2002c6903258840c0304c0e01e4200a420204c0d1000991700e40310402c51a0914094007008180f40c6010308440e0484c1808200c0b18411170940051706038001903480c130885107580c001c90081592181e408290300302460403500c103501607a08100034904040c08a003034015000440c500400b8008020306c030000550005554110b510300201c1441c07034090043c036012a0040c0448400010100d07607440e020b181501e4031002d1040001040f01c0355500040080c0e005036040440702b60005000c5510139144e200780c0c83c003203003d0300d02d03200c008120500103415888070020103000340c881c0a165a0807500070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 373353938 1250 373352688 373352731
    0x60503060a05161808060903090907050a05040e040305070510020910020102040509010e070203040b0a02060a0609020c06040602030603030f1611010804030c1b09150608060102150f0903070209040605 87
    0x366182941c070010345900b0582c50080044c080c080340d07103581c408600712212696450040900700f54049809a0085c1c100051203000c03460120342c1103900950074100b040c10706404c104000d046000318020000744108041c00304051500520a4907192070380b003411112000040200403019402110b80c10b07004001400c0070010483c018026035044d110701410107a0301c0d83c42c00807420b0b9a001e0260120081d4041080085000342c3d00030020301581e840b0350010001030820591001c100c40e140e0b0b00241d038281c41807220030380122003c03846c01c1d00a90030140140e1640c403420006800d51040306041c60304404005205c84007003070005255402c0c0c600404143c460100c9801c01502e0b10070080b20000c0000790703540c211000081b200300c0070341200d8440108403035010385c8aa102c6012601030b0380d0022b80d8420202c404001c0c0d5544042481d43c030503420b2015200e0f81182e0108034150503070241c90364a01c2892400042c45034401007060720100d54004100401500f4181003410040406585008030700c03c808000003403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 373355188 1250 373353938 373353941
    0x12030c07061b020c150f030601110d0c330b01090503010f09060b03060408030118020d0903020c040e0d020a02011202160c1701060b18030c09280504030504060c080f0409060503060a 79
    0x5d10402c4001e4040c58154204440002607000403c00c0f07051219503501c895a0420401c43c2c002c19814640700c5e94040d0f0400e04140008070219103840602d24a0404202400046030083c18100607050071b0108032410600c0069403080e2550300442d8041d8079061b250b200c404072980012060a001d8941005007900c910b042c0741d140c150480b400780039440c007040104404464040e030041c0380b130055980142000105c0d80d103501a9600840c080d40168007501200c1003904e003510880b54025043c0f401007081c80c08045010b52201c2d060f1a003e814440250000c110746030b01601141c03802c1d105c1ca44603044491591518440b03146560091055048414011190707062051041c54191a50300178014108000d00011b00b1a003112400c201e80c043c010b980801e005621050740e2203004d08801d01c1f03101495855000345603e1408220400081c06d4240380a0201007608039049500380c41442c50107820480300c1c0c1c144008980300d021000b0150b1480001d002942d0780e207076484a01611412400c0c0c41c01511824000c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 373356438 1250 373355188 373355209
    0xf2d080903092202040902030f04120908060606090a09060b04061103040501020a15090506190c08060d0305030c130f0914150f0f15091504030512030c07061b020c 71
    0x3600161a4036a0f00c200c1003002d03424038880040901c0c05454181c40e0340d440805d0341c0054480c5e00d82c841c0c103e428070040080c9440e0101c0600d98529100503164500443d051381c3d92405042e15000b1400082c4104498940c10715040c007500d1400702c184109651601ca0320181d0740140b1440001980b004000240c0032000700071a411620140c1c001d00740407401d901c502080d9003aa031108459140d9070421240001c1080c40f9251044803151200040c1c00b880d9800c3c3d006581c40080401c0801c02541e04020142c0e45100318524226054036082d40c83e40d5960075460301500c940c03151034802a13000c0c58009210031240c8584015100c05640c180442c0c9c4a1100c501c85090064407288050a00054600e50714200003882414501e0024a880d00040c0d4040224403050150040c2507500e40c00001c002d42582041c20043c4100d82c01c400e01e07103141c1890350300c542c5d46507401c200d401e00b1008800404075801083d1101a01e4081c2c1e0041c201b0804901c840d202c202a1600551841c4054010000c180109103000000034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 373357688 1250 373356438 373356457
    0x903030c21070b010501030515040c020c0a090608031b01060509090609070b031312090b280f020619091a0a0b010201050903090d0206070c03050604110418030f2d080903 74
    0x1d425900b000019005440b0081490202700d0488104800b81e584078000d6649440030740c0c0162201808800074004a032525810a01e1060b041038800c2141c00000800c5916001c15241c5010704071022004460142502e6441940c0c0581d0f55000d00000a02c0030170680e004403022011940c84668460307492185000403158000b11003d840c070000d010440d00b0703e220785207181c1807a055000d03a8441c0840701e031f260010300160101c25501c031050388280e0f24a040311071810400d070810700e038040c2e8284002943c96070000d00891044908103d20040e0140a4108000155208080002c120101010501c00140884009400c40c1c08c040c988031076540180f08941c0138612420141d85031110104c00c0c03014100c1051070490708004100400720115129800c440e025602c0780010b0704503401c00d0f0819600c003000c0840174074421032410264503800c81d80000d8814130144d05082510306568052010f0b18002c2e299041d134520261003071140300c0310703880012406c0400c484544411400e901c602c00d81c582d8902403072449 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 373358938 1250 373357688 373357703
    0xc0c0f070e160801180e010c0f030b0607260c0a0602030402040507110d0c110307091e0204051e1c15180b0106033306081509010501140903030c2107 65
    0x6000b04044c0311710040c40d04200e58008104c0d840e4000c901400c465a0042500c00201101559421a60705005883c1c000a00711540c0b800e000c002e4031125441c400000402c1094111050b8402c0b510840f402503500240e41c1c8c03015503000e00954101b00000c1d43c401c4600724403480c5000c00040016000d035068500070001c1c0001400700c2203070b04a007596000543d040c140c9078081c0d91403c01e84107a500304035074805080f51070800704003a2460a1748001107d54100742031001e50043c0800d0005495000f04074108041c1c2101c9000e100a49501158580039141d40daa450001044007020a00c841819414900c13210064104681041d00c01c090740620b03062000141682c031920010040980b20341c1040d500c2d2468a100d4107107148503000444e580c401020035803042c000f038101d0100f06840d00140608d5002400f407040e0100700390311400203141c003201402418140622481e687e04804500c0341962150500541201e07a600043e04015540e42071071660316032000d201c507850b400140d0b080402d6459140c0d20405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 373360188 1250 373358938 373358941
    0x21002120f01080d0c120c060e070f0e13060c09090f09050c01030605030303061011070305150c042103020102040f080c0a1509150212040311041109180c0c0f070e1608 73
    0x80307190003144441d0080c1e0411082d0348031f403408510984201000080440000c4c580d40d8948544403d483c800f980c07282d01ca070000442007200d0340804945049000303a0040c4006002109103009881d000c036107030043d1440f03c1c40e10140c060300c1c400561007009914002c004907000e50f10b020004400b540d403140202c0f50035401c18404210181400701041510703006500b051030003c2081854140b40c02c21a03441900d55900c400d0f0f000c05404200c04841e034002850840052503d030803e00b0b5040c0501150446181c01d041192141c814075200707506035406455110040f28180d940c52202c035a4403801106c0c2c180c0320b404114030026040340c4680307480a00000940312071180d50314240343c4040c14040300500c2010350048010040d02e0300b10313101c010b002449c41a402000c807035515009220860f80d10640c1001605c0040080042503039441400003c0541415507001e04c0d6034810301420320781d000324080492644101034000c0034110f004243e00080e2407026040c2480747c0e840d6000e4540c05d11750709031400041042c040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 373361438 1250 373360188 373360193
    0xe060a05090c1b0a06051302090106050a110d0512012306070f080a08071e05041a0903010905010501080d0305060a0506030702011b0206060f0102030424021002120f01080d0c 76
    0x75080da00a41c481c07001410300c0710101c0c8040d0840c1441c544045140c100c8001c003020044184200341d00f003040440c55201ca07030640c1d4041030100f0310602503201480000304602c1c1d01d036485201245c404801c101c00382e8002c6541c0d4000500560031030003545480c00c40c2040042803c02181c0c1c010030350380601280d00c0f005100024144030f201da00000d015540f004009000102040c051001006488801c1e0703540c0c422440e1148002b0f01449070300c1003c10100120250348540c1076030000a035030598940b15407540901e00316802c140d4a82c1301e207501c100d80550030081204184036041d80304504170341c040000d9a01010000808900310740080300d441da40700b903000406120604003c03010f181e001d40030303000000d51088800741c1080e40d0705030b480110005900410400ca428241f4404030740080d0400e000860825061050340c207218105050341c1e1840450b1001150349042c403c12a03420801c2c0038030404c5584011141d84103114050407240341200040140c0001510381c0005400140d059a50b030700e1400000d03942c6d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 373362688 1250 373361438 373361449
    0x50415021207022b081306050a0e01030225080706050c07081206040204090905060a0e0d050d18020a0308040608150102060f250302040905070908060708060310110a090e060a05 77
    0xc0010036001c1007003460b030380701c1084880c4415543d45e0042000039101c4c0c0306842440c0e1180d0361904010100f11091040d0381d201500002c005c456030381700f400c001da160703013603d01c0c0004030300300f9250695482c10007545180103016104006000071400340005101c0e0350b84504003100b882c49040e0005100420800104544000f038100311fa0304008028409443d06039510001c00640d00004c4080c0c070140c020b407007840744003501e0344500c2c0d00b08900b550180c5800740001801038064004c91042c04100d60300d4107143e95410094024540c0019402042c102c0650389a081500894100e4010440841c603014003042c0b44243e1a807200c0d0a110059005000640da5030280b0781000c90041c05507400c843d08481d40c81121000c0703082e4400d901b0f10342d03580103880c0c1d0700c1d01c003000c07040e550040c1852080c0110302105000300400415090707400340c87c03410800000d072989000b01e4a080a49000285000d01c2e000303003241c0303041300354000302a4680e0944d0b8440c030080e00c64004c09a80741d8142c84981d0f01c180305440402050038003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 373363938 1250 373362688 373362709
    0x4050f19020f0405090d0507050705040e10050f06010903020d021f0f080105180a0c0e030d03020c072c090c060d060503061803030a0905030c03070f02011e08151f05041502120702 78
    0xd100ae84040c40c1c0da5001190a4460a0220b01c070700e0382203e0014505400c06200d015449440c5c0701042440c1d0400d080080d04030200ba00000e80106003c0a01c9401d640b00c00c0c580c1d150501c000b20a0b021400080d00d4000c01c0301e000010343c440040c0010b00001000e00d0412465454100c00c041101d4440d1500038585004000f0352010609201038407001c00240d940c184244c6480803103584015a0701d17a0340315080d0b0b003400d0b0207030800f0b880d00061032441d941998420081805042c03030000c140c201031321840400e6242841a1040c0c0f5130000380010401c0a81055801580444800380c040704e000c1d880d0700002017580482c0c20850720b041d42c801c3c80012101929500030f03c010901030001c0c2c0b45490000c010035401e5600041007035a291a44042550031942d001e00610300d4000c00c1340219100510070400107101000160174104102c51201c0f5008095840302088a040340c9400e81c041d042c03100446025010340c10500c54032441000c0c06030305690050001c5100020004c0101095103050026400c11101002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 373365188 1250 373363938 373363943
    0x60e1b030c0307030e07060503090d080108030f090d0606121e0f0b0601050d060308091212121005130b040e010204120b0a0e0601080105040c0f0605090904050f19020f0405090d0507 79
    0x1195120403078008406c1c030001025084581d07400b40d82e03181000b0280d1030030005481d69030030040d00070010450044048142c0380c01d481150318544d5100c2e1041d0019035108000840075124a02d4000005040c00035807070807408181c800c0c1c0440b0400600750207804040300407020007602417445407240c040000c010a401c568408070504040d800d00070b4280c10b038000c448640c2c204451958000608002903d050030184120004880092481010482004141d8001c00f03460380c00d600018400f183c21298010a034001a160141503548460004e040882c00303810600a1709004910340320507611340c54018001c0ba802c1c3c0b00c0150700344500648950352484c90356001011800c48996a024201c00b9440a10459008001d4070300045001d0805080085a916641e48600d140000c120810040190000107a41c07003444100d409180980c0da60614600700001e0714804d50250280035103452000202441d00c08000c0d00980e914080c5011440c140030440d142034449a01c1e0743e1000c030741c0680c210300c5400240042403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 373366438 1250 373365188 373365191
    0x204060b030c09092d010317042402011d01050a0506010e2b08120108060a090b0612010b28080d0507120c0b010b190807080106110703020603010306060e1b030c030703 73
    0x50745e43c1070b00010700d03081c000502605110700307004000b0b100c00e03c00c8441181001e030300708230315103454000d000c240e2500909980341e0700c007650302c04024030b42e00039403020407844080d000f10b5110700e401002043c001c1000321041e8011500d040046880781d4800c150001c108400503010905402040e605d00c0300a146000c0c20401c0c4485441c4a100021b59803001f5050014002525000e5541400c134500e080c07110080440e00103500d40440100400c9a2041d4140c02803400d07038101d032483c00344070300c0280903142c54007035550422885c40e6120700540e03821010004111300f0940e401911926110f42e281ca80341102d076007000044060140e50b0200754494802600c032603060501a0010300c1c1c0b80d80b20385048a09911000d0899000720720f850019400e1450042e0460051502907401d10b05404003400e044818050001000300d58503001d9070604040020401031a002003000761290b9407132034241d0290844d03005048120341140089100c248100018460301d1140e00b00c01e03070440c9e42d60f000300256a00000c11060405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 373367688 1250 373366438 373366471
    0x90905070b1605100209090417130b0405100201020909220b0a020a0f0e1806010c170406020c060403050604060b0a12030e040c020c030703080711090703090204060b030c0909 76
    0x111807000b0060701029819400340c110700750810b2030512440781e01d4038800c3c0780100b15080d03003950b680c03e0b5150b11550110380c801800702045044601070044844000c644c1c0140c0c40d01144061003071000d0402c03104219001c0701c240c030840c2070807401c1c0e0040003001074000d42030501040c0d0f4017500300400700360b0820043c01c0f031404500b01e03261100c61510544505034020360000304050407079403050321911070082c142012100d011160004c92742030000c204003030341100310210205206070301c0b5400044030f10b81c0240b040a0150350100e0044042c0e0b10601c0381d80b02521422866a080d42002d805031811030317802c0b07005800182c0c2c442d2126030203013000088540d4001800c00003c00e500c0d41044000c0070241c00790752100020380441061000301d4803c07902d140c041d13612005240101e6500001c0c50001e59a0003250961104003914052100c111072009541d4040844000c00200079030540c1b121100500844051207003035035664960a0500c000e6600190390881048088854101010556040071030113104c1c210b0b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 373368938 1250 373367688 373367699
    0xf051e070210030605030c01030204032001050d0204030b1008060c0406030515120a1b0b07080d0902040e03031b0310060507050705030601060c05150f06100c02150d2409090507 77
    0x20300000d49180b202095440c070b020301444c1030401411400074800e0038114507003811030b110060112021203010355044064001c0b20f88603481401900c001146401040d901c03244c0303900e0f08540d440707000c551540300a4401400000c031360303a000643c94042c244602e01503280c5828030b40203e01403c07004007910303143c0c0d402c0300018003103172500420340c4c42c0c150201d000303400003603a189019142c0600d41184404140d0740010b091102450300780445603c907a12200c52503640302d928a662f00a00008034020354424544507280c0c000d50b0011009502c40d02d04107408115504035064019140e0000791fa464296000c140401e00909005130018032103507001320112001c0030342e40e20000e07150035801d0300400001140d01e002d000401108028661104030704a07642d41d41c030b1a00c00c1d070000801d0802050540f1600a0300520440d140c02038442501c4e041c1c000c1c18817815120003480c0044154015901400801d1514440c512a1010b0319640100d00300303168600c6800e24030309048000034080c01a0180c1e29801920400544c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 373370188 1250 373368938 373368949
    0x608040302031603030c120921170c0703021603120c0203030c0607020c0a0506031e0402060c0607021b04200a0311180102060f04080d0207030c1509120f051e0702 71
    0x6104d00c65540403031a0403c00340001c1c8000095800f50041c1420b0038020800160344e4585038203a00e4542c01040c29601d03400c4000c50300710040e0b0140d0b42c0d410004c51b0500003100c2041c0c00400300e83d400783d001c9412010030522000c0011410703200c040d05914101d85a21415407082c0500c01d9850b0000302140d04101801c0b00e50750500030b06440b8500580c1c001c01d901c00c0c8604103542a180102401c45000341580380994000451a86e0104d50300300c0444400c0010702159140401e440b148616a011100c0070700d003140020791f84240004403000c000c0d00c1030341d07900f034903180038001c149114018580041c411040c666006015811540b500c00074562295800741403404e15001412008100750304219055000f1400a402e01d40081c106c3c0b85e110300704004010218810908603070724403400c0c0c0c400503a680c40c80c2c14221401540040001c0c4000000c83d03480e01034154980000400c140030b4401c5150039140c1b9502520108003800400d4049881480b000346141000b180146429072070071104d03490104103500049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 373371438 1250 373370188 373370227
    0x306010c082206030e060c0c0a050319031103240a120c0306050901022703010f0c1701050906010c0201031802030d080103140a02060d0b150c030d0b031204060804030203 74
    0x7010400c42c40203601d494681120311100505a60a0030032490b0411060b1031348401e402889000000b10008040b041080100055544035030400305881c1c407041901100550004030f40d500100080c101400c0c00609074410044038010b0044885c0a0252001d2200c00e803940038003504020f510950801000408008588102e0215407140e1183d852007400c2d49098400c40300041c2c8070503070580c414000001c1c50713016043c4490742c2040e01a4201c01000d41c0340000703400340a00745404850f0b00d00f450505080d15401c00c400d00385105090241c104940e80780d105110350354034200d80c0280011500c445400c0954000d0384000c2650f1005018158031340f4082c0c01181c5005500580d110021700311000400501c8801c0c044004203207050406800d913850242c001070034501802c4003254200c0d6031140ea00c2e01c1651500301e540382c4590700c4001d454071a6071008109889400010544a00e50708114811215150204030b21189a00c14481d582c14503080180448011400a10842c254070040180780b00c00e00a6a00780d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 373372688 1250 373371438 373371457
    0xf05010c0f122604030c030813061505120a050303280e0303180a020a0510021c0201021801091802160f0506070921080d060f170c01050418020306010c08 67
    0x100600d108410180c0082c01c00f5200351082d024800c00e0000017607028070b04804045d0149050784e03060b20303a0754000c05142000c50000340264078101442d200070806a894400b1918102c0c1e1074448441d5a005840e1640301403100100940c004100080e82c003080f400c900d0704130383c0906a50308044c5101c5100c0310b045a02188007a00141d1001c420044105010050b80024041d030101801c85041c596003c6410222180212445407400d00c0588440c544200240320010b20407075a0b265184030703034200182c000d43c000c0c0b40d0f54a000b100401031607441d5004450346c10849040344126450014801000300081d00500102440c2c1c0200d00c842c1c0d404120000c008040003800b40c2c000c3c200605060a01501c048441d5000740c01700a1165a03011000f0b8481454030705c4285c000c0180e556840408608800410864000b447ea0602d00e110220f0034074500c4044c01c155111960481c0d03030070b04130340300151000d0146108900481c0d0841c0c0c004516071165130055608180103040401140a00d9901c040e082e802c1500c56 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 373373938 1250 373372688 373372697
    0x40203090307021215040b0a0222050306090d0e0409210504090605010c03020c12010605120312070c02030703060c0e04060b121b070f050a02100f090f0f05010c0f12 72
    0xe440c150715189240e180d04c0b0003100700500d0304a0304160b0803540d509000704060015012403000440b10751142d0129880c4036190223200c0640040349907000036079815400307080d001c3d11840c800521843c000155070301032905a034030750034140060901000045c03d5501c10841d0710a40800005a208424460302801c41c050390321115290382c2405a03400440310140c0c401703410044803d03031003404243c0115141c404890103075010b14204a43d4802c0501400749640907a070070a00300c8905804c10030020000c3d010654040f0f00d1100712742c0301c030380c01241c1440d008d18010750326400910301003000440382d61100c4103000c403030708140c029070b40721030002030450b0b6407a84a200800c50001c1e8031400c0794000071449070b0140d00d0301e45440100740a4020300219000300b0740001e000c07944428288042c000104011050702d54000d065080341c4411440c01400070b80e5490700c4802007100d481b408203004e0711411142c01682d40080100200c00e180000440c0c509a070307000c050340c0e1101545001c4000c945049d26608562105444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 373375188 1250 373373938 373373947
    0x6030a1407080327030d1b0f0203030a0e0f09010b030112110616030201380111030d0603030807050c1f020912011a0d05030427090506041106070c06050a030b0402030903 74
    0x680302d070810301c1340083d120b60000902c030b11141d6001520107980b90744a01c207090401c020340c94001c0350312104410107981480086041e01c0055403141060401950a5450401c4070081c002071010740b43c1d0030b00542c0030f030507424401449010002d92016865038041c1c49007501e180401e101040c03003603001070050b404000e5164007a001385602401800b41c0c8440301d03104034102c96400100761b80144041c524058184c01c50090000e1140c1c4900c1d03060740c0c2940d8000680ba030b506c01c80c0000000401003440b0843c04140c0e0b01000a603014000c0c0c084ea441e98078804054260000000605d800c42c854052a80050075070134066802c8a45904119012500e42d080000585003107682c4661007045420000382d11440d4001c41100000d00040251011101607400e54103007402030408600e510018038244003c803034034048510003840390002d14140031ba4001c800001500e00c280b0305004031441040700103410400c10300402c1180d144154000d009000d4036240c0016905824000181a68410303100d0810652001c00d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 373376438 1250 373375188 373375237
    0x190608070317030702100e070e0c07050d0807020303070e0a0e070309050c0307050307090b0103380405040515100f1d18070b090607062d020306030a14070803 69
    0x300c1c407200d860480000c0b0340c00c500d800380c0000e607200389074020388001c00c1d215842144000c00c2009880090440e040c180b41151920707000c008007c0d08122400d490700d05c1040300f4161000e000c0c031003190084110354080c42c5540d44d660010781d10006603206a030303084440b0702030000308401c001804600421556602081032065030070101e29008950907440d2080d0029074007041070b5500012641c00300c50b245407011131440b5407400160010800594a084841c0aa0110720078008011140780c40b00210511825a030310000421b01003101c40480e001407444d8000d41440c040c8c0009803610b194030801c840340303529005842d031042e10140045940009400c904400c4540396402d002a009a4420916503008401002d5494020369550052080b81d82151001070004500d8503258216403155401135000d0086491500050322483c2151408070414071340c100701e00c0d9a0061900031a8040c02c1c00a00500700400c0c2501c1e02807404200703000b03000051140c1c0100142e802410b2019001c48400303882032004024151 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 373377688 1250 373376438 373376453
    0xc03020703030506031207030804080d1812050306011b140f0c0108090c1810051c1101090315110d0c02060709080703170702030a0510050a0f110d051906080703 70
    0x503100300d20982060a000c6c0c800001c042c1540c00040e0103143c000c01c191030321304012046100c2e90185031002d42c240b241c0d0302c1c425041e4400d0805c1c0c1a03c034802c42007000614400c100e4071408240c8000b40010242e0f02406000251214441a458000c1400e42c40515465801a140c01d40c03d69038218107801081180b2001e40c0c1044c0600da100701ea44000c5e120340350150300060b0b460068040800b1040c2c4901c070110b000a45020444409064080e040d600380c4052030b8400f00c40c0940b40c00c01119416128841c000d25175100790014012290302c0000f181c1403504c110940800760a000c2180a5a5201408485803845442c014105806104d40140c00c15007031810009042202e80d404c958201d038071200b000c2000464417100010000d071421407403500ca5a036480003a04204600001030298814100740082440391503200c14081c0e89024400c2001c581001100703410364400141640310000c0038082d03100d9008494110580c030850209050071412381d820140e0341241d030550044a241d0307100880610030083d1a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 373378938 1250 373377688 373377691
    0x30801052d120712151107020d0611160b0403091203020c092d06030d090810091a01090203060103050a02190e040e0106080a120c080403030c020607060c030207030305 73
    0xe44505005803100240512a05101128803800303001e000008440000c800d011010213000c440d18100c02890050510317014010501c6492501d191801c541520a400e120049501003603000e041c003e000d2003251196401024218a0b0280480d801c1244050102510095440c500d10039007591003142000d0800414404841e00b080c0d81c072004c01d0b1045000720341c0000740c0c100c54500484030340d1032540e00c4c90301c442c610500020007445104008401d01c149490b4000c003807449804207508444510030302000131941c0013000c0c8038048054000c50190354075245590440c0365018000c00c0d0041b11040150000ca620500980c4201500740e40407041c441c00d507926000e1f20307803c403004075815403d080000f041c0d09049034101000006019942c41c2503121501da680001107002c4040e070081042035504c410350340d1241030000c0e0454040c0840b509580c511170142450700358541d0030050090600307003190b600b03843d20300407028141ea10100502500c0e0005071240100c0b04840c0c450b55000d6110303141e0745000341c1602c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 373380188 1250 373378938 373378969
    0xc041e1506050d090204020f070807170301060507080c0f0d081b030118050603160617090f0c1507050d0906300c0302090a06090e0c040b0f0a020c0301060303080105 72
    0x220002003011550001c20340300101d0300e4000000303104c455880003d0080c800c103884402c0d4000003151060522220030080c02040380500040f0b90140403039a08400b4620003401008080b9000307010007070129074520050301a460703441c0111180c2c2003030520b04518003c046940c034000103500d54104203450420103404280022403103009800d65040424500b20001d83c81d4505503003564441c0003074001c1d64204802d007a86800c06802585898481000402c1d403c4a0742082000070503c40103d8102c1000042030844000c915000d08040c462100821071565458045560002014480f1201090f0140314070300b0340c410f20f40c07201e540c00e0740b506001404945800101c00b5454030720003c404400ba40f003105400d0000040d03038000604030030044054000b4000c1c5180316400011a400108803142c00c4000c100940d034141da5102030a50319042c81035502c3c400d5000b85550544280312400340e14070780d44007604403201d0f1401074818040d40e43d80070908490503a030040e00020019401002030742071180c3c01c48034915 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 373381294 1106 373380188 373380221
    0x1a0d03051e0414010206040c030201110304030501022205040c080406110403080d0b0913050c090a0e01140105040606020a03021209040b030304060e0328060e0c041e 72
    0x1c0040c000c890450600c81d403c03040c02d41c0001220b910850703100c00001b025500315801124201e0005012a40300d120601004c0005202800900031106a00320401208060a60034a40301c4240764800c2d40118940258840c0c40313640007407020350081d004400410006160003042000344200c2e03102800c185404160301c202c81280c0d420480d08490106c1d04070032951518011400f003a400804004c2442e0301407660f131040c40c00c00100e0346d41d100450200002d401c1258003401825949a03820300d0410303a61103030060000d07141ca441540c019020b54030060000035103540d0003959408500c05c80880d81e440c0842c0c8a100b543c0d40d03400c503900605c40541513903151942d41c0006000c200d07140742160310034082c07001d4050401c03041d151605407160065003600d43c8103809484000c010040701e000082e8900a141c15406207480310700841085030116034014004100c0c10003450121000b103014002c028 = true := by decide +kernel

theorem cover : BRFrame.Cov 373201438 373381294 := by
  have h0 := BRFrame.cov_init 373201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 373201438 ≤ n) (h2 : n < 373381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
