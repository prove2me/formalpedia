-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5418
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:48:34.137028+00:00
-- url     : https://prove2.me/submissions/c9d9208c-2fec-4f70-afc3-7f271230fc8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 974280575 ≤ n < 974460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 974281825 1250 974280575 974280583
    0x409140c100206150d08070b04150c020a020909010f1509060b071e0219060206061518060a1b121106010f1a040b1207120b031905120703020c030c1804020103090c0503 73
    0x7e14000c4605940394206840c064921014101d5480f15807030a051151000c160046007075805590161a0a28035640c0c11542c10b00400b1003004010b01e81e8501a55099205090851076003900e040d89001c2100c0e0b602c8804640c658010460014181040c07441c0207014010700b0801003184074409403000c03091400114a0005a0009400101c0164000304c20004646003641888251101807a011031910225005000c00c02c0e607001440c5025010020300000458400c0705184024002c01680e2808130642d403401d51a2480c001c1102c40c0007802080d01700f051408041803050407241c030480c90044241c681115540e050354851218280c154042c000080c090300301d4802800c81c2044c07000d51040c01d01d018000600340fa214a1803050b06176250003a0707240300d80c40001d202d012414410204140031907a91078030030b29000101074000d5a04102080080400d9000140000504011820b84e074291084d103080c001c031181e584044841c50020341c00401c015501a6020840660145090b0b8a4940e10b46001c00e00e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 974283075 1250 974281825 974281837
    0x20408060f040b1305030a0e0604090204030b2e1401120f090b09030a0f1d03160617130318051005040602010515150c0c0409140c100206150d08 63
    0x240907104100b00402c00500c0e50700c1d60002494006034800b55441d01c5580d92405881801c0040c455410700015191340d8501c1520b005101c80481907595980300d15080d80001410b55200c04110090294807400b203400807030700300c80e00c0003100c3c081c4a100d1501c03802554ac3c0d007500340740070305200b24030490590b01480c030b028900815801c050b010426030b00e1881c040e00010f80091420740c3ca608240280d04015501800d1641030039403e14002d902e10441d1010412601100e000d126414840c19031035441285042d034200c02220595200c8004800e0300091a1000b01c204071040d4001040c00c0301c1080000f401617540300080482d003010810301c01c1d1101c0126403600c1e40c00c10301d203000c508080b604203c2c0b83e41c2402001c2d4080e0780500170f1440900c0b5603001ca0300f10581020210707004140400d440c2d006642c1002a4410000700810600024246081240c20a0f0900b0303529001d0f4018201c014017103007422000002065601d41c000c1c010341e0758a50344084c801c95051a025400744400c40c84134040341020014080d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 974284325 1250 974283075 974283091
    0x1050d021332060d2c011d0304050901060c030c020405280608280b070f030c110705010809030c07091d07080d0c0c08100905060112020a03080d02040806 67
    0x10010040311061070304051210039a40c04180341d040d09101074440c0710689003601e9041070b0114614220307500350401d00c904000b10946164825174031a02c200015044403210904120710080d1410703d0484140e100d00c50b40c02030a4101011000400c20244510540900c0600a02d0902003d40c0c1e90b0b40020240c0b041602c41c1300340c0c1e900100b60008070500140c041c891103208810f00300441132421f40c4003078840780c010301c80314889410203810b02da5a614030300032180c2541d4043c045d00c481e40381019019051024600690740003925041008581c0c5002c0d4500300a07400c00e03480101100c03480c1c48011507140d04d004040784254082400390341c591301070070407011000e04800403000c1550b00046c0b91910010307003c1030000103294040c80080000c0c0e140413450452060b028600b0001910312814294032840b03180d030ac500d4a510035180b80740d400c3c02683e88107910f1148a0001d59040e6640d800c601160701e09a05800b0f948421402000c000150b002d000401440012000150a041d52038411504200c001c6440340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 974285575 1250 974284325 974284349
    0x402150316140d0e2d07090c050f041e09090515090f1603060b040506060d0908070b010620010209061803070f0b0c0c0d11040917040b041706010302010e01050d0213 72
    0x848000b400408020340d17800c58000940101002c071503080d03600c0d05e0621540e507055603900d20341000075214078201d40e401849182d0307845d500c0342c0d20307000302504001d0b4000e0780350030034140c10001c1603e0316a4000c03c0d88440d0400010071032010200140361180c034020f44110310368490501e40c0314154100f80a600e4030f00689051040141d032942c203140090b964661280d511851811040000d183d0710b003812356480280120000540300b070740c1c4c90200b0540c410141c0c0906000511400010100d0303110100008002260b0352902c4a595002889400d07405418060ba60021060000404007110110305640d4860b004007190b462a03a03424140c3c8404405400c201241d2000040c20b00140c1c0d403c00038440560380a5404a140d44695200c0b07040a161880d4483d120b10f0b15480d18405100c1500600560f41449140d0750340d4607952094180304035480b52003209409400c00d80d03844444000803c9960417a80c047e12907140d40362101c001100d003903100003010070b40b40d5820b101c032400d401a1405580050132480f1182 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 974286825 1250 974285575 974285593
    0xe18090c19170a0c0b18030303010f150c021e040f020c06011a0a020c010302031323010e071503050c19050406090806130b091011030402150316140d0e 66
    0x70360140d18800030100c2e103500100b003071800654040400c0741214140c49030140c0355410720254440c00c2e401d440b00c00e82e06220200003c10000c034110313041c0040b9507400b0980c0c100303c0d298010603510403019210181d40400502e10f500492a0805442c04c0754490090001855a00800c080c0d4101d0b04110180c155950040e00144144001e080180511004000d0b900e4281b22032200000c1d46d5541403258a4101a004404100b0141c030340c040410741030758490801703281e139214420a4000c2c030700700300c416289541c20134454000e1010003144403415071b03d003c04850401020100140e010380401340031110403000802c41043e240c0d02071303c491a164240303075076115030303444c81c00784024841601c9800540d129080381c0b05000c103146005a00080d8181e005600c8422540e908240354101520304100300200e034102800742c0230080c9102c00541c4541e01c00c44258401e00034102c400103060004591300348810340c0101c122580d40d80101d0b821182c20401070180380c5051a50850401034810300c043c840e0083d8072044d04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 974288075 1250 974286825 974286839
    0x2070f060e0c060f040902130b0a0807080604060506070f020f03120703080106090b07020d02041e0203180606011709010618050403091e0504020903120f04030302010c0e18090c19 78
    0x16402c0481003c0303a0fa5410400500c60340107551081d0b00ca95404c51342e0000d1080c03066051810034500400c101072069460340100403001d441c01c901190b0290000d21103000054480c90715100e02030a403003015010a0401c080740d80c030f6035030115801d041641c0c00841c000072440ca90b07130104490304580100e07001c100e44501d4980b4000e024058103800075024040142c90500c43d1081c1103041d5402d02c3e8040f901c83d0a003891038001303c0c3c014100c1c0c1c900495203101188005501c800309400440c01030030001c00b580004080680c1e8662170741000c1d5022030025800340c100c82d0070110300235120750b0880f00e40800040d241d036454242d80d03001541503005101480d1030300100030516801044443c0102030040c01c941300c1e00d04400c0421122401c900030b8500c16940400c0c2048035031420084980e030103165284069848038915000085d9410901c0100c00660912441014a5110700082c609425024211b0b00f5840f00d4560f4541ca4110020315a802074030070607100d8001e9aa40201e506103903a00a20201c80702810260 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 974289325 1250 974288075 974288083
    0x309190f150305100e060607020d08030a0204060914030601060513090c0305040312090201080106030207031e020309090703090807060903111b01090e060d1407030614070e190902030a02070f060e 85
    0x40c84000381c107510f10411115000e200b17429400720048030942d0b0344003030610024928070080b07000600400408020065441001d900810030b50b5030b56181c1c5000c5a6403001100c822045403200d060705600200010010140144040d04a40341011810724401d40c1b00c1d0381c0801250218003018000a0303c2d1010300040c150049044031a8031900c40c2d042c0204003268002a01401c41803040604040e800106101418800c180301c003107071b10201e840d02005000c41ea9000b55290400e01401d8840c05654012502d200e019124150613254090081401c0c403a40b615900700910403018281c0502101007042d0f100140140111020010b80540104661100000060440c050741e00158402001c81d41407051030340da92402050600c0d4411030301c00300310501042040c14180240d000400c1039003096010142801c08500d1280310b50556503035480cc01c28030700300300405805841492071139184001c00610640c18150002c2d03920002e08039003d442d02c1640d41d2050001e6400b11410340d01903a5901540c00d044d10144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 974290575 1250 974289325 974289331
    0x30c040e06040e0703080a050403050712020102010c1704021005090301090605090609030406021903021203040804230d060902150711030705090c03130c030f050c0102010b040e0309190f150305 84
    0x2d07508000200e04102815a161200d01000e40b03520b4021407021702051055040b180510303440000d4402240e640c2806030741041101d64200d000d5401e081140340118454044807040305803003d0f018000b03450310380070701c000101000c02c100100b01c400c025a0443c3c1e04c00b4020b000c02d6134414500020180381207004282410009884c0c003580750810041000300319030005041c0140c84948c00f1080007601c40d40b600707a00c5c092504224006116010042009025280000e0700880e11a9550542500d211280c080703151801030047c19481031401c00d040002c00c1195002d065940d10103050400c846440a40a0210386c00c401c5086840c0503507800558860b050512040c0000c21080d6801925400c1800704003280c4d0100412100420a60140d0982404042d440c10700045420a00086158405003040790300c1d1401e14030035030301641c245509040981000d200c1c230914403040c20013450402c54104108041d40707406902184d50480c1d280c90104072a1840242d640c02080c6441031000d12500000e0080d0035a1401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 974291825 1250 974290575 974290579
    0x50d0203031009020f13032a150c0510021c0608070e16030612080702120c0603160e03010c180911091002011d07080c120c01050c0a08030c040e06 64
    0xa0041c0010040140700c0d800990f001018096207801c14a020203c040c003c0c42510042104841000800c0c44541c08000071205c2e0b501c8911a81c09000d2000402038404500c20341300104801e40d1041c0f03aa6104010b540c2082d40f00ba0f0580340403003494110103060b60040d419690a4100c0c2c000c0e08002144184103500050910310081c12415260030582e5030b02e00c100501c280c0b11042404031503006503200c0d600c4100546041245800d016200341050041500900340881c050070150740c18100d03e280000d41c03c40b810f040100303900d25555032101c403108442d4001068030244035805402e18510340d002c3c003910003504619030341c201c4144050b45464a0307000440d80030b110041d10b40007130380c03080c0910981140d501140503100081c040d40c0610b002ca0040c2800390710284001c1450b0030407090300c000840e9640c100c425010481d03c00020590800402030180c0488145a0748000f180405a50041c8060407010003510150707607541581da16803200c554021200002500f600050500c01210450002a000841 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 974293075 1250 974291825 974291827
    0x11090a0905090a0609030203040807060e0f06160201050d061a1207110d1809090b010302131404110607020a0e0f150f040504021c0311010e0a02011403092107050d0203 73
    0x205401c0c45403a106082d1014000640b00c118005c28503008208480c01884640f04a44001e13581d032200406030421078603e10b204945101110050f0315200c4142c1e07010b24139503641050141000d43c010341d002e5000008001295469450000780540da05040f01c1c5500c800507941c566a002c400e42c04083c201c1c005200006100010813a039019210000d40c681c10401c6904260005d1841c40c01207000610665002c00301e9103041c011500108408511818103c91003610240d681d160300800282c00e5920700c90301c02002e481010000380c0800c48a821480880102500251414410b500402c503108625000010841400010b1040c1c0140d4104555845426403403402040f0341800c0000b401425440c000310700c00e6403944042000d656844511b0503003102d4800c09000000c40518000e8541001d840b1509425460007050410300180400c20411507076050307544000c0e41d400307151000302940024009010922039424444002e0788440046034150296944031911001146403042ca4105801107050840d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 974294325 1250 974293075 974293081
    0x60f010f12031404032006032a1603091d06011403070905030d030906060b03090c010c050f01060e06270112060b06040b0a080a0605010c080d02090411090a0905 70
    0x800d41040030079103408000c0d5100e00001400d040b40c2c544403240c3e039440c620100003400401c0000b100c030b41c221420307061031486d41c6480107901042484d000454000300503000c83c401e030031509200c1072500400c164015034642e050021902c280c07103050b1500c0d0710490206249500502a4a050002050303000400158241d841d02d40640001d1542a06450800301c544c000300204042c0780c002c924200c0501000780841340d031f401d24040d008000d0082608140c0c0d0b0300e0300d00007001c18160414030469118600304c3c002003210801410044603101039211054600d80545800c0684d0000e00707010311401803201400c542d290f402c0400030001441d03141075031000d241c2c100c1c00031084c1a2008058440c11501c42094000420a080c2040c00140c07480700744296024400240c0402c541440d81c010f030500e10007070b40e5401426075501c07400d20100d074030078060b10b40800e80c6a52040d00080d4100300070002410f040b1805070030850490301180aa4071064100d0360a42400b0031002d03847c3c241040e0400c0205002403041c06241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 974295575 1250 974294325 974294339
    0x1211502091e10110f0a03021f11090d030c08040312031a03061b090909030406110a031409010504090207052b09031103030712050d0b09011409060f060a11060f01 71
    0x24914403c800340103240880082030001400b800b9117000c00201a10302a030150300d8004c1d1286c0001034410119491509504c1d15903602c0c3c81103441c4200301c503800c545030042c15010042d1426140742e0440411400c515924009244030000c1c02c01184600c0041c507070410248030140955410348285d5584204c040b45011aa65000414540118000140801c00d44462405151a1081c401c030580c01080020508c082000e001000b48103c0c2e482d41d03207248002a00c1c0c000140c41d00030111002d00090fa400700701e40303290b9665900510020302c05051107072800f40d030b44619006a0f00300c44001d652940003100390f500303400001d41118143c40c0b14200c003101050b5488070003404007007040c003000c0d1503c0c0e8803041c80041d540b820411a00c203113820100340c6032203c00c1c8900051480d8019005210281d007401c1c02d800007030400341c0c1300e141a2804040308008629440c0c00348199004000c1c0f02d254090f00c0b00001c0c0c240da4848000501c0c98420594a403a5070700c3c81244514640306020b414011402c0340030004001d40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 974296825 1250 974295575 974295589
    0x60304060c050f0a0804050d050c0d14090a03080309010c0e03150903210912070308150a030c150806100801030b04050304030b010e06100305010501050301211502091e 73
    0x156006200140191405004031118021414403008803d8001103851100381c2104003e8030542c0f0440441d484500b54600072a0540075118034607007150712541520560a000d0841c2c001e509400002c5079003484070410014000103855441600e4030240001480182c60303080c05208806131440c10718490101c10000030039550741e12500c00f40b00b1300d0b401e1800700d0b5070300070b05000310781c00d41148440218040b810010320404009007071b02c1620306071050591519440ea4054140c0d1041c54243e218a00c00d0754490b802501e011204090403a4400b05075400400000c840c0341c0c4d0300700079010126200e44050a400c4e0040d05404028010718032070740007207a4014030264080d008a040d01c0c1d00c500000c0c1507480d10b00d80305195020740c2d0001007001540000100c0d03003c102039011407003054112203e06c519032179140250105d40b0280182d40c00500104010b1000883c0100780000c2c50707505003511440540c454a91607840368400741c07180c52880d00026409054901a1401c044402c00e034100e020440340c595001a044c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 974298075 1250 974296825 974296831
    0x204031209080723040e0115080f060105040b120a0606061202130603020901050f0a1d1905060a05040b131403070f05010c1a0a0e0601060905010c2a061119020603 71
    0x103200c2c91030b419948000c1c01c04541132a001510510042007540d00f114003800c207522000c003010362150b400081c1242c00003000b02d00c400c65000a0449039003004c2c00c0c840944807200540d50440900844060802c201300035541544d8081e100018002c1c1c10701c040180f804800c0105209040c0c0140100e90400e101000c100d0700b15000d5003401030713590745100c0c016034250040c0d484a0740c9818000c544c081d0f01d203400c40c4070603501c00411551468200640c000300601c0341c41c80403445c0e008206008007848181402001418102110305149042550b00d446404841d03000b41d00010104004050410254016181b224520402100501460f03400d007000c00c660030500340718050411060130440001c0c404010390b40b07400b40b020421b4024032850180f0142c0068609200d442c0c02c80e00c9080000190f10740304400010a80744146e441c40f06401651b20381072a001d00802c4510116104c10307200e01882e00829001c10000c1c000da8861140c00401094042e0900346004002045449074216510060740c2c0d8508582d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 974299325 1250 974298075 974298089
    0x36060c03021509120a030506040c050309060f04061d0c1003060b1903060f0303030506180c040b031e1906091107020111152a071113090c0902040312090807 68
    0xe11507860f40d015034070740240d4140054000340b00003080c2e2042a07054000c00d102d210b0503202880305035a00442216540300031510712225411010103c0d1510f8107140310742d17401038001c40010a8011007055010300d42500a884240d2503404004500c01505041c0700c188040181350070104020352904d40382d04020320488180303c0c0120b1688460140c0c80b1702940c440030103080315a42001080f5100d14000d0020103080d142c4511034180d5200151030030703410180440c8603c80300c0028038180b070300d0700f04140540d0300086d040d600e90481c410b2610541c60007039441d051140051040901d80d80d0007407010f240455480d9045038001c0b501780741030b81443c000780e2022114907550a10342a00341000c0072241e182030203030340709560521410f0b01040c004400920a07002c0143d00b031010003240103851001201600348601c2100520100488288151a16180c400c0c4ea000f00440c4074007080020301c81d0b440b80b41415107034111880c81e0741d0124091090004890f14045c0b011601e04141e0150350521300401e50b25411403041d40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 974300575 1250 974299325 974299363
    0x105010c03050d05181c0f140c0a0507030b09300d11030601030b0603011a07020a1d042102150a020408010614010e0108131236060c0302 60
    0x2004040c4148110f606010a044080185017040070101000c5100b080c800c40407031107101604840e048040ca41d00c02c20304940c3d2101981e000d11410207503a61300b141d98401101d804207011401c4803410a00180320001d200700094000c050552602c54058940079028062941c401a04510042551030366140040b181d00c4041c03600390320820301c14a030f0388138100b1050040d500703001c01a144604039201443c0110800d88007485440c03c80c00500115000910610001c83c121006452504003071100511525001030048160f40c2d40742c02c8165250300d1400183c0e200c0c10b072480208424040c032039905006054911301944032424070450000d43d10500e40006584201007240810124003460b41260001d05009009100295490103d1981e113145040304502141c511040403040390b10881c66203105443e01404030410812903169129800c141e880d4100c140004140c9503c105641c0d1442c14a070403031007801d004141000b840000c2001c01143e8482c8003800180084100000d402041800c03c143c1082c0d840 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 974301825 1250 974300575 974300597
    0x901030216021002012a021b1804030206010f141809070f060207050a0603020405010909020d1116141f05060d0c150e19051020030c0f0a0308010501 65
    0x40d4801065901c0001e511880101c9111162074041d00848010b1071007021020309404c0310424010520b100d00c0701c2ca0b006030480c1205441020481904124032000544090a03800c102400d0040c0d024007510705501603481000100090100d0014904c0580701c2c1e002041c8110b045540070400c000c206840143c0b900d10080000b03110b0750800c05c440300c005c11200300107030881503440e400a51a50150b0059a010303001032980800c0d014020b000312021500c060f51116041307458002d020009400a0039000803080e00c0e000c90f81c800040b0740010b00b04c10b50184854030152031007403400301340710b50030401041c80c2c42d0860400340d403130743c04000e0407071442041001010907160b0304c2100041341016407000c0103040d042c07009000706840d801ca40301030308241e00607242d10100c001ca0b00b0810500301008000901420381c00300f824440d0781000d05070301204104c41d040c08620648911307041c0e00003040701280c0060036400810341c90328000307041241405a90700e0030040c0200640d01d0310000c05c80623050050905000c41c00c640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 974303075 1250 974301825 974301847
    0x180f033c21020a03060305100902180a140709060f0801030305040605071401090f0516080a06020d0b030d0e030d050418020a12050c030106110303061807120212040215040b09010302 79
    0x54403032071030400d40e02156181c60094010340144110302007900c1c0c62081600c3c00320304070054843e1244194006105800380418181d8291f807c10005041551440e210311074502940d0340300d0400c40c0110711031346035411017508204e00100054285031100d400c00c03055200410200c1d40000840e4140c0d41c852414070340d80d2219080c940041c141d168103904856107040750300b03010700815407203d10580c0d00c07400c107a504000c5411404d45080104d80500a80b68210b440f02c1800600660f0080480c80050000401c501c219000000d090100c80d42c190b40200b1b0003c0a200d41c1481c061101c40d070744420b50705109003410f003040000c1d8819189400032007400f07580000e0708082103001380c081071190368010b0014030552509248240c1550800e10842021504817080508618000300999100314800b070080247c032a6070441c450800c04002d0840000d0095240c11001d8601301030004104000508800100c1420301d0320500c51240f0b142412050032080c1404240079009882c41240d072000e10918000d41c0b11852001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 974304325 1250 974303075 974303117
    0x1080a1a1e12070302090c1903020a030b1807020708070b030103120c020a2c0103080a08150a061e0e030a03141c0902040c110709180f033c 61
    0x806903801102c881c2d40c1c0303042e030000161140581c0d109035a9200944c0355000c0c98400d5004400301407074403880d9200ba50302414803070381c00760480080c0707450f002c540b110018011840152038048540e02100d030103420400110707010081071004000702401800201c1c98000c244103c0c3c081800010f2241c148840a80300c003030310600840c2c072442c0d0000d101c0350305280e850120b085c2c55100d9a0b00d64040c120b0940001c484901c2d0b1602c0b4504881e00059900d140030b007406012160020024504456024030500700e942c1615440c20000240841c1c1e100c490030104070b0410034049481d11300b0680c0411146150b11180c6440220310541e62039410300300007003030358080a11002c103070246922141400c0700078035032036010046940007110501d0094508110515003810200c1d00441000303140340c01644544400c0000d14015401016255124455078100620643e0303040c1030710003100425400500f403500c404200d1603182d002a0311000c07401103a80b60b005d10a4640150742c1c090b17141c5030750a11803030300d48810030050101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 974305575 1250 974304325 974304379
    0x60a0305062a0901050d09061b02100f06080c0d140a080d150302061902150a150b030708010b0901030b2d0402031b07020d0501020a03090201080a1a 65
    0x482900c41c5403400038244001d04140c0952011040301440e10a0010080c12040f11200c0c0341c1a512185080500c1040b80c016104003c02213440c25603404480704203240c0d241689040c907965030702902140a010660000350303030790303c20302000c03030b62601408100d204c0b00040e03201c3e00104c0660307504400d207d8606040340001e50150395400b00e8003800c02110f0810203000003c3c50410320002082145080e18004d000d001c0700c807408004e401402c1040814800c0480280744a0092141d204442d948022001c0c15203690b20300307503003130313039031952102c400540e04003040034060050b00c501540d0074114501580c0042c00070406201b42c20341c0500000b07802d1890791298218042000010b0030300150944041c190041904c90640c20002807603c40c0d648030120b14150003140d00903a10210f03000b000d4541c0d1425420340382c0c07161a0482c0c2c404841c2866100103402800a400301503519240003440c1412400050400800141f2807070420349040d0f248100c1c015130001000da1802c0c141d40c0a00c2481003203500d0808850340c0303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 974306825 1250 974305575 974305583
    0x50f241e031c020a030801080d090501050d0605060412170a0e010528021f0204080a0209060a0e0a0e010b2b150204080c030c0402090109090f1d0318060301060c0b060a03 74
    0x44160b0b502c03680c000400e800b400c3c0c40382d13403151426070380c0c0e080e461f4442143c0d1012900140342d121081203103610070f0b0040c1000d02c0c404607002521a55034400950b16900c0755028112044040d4641401c0c4607560740c00010700c03440c1c7c285451138100d48080041c10310b03468403045814000042880b0104040c12040e15041000e07140c3c1844100d0041c0300046d6840180c40c8070309001021514003905c20042c1070003030780d007202e14100040c06101eaa035400c004104030018200d40e0001000100001d8004c20103100c2070140180c00c900043c03034005045040e080d50301c0c07212064000c50360740c010409040d070317444846600050002d5850001025514084240400303a102100d01180007040c0420b0180c00482d005010391012011507004030507801c00d000590040f550302e00c7c0801c410280402c2280a9500400b07403034401254001810040624010881d4000295a0303269520114450300000c00d0014039041d0390302c040742c40c2800c42d850144010010225224010810b0600700c011510503103c1c1000080a1a88 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 974308075 1250 974306825 974306863
    0x1003090218131205130f0b0a0c060f090804030318061d13150f0e0c03070f0c08070c05130603050309011d0901080105071407080a051c050f241e03 64
    0x70f00d4030024501c2c0c011034981401103031031000020b5a45841c5c80b4810446440f070300d51504141c107004d07054440f10041103003584c0380340c0c80d4150301d2496180c03442400031440c881d80710f06071600d0a41c20024a01c1c0014203042c8040c0f5030307494042c02459089003200110100e06044100d100c3d4021740890740c0c00c000c010300400c03414100020120300c84d5003010101c054482d404505008255a81c0043d14003000035140380c1070144040002c11042403041c0c0e0700f102101420309100c0311500090380e5511003984518015560303400300d144140081c1c42c219848407010303060064280f250900710f441d1a500c82c403880880b5418030006a0440d81c4400301102928165a03006290094960f500c45071180030b0002120080c00040c2940a00001005000305454019405c8000b00e0705214200c0b4055510f5400004001607100c050805072110341d809005040c860900c850440040c2d0501120480f80760301d05034148507400340c03085200003441d203c01d00e581108005000700342d15040c4030100481d01b8000400c01c01c80b44041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 974309325 1250 974308075 974308103
    0x21609020d3809160c0c03150c09050301020309070b340b06030f0304090b22140c0903100c051b0109020306070e010f08090f1902100309021813 63
    0x1d2000804001054410980b84508202d001008030010088440e904140442018082001e1140b007107103003282d01c54190080d4031501c80d101c3c1070f544c030200c00344078218680301d00740c0c181020751100c100030050505a00075429411702104d403030b4540445000e030540799080400c4524844201100c80301500d0003446c1d40040710050203031114410ba41140d400c0e01c0840c10003000c2017090600040741c05d82c20709504013441c14581031112100141030100c00c44c2d075200036103400c1303204101c5844001d018400030440d0f001585590b40000d99145040040154080e0803003400701401c07684000c038154500b8410078a0028410602d228141c40c0d1f07014800300c01c0700800c03142107540782c1c0b010150701c2000464001c8040b110541d54480003295000030504031180011444101844aa801860207541000c0300c1815121400e11000a092500d829050300c040c6090844120a095007842500b01c0298a00ca01c0c00f0b20070803035981c01007110a80c0004c401c00d00c840121002504141c0010071408a10360b0210344006894 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 974310575 1250 974309325 974309381
    0x2010030f05130c18020714011407080c0a0806120703031701050a0f030b040f0203010f060513060e010e042105121f090b060d0921021609020d 62
    0x194a410985000d2821002ca680c604031004000e01d000e0740f02200300546810071185003801a072903541c00190310303000c1c0000300010381580810103107180d41a000107004141200c1600120102900c51800d1103441428002107001130812240d00c1500c0703082000c941d49400d80030076000410410b02034024013805030048109588a081030044885004512070540d80b81e50400010031080e00c42c40940c41015001040000d520291041c1e0042c0251b20b01c0c1001c640c140c003c6403c0d01d01040c0b00e9000282d4881c0d040c8031900d01107905c40240307462107004008090070006550410101030059050640104001504000d60022444212402126820805034180101510383c0d009030b621403110f8804c9200091000404030036089002c0e10304042c84c424070703181445690007070280707414543e0840000c11006045000b64014030038040d104039100080f2140791440200900d080e14001011500203092254800e418075110000303884d00c0354001603507040540c560800034000820409100090403030412050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 974311825 1250 974310575 974310581
    0x3120207170316031103090a0306060801241421010b0901060e033711040510030c0302060a0908100501050a050d03021b06070f0609060f0c0507201003 66
    0x580302034664004400e40e510003141c0728041c600100c2e420f00746080381c54000c24030803d0100310b454500415a4900501e440110f10754014941050300d2258550404216000d0b0904c07500c10054159425210424158045a01304d45800d1041480c91080d00405c585c290742c032581802c03003c0d00781d03500040d4243d072280e0b1b585010303002e1050040d01c036244020002900a005844c10042200d004018012400c0811008051202100b03101440820190401c9080c03d420402e20f00070a0b001d1603882d10b80b04030b24002c0005440d4024254107180304140010030021300160708681c141c030b50441d1004d4440024900480302050707690300c80c804074400d02d003003d0884820740d07005074143d4505556030744050b604e80c400d10003030302d030b01d1840100145e002c0122020568410000800c064000a20b1a8540b08882d16a000c0711140300b0f6040d90400c2e0b4901c0002c04102981c4a103210100310150240401145614003400f1405200c0e0050091000031100300c40c401650b48052155880062243c0d5010041400c01002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 974313075 1250 974311825 974311829
    0x114010b072a060f0804030828020f030103020f060408190503360922020d0611030f0a05010627090e0a0b1503120d0612081c0501050603180703120207 66
    0x10505401350440118440c840107489150992503079051a05d401014441640c40340340214840342c10341c0620900c680c070341c3c0010040564900c4030540c882d4110700411400c09010f50b410f45c8190000c11081044000c08071b40c0f0803182c9400c100754001d558082c10114114400d02030100b10760401d080300d101e60440d42ca07088500c80c000c88039000030030381131200a00480319805e0f1461402d030f06680d910100d90b01c00780200c0300f007100d2014183d4038680c20240d031621f081d0750800e0103154100b040072040040340010451959480103950741d05211651600c50007604401c5e028640912040f1004030301003000400220200c02003a0f5000200715121081646035101c0c10f14040032112003418a01285040d20f00401220039144010080c0c1040c9541d800c46070030950010306d100203143d032140f0000540c3d4266030b80c40c605203030181c49400e6940244031406405907103115040c3c01020320700401400141c440d00c098950003c0301c42803045880b01d52a0180345408040c0d40010b04460310b141045800301d07804100c0e482 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 974314325 1250 974313075 974313077
    0x807020c2d554106070803161d090627070206090c190b0a0c05010f020d0f0905070315200a030c2604140a060c0806030114010b072a06 59
    0x120140c50b4000b805080c269030041840c0b201440c4508440e8240005407401414070004c1085207411480c1e600c41c506508100c58520b580020030385100941a04000c80d4032031440801c440040fa030120b40e0000c2c3c035100c400b8020600440c0300244c00a00b20075861154402814440c0301c2c007201c0e10f00703142d0080d034031001290000d10f503018100e0034a115040090810003a003d0030b1111041d040c0c1426070a01150300000c80340c80404c5824220040402c00a10501c5035072554a44003691b96007107501c1160a440314500c01642d60f5181002e00c4d004264086032907015a0790108050b6178001c9a401204080c090a1440c500da580c552440704002842240040c045030304161001c1c00882009a811341e211140c500f46500b41c0704192042e01692116268210b0780320748038000d240e01e2500c14060b828900303245100110f904640d1074500404044e000b050242d4062000c4000303102100d5104080e45900e60103105806040c1d1000c251070040116100d1910300303d000040c3c8108580784010308156251130030b481880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 974315575 1250 974314325 974314349
    0x3051c09050106090c090503060f09160e060a121a0a060b0f120f16081f0b03240d031b080a0804060605031506010807020c2d55 56
    0xb040e01741c0039081440c203d40c0d00601504203a90344540f042406034000308088001e014405485140c440700a011074054490b40002007003a24001d002d200c031b02c100c16009514076031445108400002c05240226005220301942e0901603102c0501c194040d2240d03420240700e404d004604480d541c0d03001805000001c43c140390040164682800114003804195a00b1101411404200100d103004070642034100b80ea071075000101500d10b10340c3c0c0300140c045800450090a002040c007000720066455046080403c0c100301d4410881440060504800e000e4004c3c10700c8403150303009803c0341da40807601800b00d07044a2400d50341c40c0069801040054211400c5510611300324011401341000100e921030088484040e9400751110350055440c00c50003014081148140b01c2ca01459840c0c502400c048008140001d1001580500107012404900700c0410b0191428000130300069003281c1c0f29022003642d002d4040046040030380d03803200c10705c111903005154092800340500c100c1c54007040f00046403608003842d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 974316825 1250 974315575 974315591
    0x70b09030105060a0b03062707050c100c0f0f0c2307060905060a0e0409020a08101d1207030908010c0f17061e0103060503010920010c080703051c0905010609 69
    0xc0400030807801017a03100b640900001c0d00307d00749135482290509503080300d0184181ca0305400009408200c2d40e440008030045850b40841004000b1000300c03100e414030034031001001c1c80c0020f00328090740c584502003165054580010500580359514943c0e0088a074180000300e200c065441170302c51100d1000b0520800d040044c5280c0b02c2c042c44410b55000034100f629003050703400116400303100d803403105501c15602d5400100581da4580c51390300811140340900241c0260417899000c5808440d81000800004c2d00f4200d4404400305005220008110b18035884070540e04044800c0c0c0019003121302950f20b020095030703449030440d01c0110219100e40c0c8521180d18000704400124005a4840d40c110100a211995100d98101503000105040c500051456a50b0000a003900c4072024291407d00801400c03180703400d02018145981c0b802030030000079036042695060400d03c034150000e410800045441461003116070303800c50214402010a00006600741071150081541e4851003954038039201031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 974318075 1250 974316825 974316829
    0x20d0c08010806091b12010c0e12030f041e050d08070c143001060e01080601050901030218090a020d080d0c0801050112051308130801051302210f070b0903010506 71
    0x550700c01c0f454138024055120b8402c02d24034814201001c29030b44400c0b034803a42041020244100100491160354039080140b60005101d40c0b4414110b000959410800c06d100e04408164120b42c1142c5400c400b84040e040200f0802d03414040070b400c03c581c003070051082e1405101000c0080c002040c040c0900c902d9180c3d0312009032a103d134202d00420b40010075001e005880d80c072590008904140201002e51040c00e00120003070031141a40c0215802a40540c014400c004041010902404040d90f40040a50650b000a00040b40001c010b00000003c0000174541e68014024202100e501610341c4141c503003145003041003a0041d0191515161901e2030400e0694400d02d0068101c901c1030311441034904005d0707000805440001d18204400d000100f0000014003140000c0507c0010791a01e089214185180c06081d15400b40610020003909170144001d6074840600d000c0303440100407111743d6500c80180040c00c0040c201001c0390b0a0041000c005600010407004040402044000304030968503081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 974319325 1250 974318075 974318083
    0x7031205010e1f0b0a030903020c040e07030813050603071e0c0b130501020f130515030c0f0d0e1608010608161a1c0605180415020a03090204020d0c080108 68
    0x41011500b01020000ca001c8030074a2150003180c88007803503606840c3d511452107428690052030b600000130350342d02d104401d059040c0006403401400f1a000d0000940c00500143e4803201404060300407070001810101c0c00391107150050041402070100e548a2408400c0600030340e01c03a0035051a1f41c00c510781c05104c61b40c401c441e0b00c0d848545c403040425940c1c58035207601003180c0b08220221101d40d800c02c50610a4094400a403214812181803003059a05020510050350506600101491310500600c52040004025100c00003075001085490f00d405c0041d640207030220f03010111640c09000001007461342048080d405545c15031009128041e07480c0401591030810f10500b46080d5000b8400b4041411040382641c0403850610010782001001c000011460b40254980c0e41003c1d9148420026420400da02c00e0300c5030b420034040340e4a0b290607240c4038003040040400d203100981c001a40c202460182c1c1c018a45180c002d0402c41d02d80e02c2006401e001480004000c001041500d40001034030700c0300203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 974320575 1250 974319325 974319329
    0x91802030717102c040b07020d090605091003060b18030c0a141c05060708150d0305092404030c03110301110a0c081c021e090a030b04080c01110703120501 68
    0x744804511850840542003090201e07086405540c1d006101201581130031940b50301403030080a4050303403820403080103807410a07498000d00510241c0d0f0802c10103150040309441c2100001e030b550500200e80f40d0800c9005184c5500001d42002000c524084242008060000c081d80181c04407404a01590f0412100105a1041c00507094200700c220240d4204080c1400c461180340c0901d03144101c41e030303542a0815070110b4402c40011148010403891075184450161443c009803024100b940d45910010054450320712414040c109207102403c1c610b001d64940f550781001444040c1c1c071291289404521004a840250380700c810034510b019403460103108980420400c5146a4134004040d44190b903800c0e0a80c1040d1041c0009100e11605088070503402406e40b03503c0c03280140c0d00d5038074044042c00c51144540d281410081031011215989420707441605903034000707110401d0b994070303480c000800b84164069803072070f5403c001030035a20000100c05400d07280d11a40310000c0111041d149041216024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 974321825 1250 974320575 974320591
    0x2040f05010c0c15020f0d030603030c1b090c020a14011406240a09091a0907140705030d05100905091209010c0f0506060f0a0e0109020a091802030717 66
    0x4010540c010510b507501c591092220b400c10503650703c060004507100c03071560300242c0c00510750002110f4050121610140290404001071425624000c0c2042103001c0010b18648454404405889608865400030149100c040c0081e00072001c0081d10380c03407001383c100c8030312381882c140410314072042c041c20b081820b81c080740142d02da54040411001508200032501c0d0b00e00c400c00c030030300410b4014000b0986400b49403101301100e480c0480b80c00484121064151141400e008240e06a60314010600e4000c1c80da41b40c091f003141d68404c03804901d841141c030020030b94400000c0310081031100760492481921081200624207603034002c68420303a141180d140070241c02480400d0140901341c40980a0707110113141c00044031a1a13074500c8064800002c01341c48035401802080a2442e0644a101c400c51081d111002d5080c40e004d2003060b603100601030b00b000345401240100a05100e82c984c0780051070031181c0700c04040c0c2c10200b40c0c0029030060716428005010b000d130700d680c208081961517000b4100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 974323075 1250 974321825 974321849
    0x61401060f031d060403140d020d090b01051e010f0905060c010609060605252a0e0c090307090b0d020a06090e07050403030e0d02010302130e0a1a1e04090b01060503060f03010204 78
    0x85e0b0360b00f240c000140070b40101881c40d0520130f0742e100145910182c240d03207035494000079007010359083c1000c2080c0c050344014880c0700b2110103281154031808200120540a003419084000e51580540d1a11f01a070002a001400880c00c8124502c0540043c01110a2070404211141c3c551800300c46034800d083d99060640e00c404d18400407240c8100500700c0c7c142c020044119088103e850101d0101c50340030b000b503d4507285560921606540310440790300070f0303014240b2615012044010941328400352040b45101c0340c0e02e0103840f00e03d4841c0e150222140b54014006030086403a0480600740c0c0c03038240100c203419000c030400111040d003d40b085406598041d11012000b2900070100314100d101600100e041680a001070340c11040c001d003c1a0150138400e01d00e00041c0741800042c011070720300100100f0707040c21008000400e40c40d40e00c6480b602940341034000c02d0440194002c5400b90030740141c0207207604c0050000040c181c0c1e0000266000b4101104c040c07109540402c2011b00b41d0040b40200c40500360 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 974324325 1250 974323075 974323081
    0x40c0e1b0d060f030501020d0608032515230c07030c060b0d05030d0b010212131a28080f04051c0311130e09120a0c061401060f031d06 59
    0xc20300c4050807441006000100c1d8058841d0030310fa1403041c180e8012200d5079008600302894030388a0103480050011a0b000310708250800c03903540300b003c6188140040c9001003144490a0104460390640d40481c6100c00b8408142604d0001340d40c0034100d0640c010340131010011591b0140e03842c04440d000f079010b503100b280c0c400403900d03404010841e420a00c0d80c804446422140000d43c10703c064038811542d4500041c28414100001e81480c6001c182d459542c1c008001192980c0d4404044405a9810301460046032185100c010761b01d120307000d0410b0042d10150f80018400010b61101c01880d1080d03610140240c13122a100402603e040d00c0081060308043e110340c0c0c0b000072062103601560a9844d01007440004150301d1500c641c0321104030030544000c9041404900320b80d5400039003010a00d030040150030351004070b00403140528541d110030020718000744010b120140e004a845400d40d44881c01d403550791200003030f0100801d4000000464100f481e8011f00309511642e802d0481a404040c01581d1707 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 974325575 1250 974324325 974324371
    0x9090a0b180412090b090604172109040606030905212206080702070e04061e14010e161e021203070302030108103c0c08040c0e 56
    0x4058005141c00010740040c4101900d080c5020728020303401a241c80b4a101030550004008400503081440e901c81d00704000030441d01d41e1400c8404544140034010224541c0c440c8880c102903009500d00b11f4a03030f4802601100f00602c9008000c2c1420444041150301d60b50b00095095980f204009011500400c0604034003080d1500d8030001c80d007051042a00c6c11108960380542d100320188401d00c1003e018174103001142c0c0200f05160040c400d400140f0007245806071001c1550720040000308540d40f910300148400300c1205401e41c00c81c500c04003e101d01000c05c101d503003400d0000d100d941400500034011440c4040b0105a034103900100d60ba035011807080d010511f50444200900369011489454440b103500f50a80c000b1318010f0305030340d401582d00e514148010345041d169601e100020352800403605400101c1c680f10140942840708074128640361184a00f4a00134082c0819961906000306014005c2d4000200ca124622900c0041c90307480d11510700c510341c1101214031810307090390040210410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 974326825 1250 974325575 974325581
    0x90b07020f01021f05010306271407120807020a2108030c0d0501080703052401090e07050630090703080726030106020f010c0f050d0b0607111509090a 66
    0xc6038041c012111402884c2414070440d81020034140c034026500c02c01441000200c0c02100c0c0144540c08070040040d0890382240c010603001c078001040b192105110150001d400c0c003143c03004081211441e0500a41c9062031240d90b408000101d1240d40200c0c0081082c0507101d4000f41e806007640d54201d074504050340c5002d1540c0c8043e10a00b0314040610000ca000030290003454040c02140c0d0252100e14910b2a08615040d1015002445001000b40040e1815845104103044036250440851186a002040c82c1012696000a030b000940000d0b0614560700300106c0f0000e03115841c07a92507107882d2a80c540d00c02c0c603200740d498200541111f8410001314807103030094074a0b04c0c051400d40d00e02150803554100105e41100117028a20000700c01081019014041c00012000000c001d000c451000c000082114240c10f03422004d2080c0890318680100329540a0740700b40c44040c00c019603c44490402d245581e0243d00200d20032142c80920803400c800703001c15a4000080904070b083ca0380c841900442c06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 974328075 1250 974326825 974326849
    0x30f1305030a0c030201090c03061506080c0a03091a0f10060201090c0501050304020a1203120c050702092a0c0c21030d1107050a150b0d02030a0219050a080d090501090b0702 76
    0x215920303280150301158104d192340f03004601c07a5200041c120442001c1ea8005001d940c0a04148182541040034416003201221000d031124075000412140c90316040c42181145081002d5503004a0b08000341c402c00802c01e079014240020395201c030543c0c0c44d90100e081e03600080300200f01d4001110200410750150007d1741d0858030050902603010344601c4211903024060b503080d8001890485020b104032018400d200b85c0850a20f4018a402c01e10f0300403401c0e035070001d0000452182d0b195542e10200102503000603d0007100303089190790f415000c2c2042d40d154080b03016a88500b600c002e402c03d84040c00700081e48020710210141d414001b030400220014043c1800500d5100070400c40c0c000050020301040c1801031284806006041d1410401012690240c10b4280903840b0410010050f0750000342c0c00e00d0140d41100d00301d840d6010848400716501c96a8049500301c2040e50010802e00d401082c881c910358203d540d200b501603611001101d10a01e6440381d00c2400104200c01c4000d030030464403100c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 974329325 1250 974328075 974328077
    0xb070b091212151206060d0809060706061a0301150c0201091809110a0b0f0702031e071505160f261e04030203060601050a03090803010902030f1305030a0c03 69
    0x2424a02030301500c80c581d4001820300206490540c10004a1280c0051400c000b00f002d468103500214082c1049954143c081c00203032040507421203107401c003d01c5030200c0d0105400641001d80b28000c40c41e10341c020300140e00481200410407031000e503107101c3d03a1043e07034102e801c955011900310f02c500c1c42c103a816603039817a000d9041140074071011900ca80403402181030144c0d92180001c0c0c0103c80e05244450028420300d05200e060504030400600034920181c2d486100704003205d6680c1c0c0f0b443d00c00030345090703150004c4c00c0401c001912015596a00810404115055218050f402243c05081290b840c1701d145042d0300d0003119034000c14045070406c40451440c91003440305440e8515084035490651404002c907011543c07000800c000880781e507061208036101e89560450030503040d0740c0007944034503004090b2070400c6408556060440e00c2a0820203209400c031001c07990344e5071204492030103580f0403100041c8905022000c0b42020400406507505160090041c508061500d10300316542180035000360 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 974330575 1250 974329325 974329333
    0x19210b0a0e0c2412160914060f0702030706030504050f010b0a180207050f0607140f03220f06020a26010b0c1f0b091e060f060c01150509010506040b070b09 68
    0xc001d508280340107101184400c1c1c0410003620b009201c002171400300244d81740401c10f1001040003e046080c0785004840d80445626031a0145020311101c14000c0d074001a5051180030030001d84143c041c0d0000d40920701520684001031480c1c07081e20300743c8500701030460300103610f18410040c0c4184e1303508401540340c000f40c01610f0700415488040c0303004030820b1802c00301d820803030030310012035080800e0024450719001c809040400f00c800e025558000204280c200a034400a903090940042c2c0850511580c004540c0201180a05000000390410790324403001c00c00881085030584000e48042d49686030300c0c102d145880c1c4c2041035200240d00325442500682c402d00c0450140042c000e14501000310740440300240c12010002040b004078006400c04144403448154107006991050a60741d00280c1a580a2890101c04c0702040c105d01c601804030b5019460310324130328a03402820507060211030b001c444e408000e90b01d4508000e21407003188288002d90404001301d600091488a003a503205040704161 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 974331825 1250 974330575 974330629
    0x90b0708030703140a0501140409080306040b060c0a0f11121c020c040e0c09070509031c0e061206090c041d130804270504030e19210b0a0e0c 62
    0x9408040075180c0c480b017191944c0c01070140007000c0c0401c0c0302105c0c089609020301d5401e0344a000c0c0340d2201400040c0610384900d0708030f11a4440f2000c40c5c41031160b403c111480f403412400e0010350345200501c1182e5030316010030f8012403454200940c02d5000030a801522800007c0280284450802c819031b40c1580900602505150b803103201e4103182000000180100e50380810402407080001403002c018007400b80f06155a40c1c81c0065404040c5103401103042d2100c160203c141c1c1c031079840c0c40c1c0b090f502c0f0070001086410f2044142c0c566009110603203001080b6190020000c400340030b14024004481e54400c3d0501840d0300c1c44030702c55003104055541d1500c041031622840142d600035000340c1c41c40c24003201c43c2003615000c030b10b00c04650310031a81c3c108041d060954004241465400c0ca26102e1075440021b41c00030000d5600400007022000400c088501c03e071084049170031210001075450462840c00a41c3c401a503000d00601518108040c3c056101c0c0758040014541034900d0a545001c02c0c1050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 974333075 1250 974331825 974331851
    0x20d0905010c0e010206060625140601060f020c030703030210021c09030309050601150c150e010609060911040b040902070311190b16020d140d09060c020d090b0708030703 75
    0x2d05122200e07960703185000c107000d00e8000780c58018042c142900440d81005091203142120901003000d0b115142001c3d100c1c429800c02031482803101d40481c60a0040070300001cbc82c80c1e0000c4092000b00d0040d001d603030002c03060104054542a1900c00139003d41c0242000c030844a07181d500500d02c0540d16100390217201d140080140440e1161a801c4012030380c2e5000c0030003840300400c409401400141c2000202c401c90b948001d12514070b00400400d03043e00d80f190803941e6401e90b00b020203940c403503800070003000741c0da074990740c0140c00035100f0049540e00d08110020fa14540301c0032681564513046110386064038104801000f0750100506408100095012041124092295030348919030705030281141c2000342400c80b003402010b0300c0c10300e6030303170b40100000241c036004503020351907030356508100100f5607501c501c20300382c0e00c10b54405080480c80c0040740000c02105074072090f06586243e0851300104041e1a040e2107504150045076100300c0c042c4408030000b807814005540c44080c80c43c022030008500300c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 974334325 1250 974333075 974333081
    0xf062105100807080d110703080a0503100909150e0c0906060a021510030c170606040b0102010b0d0303052406120901021303050c1018170705190905060303070213020d090501 76
    0x80820b8129604001d100380d030010f403040444001c540a0322a0708c0c43c6070784c1c50485c2e2083c104080705200003c030002d800690440544401012a00800d01c02d425040c60051011901c4086460140d03280401e09210703c200000c58141340103015044c3d45007501c0710300400041d038000c010b022085118112040c0031a200c10040c0f20301401d02080c62520450551524410072901034102c030b404081c03a660740d04040800040c00301d0b00840142c0d000104404d80c240101e01424045c03442503003116040050b00f04044e07260784114420b511401000d0306800c880358480300e540907800203040d0b01820074401c40600c440601070349174101000100040c80e0254805000d50740c503800e03501c00d464075001920700c07540e02d05112910b0b4104000c20700d030041c0e8480c08401441c140500b80e010303030f5065094042e02c8007a010741c1017040c28042c2170001c0183e10a1207981c00101160280341c00ba070691603062038003082d42800e00005586100340e0080000214040110080002f5007000c0c242d89113172500d403440c0002095081c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 974335575 1250 974334325 974334329
    0x313050f03100c090303110118020913120e18040302030318010213060504080c0a0b0d0902010201020c030c06061e01020303371a06030c040e2e0f062105100807 70
    0x14490001c0140340d0304007c0c0c000444038880040c030b079040c00654586200b00e120b80482450b4101e0348068592540000000045c018440c02012003210340300c50391007103400800c1503c00c1c01c011201f00140301440c281c0481c00c1e00302502c000300507a1051010408002d0f51405d200300b100c1c0c840d4001410700000400c401542d210301e81c850b00c00316100050a200b850020300c03006201003c1611110546407501a07151018411001c0741c0f10030320b6072800d0b104c0c04c6a1007901119031419910302104c0d120a8141d00e140d40300c00d03058032001d1180110001c41384120907035822581010708142c007d18116560000c407546113000d1004121301d5a800d060113940c050140030500032188140540001d0884041101c40024602c80b5807903030302c40c1c10b0034002c00140d8401d079003c450030b03600f203c0c3c502c40c11134031a0302060201103040410441480c07164210010015a212950001c44603180e030324819003603452200340d40c00c20031801921118211404600348a071842c4c1c1082d904110510900307203102d641c4841d01418280b0903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 974336825 1250 974335575 974335577
    0x102030c07120b0a0c0c08090117270607020a06020304111804030201052202120109020603010816090903080a0c180b09040c020d1215050d060b120313050f03100c 71
    0x40100b400703000c0108225a44541c8040c01045810041d500160280c884003000800101c0c00083e03562083c0d11030b0440d0314180d485140c0d001814100200c0d40c03c0f501c0e5002d90800f510351418208000b0401002031032902035010381e00a1700744410680c03104800303580f00a0003038a0701c00040700052099201c0c500701061040d44001c104c2c42a0820b890000e0a4610103001d400003038003a240040c2c040f074507071514120281d80c1140d000d00707410136079940a1f01400d55900007961000c00032000046204d0040740d01528031046404c020750b00f540b240581002c5400400c400707800070300e51070005a003c047c03680c060010f10080c2e05207007009000d007416500e0b042030b454110600c21500801c41c000c140c2410701507a003070300300385001070903c40c0f079a0748004080034004c0c4a212138007902c50aa49500205024440300501005050310b0013040a500f4100064451115114080c51510315034020420000c0150b512402c1041400d600c45440d00c0200312100a0340d02c00d2550600910301040760002d0301e845148003040302 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 974338075 1250 974336825 974336849
    0x9140a0302060f070c0602060601021e070b07050a0c090c0507110d02040e0c180c220b040e07081f090e010b1801150305040c06050705030c061906141e0102030c07 71
    0x4d481d02d40c500002641c81003003594408070a00c8444e031b070040750122481d07440400b00000c0d515250050b0340f920b1841d0303000c0c0b40c0340400083e262041c4180400c0343c0d45418051482e64102c00d950303081030401c07500020000c80000d40188000e90001e264a10848440351000b40001d4812905400003000c403215455603003190f522031440b440040c01e1090381009501740031041081e5914000c2d0225019215248010185c18159640340d002482602c01d101c02801c2e181010079180c684845880c164820300741c0e15900400d5a5000103003c81241d900041c10400030f24080052407841d019030840941540a0303d1081552140c0d03403200b46481d00101d002d4550700704079819901c2d501d4503503841450348885124004150a0034104404640700c414084220303050384c9026170303440d0001e003001401c5005040000745c6c180615001d1284000c0340000500101c254010108070b0241c0d1144602031501846c0030b40c42d005008030500038160503060f5131725464108103005072880c221165450f00d003085003940004c036031428 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 974339325 1250 974338075 974338087
    0x2006010906051c110103052a07200d0b3d050d03020a1709090403031a01030905071206110a03020408010f2306041d010f11040609140a0302060f 63
    0xd0b0000c0c21000d06106001c40e03d082104903201c020000c808403441c9814140c0300c1c0b01103400c1040e100c50002030744100610052800c0b52100e01c00009512040c016500926095800aa080e10b901400f00b5040c00040c11106c00601c1c4c0d60740c80a1070600206130010080c561604a00701ca01d0440f10564010700c0d074140340c1d0790490280601d80d01c401140d0040740c05890102001d42c0040d40001d01c8402c015000007461541c240c0580e2490042d04c904480290000c40070800c0c0810144c15401040d114000c020b0b018190211200c011001c662241c0c0c005040703a40079840c200a18032034540240881c1d4040c000100d040080c001000c1c0407644028050000030f13600183c00c00200d5070030f200703604014400f04800e0204002c01d2082501d040c00b46e0b003c18801407070030408600c031940e4580c0729000142e05030010003041180d180c02d544c020400c40e00c022904908005166025162110444081d00c1c050b0f15440c40c96410000e03c4444183c042680301c0d0030101c4c0c208040b006d65a014007401101444000d8195540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 974340575 1250 974339325 974339329
    0xc0d050120030f0a050c04030210080609090c0d060e030f0f040602100624031b110f06071407030c05010f0506130b06041e05040c05043003200601090605 67
    0x5144110051158482030003840880201d070351586030802ea135050003041640f6200c9131414144104e0348004c3d401034891681c140e200380c00c542004d214007811514081c850b0354020441c1d440d04260700c00e19a021681841c0d84c40051000d510511280c6041c0080341d0078110600000110355001c00c2c0441450000440c0800c00da40e0304000c40c1c08011701c03520b01481900d240207088180f41e00003071294240c1800c150a030080b4244290b00000020b08a2101010305500e8200c0140030b0b0058000503170201c0c019006c01922011002460318000c0340c2590b03c00702110007044140d04182c014290480400409206000100f0070900800014040076200060581041c03420411766499800c800d8024504213506144160b548030162802c55401034851000a03103408860084482960807042c0c0c031610341400980ca085d803140c0940b0540c3c0c1944280980c50040300d42d40c551044080000c00195542c1030140c600103441003480f138807003072040209107160700b8035040c0079410000260454000c080c0c1d02c030002c020038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 974341825 1250 974340575 974340611
    0x7050306040822050d02040c031808040503120903031213060603030527090a15051905151204240203180c04020a05030a0e0309031b040501240309050c0d0501 69
    0x100c6250f04aa032501c0c80c25011910407480c44001034411692801c2044e902e034001d8110703410010700e00700c0d41c09034014503180c01482c54006004060080c455131807004082c0081ca001c6415a03d0020300071030400c41d0400c80e2402c0039200030149100c451100e480040010060f000c0e0300040c5119407180d988480546000e280c3c0e03a110242e4030100034050240150858480307190703007500484494004a050359124001c2e44ca10001d41e031111350049900b420440d05010550480e000f0780301c0031100f40b42d12090b0b82041179000c2c050303a014040d00c81c1d40b201c080740004800070402d03995910140130500014a581c44000102c0e04100e03035011495040c0e100541140a040c000e03480c4000007203038110b0802c403a244000f0f0540c00018810080e99690341070182500c1c600301300307071165000020201c811a120740303122010481e03000301140c0d02860511001151500000c40702a4007902801d02031011024244030490261403071890aa405014002c01d09445880714548500070600400000c0750710b0308100651000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 974343075 1250 974341825 974341867
    0x7021c050415050f0316090807080105041a04120e03190302010509060603010221090304031407030c21060506010c020901171014010b070c0503071d07140306010c0302070503060408 79
    0x10010208a8419607500440a0b01d805c110340843c3c98600840506c0c05a40b100c0300c070781003680140708040000581034030542289200d03d2050015004420a0303066140d01c0250030358005210030480d9401c40e40310f038401c200190079084018212181c0f946100380d902c0b5075031000d03c001e4005035110010005100c50811445420860a900031480c0501041d041e031440c251022614a850760010042403200c10104107580143d0b80200282e03499a484202c00e50340c4078100d1004a4086000180024101c032034200004004509442d400704451403907030b034a400405006100c64144091544001d000da100c0c5013159003c0d0040601c0306104065050420346040043c60520000354208030035446c1c03030300c100141107045410200d00340303072148904d2a201d5200c440c260130054041c030a0703010026420403144030301089000c001c0f583c0c040c10b4403145001c0743d070b00b03501200e05400000200041025544107000783c4216030300910503264020740710b00009081000c103540503104c084000c902800c40803031440a20803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 974344325 1250 974343075 974343077
    0x8041707211110110706050915090d1409061b011d3d05070905100206040c05060d060906080d0f17190f0903091404060e0103080307021c050415 63
    0x41c00b5407850310301c10f96800c0110090500d240e00c8040d59140c00c001101a1100e6030380c0309505000d1841c2100240c0e85e201c401e600324100b1401c042010030507030351001c504810460380c990781d03044184014403413400c1554041031901307821030010008800005810244e4102e00c403198000807c007000d02d541c0c0d10303a40c860042c45102c200e13040b0180300750441c9045072100280300c900c0032000e035412100c1d0310300b1250324584002c0340703189a0814040001c100d0340284800c045e11401c4a00307040c0c100c3e10210899984600715030051401500c0c0500b400189041c3e0068000d02c82e40b90b101089480d00c8942403030581d05246c0c000c210396800584444460340d0401c0c02c50746203606c145071901076001400d460100450020346140c45095580c00c4400740c0502a41000c01c02c00b00c50501030001403610f00e8001c1443c5120320800606400c4800440380d686064000c400032185041d4a00d42c890b42107858103542940041c24403802e500c5000e0140c1c1c0005187d1400030300806413600d890b0703259864045500803448a0b030710004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 974345575 1250 974344325 974344337
    0x306060e0f0d06150303081608040510050a0216060b0406080a0c09021815030906011a070305160c1d0105040203061302070c0e090703030306050306070e010804170721 73
    0x103140d588412100e001c000a04035030411440a1905040000f400c090321100c042255082010050541160096000340b94007020007840c1c3c80214070444081c8403d81d0700038007580010303651401c040600e0300500d40002c014000149084981c4a011075140301ca003c04583c00e54840105c0030291030203100e4000103001c80310103000c1e001c00755980c03a000c417065802950511540481e489400b04021890300144510280100401216034403142003507810840314445036104441c00858480b0b00c09680030000103c4451082c1083d2850307a041d03076607402401d045d400e581984020304010072050305140c002060641c0030440300d10100800d4182c034041c1600f013a4003442c010410b020182e11740008c5007111085107000103807600c140c0d02d000c1c0e00c6040f01d03501c90131003b80c03c20706000442c000800d881c000c6a200e52810460313a59980103041c1c41c1d090407140e41d40422a8010b2024055004500007513005200e83c41c110907506081038064510b40140505640900791a544004000180400080c02c500c0300d041c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 974346825 1250 974345575 974345597
    0x106020c091506120408070c0906051f140703050706050c0417010c0c141005090f160b0405060c0f1207111c15060506070f020f06130605091c0b07030606 67
    0x850418490311813240088010240020180700c540750988443d103a103c180496072030340d030b1008500070b000c0c0c5000d6240f041841443d0402090104417044043c240e40752980140d616200804e20350f5504049001d40502c681040a800051524810346101c0c40c1c00c0303107119494174201300c0100c881000e4800d442280c1e83c50009810381da280c1004d040042503621688581018111074a5a42080003904001d4003142c2040180100c20001003001030f59140c1000840e40d095401a170f81c48481c10041c803074461150404c000912060802000501c116000d1004442d82481c40c0c90a491500d14030070041c014291000c203103101040314480341d00800e600c00300d424400314048210310b031000818181000f00030110114034001c1924040d04038000500005081d41c0c0c07583c006044c0070000001000c2c08a103c1d061020089030646030400c2038460301c520f182400391440c2e05040040e58544d10070200c82d940006020742c034441c00400302c4980351155125289000550a10382400b506444441d04020180700c0a520341c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 974348075 1250 974346825 974346829
    0xb0f1f140a091a0d0f0902150f0304081b0d020307170301081b0a0f060c0c050d0b070320070303140f0c09010c1a100317160f14060106020c0915 63
    0x102c50590b0181902e92482000f1588580c1d214070074090742c850403d042030b0141c4900200c69100f0840b007070003038405040d91081008107021030301c241c41481061800c2803020401003031000014010410002c84800f6003940060b482920341202001080d006901c0000e8110030840041c00544940c5a0318010500b154104104240c9030440c40800407881821720000000d582c0d2076a0b0800e000340300280d288030250f612000e000b08800c25407202900c0d45030040e200000c62703061004003040c1d00d580051103180d240d154104100c016081c05104c1c030f81007000c0100c00c240c10780240070007001e410b4480e132400900d0700301161008070080c82c010300e00015403030200d00300302071400d00074100d85140609181c4909203801d00d01d496440080c1c90803056841360010301c1002400c42e5a100341c101502c0c003850100c0305038510010f21407514030034000800c0396100305592403000190054451110a44035010340b000d40c0c14500203e0b071408000b607000c10300613231004003801c249040084000f07800c8104420643c0d000803078200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 974349325 1250 974348075 974348087
    0xe031201031a071707021204080c031b01200a0c0603050405010b010c0302250b0703020a0c08030414060a1209150b122509090c05010f170106030b0f1f140a 68
    0x10007481303030088103000904480c400d1044812905c00d510070f03240c8854a541b11155180c41145000e4064843c1e13015035442a05c18204040664105a58000303e030800c5075002000c038115081c8040a80c848c000116000900001c1c8103005041a950000f071946401c0c01c1881c01c0d110400038032418441c1664000700820b40c0410345480d034210014161064481000a001d040d0b00e10740e024150800e80410300a040580c04280d01841030b0007009000d40075502d4941841e01c030b01c0350780300308271000780100700c0c10b841030030024098110034600d41008040070b0000701c9141c00b510704033701c1c080f00d180340041d551000d485d030944981c1c01d80040a490383d05c2c5005441aa941d80d440610018101400030301d10041126a40c0714100380c0502000407091143e40e009142054001680307001345408100380c030f034034003417454810f0030f4050440cca0711520002a0340380c200268014030300e100b2502d0b0000c0015556480a469110812138190b01e1f00c11495003514103403000408414100f040007540e080700300b100ba11071980c410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 974350575 1250 974349325 974349347
    0xa022415100e120f0f060f0c0301060504090c0519080a0c032306190306050f0f0c160c0906030b180f06070e0a03151b0e03030d0f0e031201031a07 64
    0x82c0f049001c07181c002100f5072401d04940e40403c1d03144602d40c943c420000c0c01060b002d024042d031450b14030702038843c4040303000756000074050703103001a00910040100000e2a002803890002c0ca0800901c3c0807044603112081520306410100403811013020301680e1002c6200b0f0003100c080501d0104061800f2810030413903411441d80c0c014034100c0d0039000c501c8940d645000c005a80c440301c66843c10040c0e8034940701c0054402181d07078010010717100d00010b02c444030182840b88505003210b061481c16000c3c003090351110700c06c0700c4140d039041c0c198000172510324001d10484000d14010412030001e0303c3c0c50540d8004800714a1174500094201c1115000810f000048043d0002c04908004515600e0003002c40d186003900c1d4070160801c80c03a03140d0b81420804542c02101c1c1403500105a41e10b5120908040d54444c0c010340b2441d4140d40200a030304003510065000000911f121400414588403e0f114285940c110341d007651081d5444074010400c00c080a1101801000c00070301058103440c2116014204043c80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 974351825 1250 974350575 974350579
    0x921030921031101060b04150906030510030b1008030c1b030304120b040302190809040c090b0f0a0e030a030e0a140303040e06010c151a040e120a022415100e 69
    0x44140100c0c40d95080d081703034020344405c1b150591120b5a0b1448c900c0010760355442940030903580b50005c45c04520034000d01d4400e400c03100d4985c1c101e0740346680d1018031800041c0704911619501c20081980c50041c40106801d5502d08001c1014400301d080c099503101108400380e01c41d0f130080201704a40e4641d844002400390f00a118dc02a039503440c201a400c00740c03000d9580503800038003215007040105a00142540020546d81048401081201030f00e07200f000380114900b078401404078146d0102d415008003c1c40c0d1841c50216600f002040100f441d191403030f1001c0b000b20350f00c02100d2000342080007928000301b886101c699400b15400c0301281d00c910680c010022003001d03c800185999024406d1000c44a6203d0010381c0704480b03402420f0018800c450b0009a8a202c0d4414400030380380c24080c030b91010980300043c05006003040d00d0041e0650014080805500559180176007000300c600d446103010640703903800324092411054543d12400c600110601c5200803090350103510703900c25000802450300f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 974353075 1250 974351825 974351837
    0x171603020a1b06060e0703020702010c0605150d0804091404030507020d1a1801050c0a12090c0b0f09031c0210092609030d0e09070807092103092103 65
    0x1001c21501904038014281c1000c0c0502d8004080065641c032503c01c858611110545940380e00c038044080c0c0c402e03014040d00203407a2032003480100c2c3c200ea1000360028908103400225020714000b042c1d8040042c2c005941808010400300410b00f244d0181e840d403080d00803010007040c03900342d5000e0f100f0300a620000c0d00545500c04008100041007030b039219058030044280c000d07482c0001900c0c115900c42850940780b5420039010604800c4042c1c1660f91751851521200101400450707018010140e44009a41e4202090b10000b06402c640000b4040d010500407117651750f0780e0b11801e061404090010b00c10b105003c0240f07428400c0d5010614020b0506000404240907144e41858094a80b05044680b001c400d060f0312254420b481d413004103000c032410740989030000c500c143c068819400c4035440c590403410060000381c01b10310076007255900c1001070401800722511200c06000441d9600c1003400d01030403d02c214403d05400c0490200100a1001c1040c03003280000398040d0180301454000b020b210b8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 974354325 1250 974353075 974353087
    0x130603050402030705010903080a0f121a0111031624110c0105280209030a080c0a15050f01152105090c10021b03013309020f0405090601020307050706020c0117160302 73
    0xc40340d003406240c0d080210b0140900001d00b1491403041030845506808126221200c20708800c0c080305643d090258110403100002181d141c1085000310041c040912600c90303540300d21804160711070059441200e003200394d1182e030800c041a0031544050b05c1d02103540e9048072030748400d00510072082e15000720340b00056102c8192101003032a10004000007000305201180b01d41340540c0025120720301038021580c4810259090400000301c035015075151520407003803401486820142003004c40900b601d0328045503800c807040250034240c1c20f04d40101200c0da80b10b406111290804000e94440e800c01115031221050404001a640302c88804244651190b00d01c4042c05607a004c0d071248075140380c8484800c0300031801c000101541c0382c0070b0101c64141c0312401c2010402c003041d44240c90100030021081403801d800e21080000d080304c010100340c1148402c012000004038140405070042c142da40080221010343c40001d002c1807007280350190380ba400001000010301c1c0010006500160314140165128 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 974355575 1250 974354325 974354327
    0xc0405030f0a12110f0f030a030c1107091e0608030703030b090601090519120b0f010f1206020d09120f02010b010f140901020102070c06020606040b062d130603050402030705010903080a0f 82
    0x1002c421780d4007040b802102c008410f0300070301000905441031203a4080140003000013051b140d103c0d125418010a83c84182d003400303180c4081d405600f808081c029040c60f080030380a69001542c20a402044503904007207a84010903404d1f024140380f002c03088401c040d0381d150407030008250344000e20409200311185100316460058030300e51900a00110616184c0f10040703030034000c010243c00e407100600f88421000008074074603010103c00540b10b02094240405000d915542c001e508a240004044c5980d90f444c0380010b2800d000b62136055100340c07140407480002c408081d007103511001c0d1940c1800082d5003003261480c0c2c00a20404043c20059069413103503032a41c0100d00a0107a010002c0c05900c68107000709500d0340008211f440341c1811034050091007600c0b024098035001e050070209030146044d082c1440040c3c3c01c1c10740d000b14019400d00ba800c281580740442501c800d20350011000c250748000f13002c150f040a1140c040508000e0034105c0540e8030310707a19044203116a80c104d03001c02c0000090b5030000303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 974356825 1250 974355575 974355583
    0x51903060e0f1009020c0604110906031c02120706090b060402160213020708040314060a0603170915030a0b0a050a031721040b190506131505090c0405030f0a1211 71
    0x84d10240030115165030004980a0303513611305840c2a01d400c05030a0001c80c3c641307085005144643c02c003034041c04208610391070a20280300e20722800415409850300030600d18002c14042d0a00030300801000c11155010f08020036481005848180164010415204e441d6503a1a031507088590644400076068110640b80000740500c0d1002012008002000018410f242c01c16003030b01c0300340009035101912440c038941c2c11160948001044550f00d152007041402015025112581000e801e00c1d40a50b80c04030100103030340c021034140c0c1509a590210b5000c0d030a0040c00314000d00404d0f01c4d41800c0b1070035501e03843e061040f001840d92002c040002d0320390348103514419140c61400d5420100c1c0440c20207107005214540d00701e030b13032101c400f01d01e80081e208603805001d018010000035200b600c50911088800000e000490382d14010310700c24141c0041c142c0c440c08007180c41007400100c4280c996013800c0416003803070001c010580399a4080c0f003640000c01d0354800e40030150f20796402c00c0e4495000c4209601d0038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 974358075 1250 974356825 974356829
    0x4170d1112010303080c28050d11131d131509030c06050c190e01020313080607020106060f090b03060d02040e0c011b03081f0506030106051903060e0f10 67
    0x224203804100e1554601c0d0285140b0b0589110307456801259a80d0300070304506015040c0c084001d03480d801c1c00104155088502d03450003030b409240140c43c0c10036103507800b4180d400c4034013a00500040000e8040e543c3c40c00c009000054500c41c07060441c1d80380600002c060642d40908425002d41581000c00c3c1000726200c0901000100000140300540003410b01400c03004903800207480c0203041500068334a01c200d0100e40208038001c01140501400103000c5400d00c80e001d030054150b20080151107038100344c603039000000305485030041580b460050301c000d0941d1001c1d400042403088171800500503075048240c3c1802d80d454800190f4481c0da50030006281210302c0c0c03101940284c50300300004441e0b000498040c03829002a2201685444840804192450015000f0340024280700200340c2402042050325a184441861408800e03165000110705074406c1c2d000710007103040018510150070300b0030301383c003889010782c1420001c251034190036240c00340d07000f48001c2101c42100c0003e401c0b603c8458420300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 974359325 1250 974358075 974358101
    0x1321020a06080115030207050604151805071505120112030909140f18101a100f03140f070f020a0503040603061707080a080c070302030a061b0804170d 66
    0x14029507645001c0c11104080c000d150080b10300c400383d0341d2881d00034000c55445940c000000d1086684075261540c0e008041d40307882d103045840b0405d07203115180f28940c000c020360180010f080060b10f4442c05064101c1c0044031380342800814090003039108896078038241101c1d1400f010069000c0ea91408403038030030341c60b0080c0c5851440c005050050030800f441c8075210300014513a8072203903110020303445c110162424035003509500201a4401d185119006000002802041040d44040d1600051b00302c020717070001680003c010b94071501e0302c11b45c94059140d001c8107000f45552141050f4002e0b04800d1030080c2140c0501c048041110501482040b036241c0580d0844281c0f42c6a684548000b0058041807180d8204481c80e0803400c407a0913004501c680072542080d000305000040c0340d54092068010550400c0340340510700c00000585c6040c07108002e0244260000a51900741d00700c1a00b02404003440b40e405c105280082000042402ea2290003164900c00019140c3c1c0807050760301e001e041c0c00724004c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 974360575 1250 974359325 974359339
    0x714070f030809010e0415060f1704060209180f06090403120e010f0c0e100806030313030302010f0c02010513150f09080711060304170f070803040c0f0605132102 71
    0x20038802c1040181070291401d9035901d038022400400c0109903608420281c0300d80b0b80c5e100c0d0420600f4010703028443c0341281c600300a4900d03c90b50212440c0841c044800399030068000903c040d0a10703244418050031a0741c0c4000490f2410700401d641621000200a2800760207004045000d1501034100524031642d90002449000501d0400602800014041c0ca0006040c4241d000403280145001004c0d0070000d4401070f1403560b4030f442202c4000010380b11031b4040c00208070000352042c55074440360146000e90000300760400d00d0310310b040464180400038011079240c6000e114402e45a440b5000049800400d030350402c10002060030300401130580c151807071915101000040082040243c5490360191428034003800040d0103101c0c071032000720b600814030714821242000811948001c0d2161206250707076a810402d85a8891405500030b49080d150410800c1d002c2154034000101d900192800e494050f050110801e16030000140500800e181100e00301c0050008203241042e0070034654004200ca = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 974361825 1250 974360575 974360579
    0xe1b04060e1f030c09061d04090c050d03051201090207110405060301180b0105100f1b030302070210080a0b040216080903010e030f03160305010b0d150906082a01050714070f 76
    0x83c0040c0469064200490305640700051550b0240d2814448404400180c08681c403414080100801c4114030032141e40c8541440415642c4800644000c90391181d01d511740e44950400700701d051058164400a4064010002c08002400c2e004288511140070b44010845858510000340581401c14011001070070701c80c6904207111288030218100c0c0c8c029180194111117001c0110b0f1000e003880360744404207003035000140411007000c0400c51414040d140040c03d0241550000f002000c64012940000d2600418406050418402c035000c2c000116011486c26540c0d40c00c0e16031581c42c040000d800c400c0c010a8400c0251400c0d000b0300300c0c2000303002c2540e650310f42c000c044041c650030541e404003c156030602e580c0c9410b8040d12419041c1d41c1d0f00c0081c6400d0840104942c00508205102441c0d46031880400040e00a4240503000140c4002c101405d46c1c008043e85208204c442c942804900c0c240105da1b407152643c0000480304c003160001c0103c900260701e40181480c5c81010350018400c10891580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 974363075 1250 974361825 974361827
    0x90803091f3e03091f0201020705070b0301150806011b06020d0501150809070f03020d050c0306180c01030b06041406040305240903090a060503090109080706060e1b04060e1f 76
    0x1080b1062450118480428109105141e40e03010f41c1d01c0b0305070003092200122160100c0340c00c0c400b403031085600c00940742110655896040121907402048140d0000c001030241003d9000d40c1c80c1c1034841890a0300310342c6840e0340003e1080741410200c03d0000c1180c4104014414160111004400011424841541c1d203400c04141007034409400c00028070032034003081580f04085540001c94081800c0d0040d410b00316000c00440000b075900881e0300d44540d9509620341d44050003070a10801c0d20a00400e030303060164000d503041c02e0240a040f41010f141c08070f0480d095440703400f81c0702a1660702000086942c0c400e80481c0040c403ca40003e0010b100d2020080e2520703030740903416201d61009454048103900d440c905e1580e01c2c0649000c0c90760106240d28203104652040c40076681c0450070400200f1003828a45a29103940d1104030240c0d00c1c01e441e02400c0c041c546448904c0c541180b01991514401000d082c0900c03030a020398040e80c000c10248281d6074800b55a403440d104503c0072900c888102c01041018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 974364325 1250 974363075 974363147
    0x5010e030306121c2105100807090627090b0a02071518260a030e0705010801120b0604020403080309030d0c02010b061b0a0501090b07090803091f 64
    0x6036280b14541000200f00442404549082c4107000c0442d4008441c00038242962480505e11415190b940210010350905609018403409191030910410782e1604250149042c43c1d07642d0805600d50342130075001c1020f640786c141c46014001840d800c101101650360110f00240454400c09000100300b0000c0c01003000c41c0b5402820940e02c00c01c448245611100d9001090f540c00d10030315074005000007040c0000c501d480000101000b95190005002802c0d451107030380340d0b00b0901400c400690703031700d403040d004a204114002c00b0300402d003400f000e60340c0340240e0f129601c080305800414548542e0042000340d140c3d50150780c055544244025101c0c03030b04c00d510742e55a40100d4070b04541e45041081e4030500c9401845001110340000d0300c0c0c4c600c0e02007807412504444408000899651080354101800b02d07000b031260011662080383d0071450303401c00c114014a1075510340c100c00c01c0c5800820201041d950b800f0881e1000700042c11250704928070841058508442d020602ca100740c01291604502d0880d0304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 974365575 1250 974364325 974364331
    0x1416030f05250609141f05160323130b090118080d0f0c0e031504170f09030604030c0212060709090b061e0903190c06030b1306091a030616051605010e0303 68
    0xd06540e0441c40315806c41410350303100359040c5400b142030750b80c02d4100500c241c020306408942d803010000c1000c8a00b14828808204840754072480c50703034420200800450310310441d0405010742c000d01c003034001c500d0203034015481030100905040000422500060050304840540b886003d02080410440310001c0c02040d0303901c00561290080082e0610880403004050340501d4201054441428145600003502e51202c40d2544240340b051004800b1035030100100c42c801ca1007603541111b50f40c128414012440710351508800c03075412000030410750a074084084e17011600c06080220b048412040820720601c0f030181c00c880c41c501104030f01c08115104e18010044481d00340c1c01c80300c10302034480d8600c00c41040c034a001044460002c40c10007005220b40c024800e00c20f00184002991104d81d4450812603109501000030f0549a109155684201e015013009074081600a480350349003004000200f04820300c41d20090142c08110704646180110ba640c46503a40306000304240d44002a00942ea07400031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 974366825 1250 974365575 974365603
    0x709110d050109050f04061104030b0112120206010b0f07231e01020a0c08220806040204140402030a020d05070b040623040b040303030b011416030f0525060914 70
    0x800041c03190f2a500c80c0510174810810790b601603840d00d07500d42c0b01414025500c181100401c0c4001300c007040426819a008082d914628070204441e440c01c01c24040000e03000c8000e641211004100003903076101152480c00d50140c0c130690f030b6000742c0342000c0c024407200e14542c484043c50180900c0d071500003514000030000d206a071412a05011403140c01d034420304540c140001c840800400008030504003800c9029190840440740d01c010f1285001301c00c806620070740c190350158040c08298106031060603111310311866810114a01500420340d03509288178006c2c0601c01d046007100030b10400340882c2e4041d0902e070700c03103030340c3c6a42d0b50384020864181040061000c0800c00160502c08407020100d50844100d00c400c03a06043c03954030190010110011002d05215140701103000c030f080c000000b00320b0317072003100300d012018045030400400e1400300f052038206120040140c19441550714085001d4140d120a06c0d02d40103030545002070140c402110000c1070020b201082807405000411001807405031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 974368075 1250 974366825 974366831
    0x9170d0518120318010516032301051e1c0506060a030507061103040801021b0607030504020306150d1b031e08030a02181003020409200f030402030709110d 68
    0x500c40300c0c410720545400308101d90703400007100051211041d8042c682c00b030040c820103215109002c0d0300909460041ba40b4080b400303118410209440e40511a02c2d0f0601c3d4a0312503c0c1194441070b0054040385010b00989100c0c140039503103501e0f003090f0480c0400179494054490560780b124880c0c0398400d80c451203411030b120700400c07000824038109509000201c1790014014058545400c1c004c1c0c031000c11545402949000801c004224144240018003245032040c103401c51002071002e0550420401501560400d414941840003594000854541000c840d0005441c00e4079100001070180001040c000d21903401c104030841001030411004040f6801104500395090502d0040c898a9288107001013003444184081a040f14040e03018204861a03107240c032900300350b00800102c0c0c40b4203100011000940005040c0a800d4503402401e0021210f1500039804103c0000d911502d0b0180311102c60b01d110007c000202556070400c0242e008012400d0200702030030614100982c1540308101103520365003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 974369325 1250 974368075 974368081
    0xb0a0b0303030411060a021606090e07020d140309071d0912120103120512151e010e060d18120e0d1a18030c07170313170109170d05 58
    0x10040100c2c2e20440e404415001d00b41d0108080008a0708054a036000318816021011240d420400c0301c1009410035850b107036483c0d45001540692035600501100443d0444c005a560061300500e450741e0400800a11640781d0b079400002e9403401000743d010403400c0c11302d601221000025400a6030040400e03400356410a07001081c05001c4d44500c1d20001a6905600d00400105280c52042680302100349001c80c5001070328215416401c4c1c05852440703842c580021810154940511b00041090744084940380340100b440002c1c04240d01e8200040c041c030000582c4501d0500c1c00d52209c1903050003150780052410950418000b004289a1103801107041c4c440c2107031203468640b1480c0c0e940741d4407030105490b600e240b400701c0b200010060310142c0c0c3c1c030000c001c0a07034074800d050019160311488040204801c40c40c0462502c5a119410103103400ca4000f00402c0c806161202030718801d0303404241844100d200240c041e540103104a2101a100c05516001401401c12000040140030141c28040c401ca80f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 974370575 1250 974369325 974369329
    0x40609020a1b02130f0b0a0621020d0e0d02070810050408040506160204020c0d0207120b06060304030c020307030b07030f0c090501030b0117250e0306060111010e0a0b0a0b 75
    0x4481d480800c00814030600d0301c003090044882d0720242483c0302500100000040ba4148015150b001844d084655110101101079013001c0c82401c0c010302c0c0500c4d0090065454400d1f001400301c200200000442d000184c01c0400f80142c0c102d03440055441e030446103000700d401002074945080340581c0460b4001d821000d00900240d0007800d0059400c41c030003d2916241208108803644065028005120204405c1001d40c0c6c1c1c0740b0107001c10300c010b40003900c04c000e210040281840702c40e4000e4000c0c5001f150404000c11400d5440c9507200b10b054407040d40e40d40322420199540044100300940c140b1032441c001c01048a00c0007414040c0c0b095407001c5c018034a20001e03038015a001100e1080015181e80c10400441d80310707400c041e0103101b040c101b00d640d40901500c081040401210400c1c84a41d00d040845a0720442c000e840003c6d03c400d1804102245407000041d40b503510241000d4100024042e2007007800000707611403602124080204c410894880c5041500400708544481302a85424405041c0b8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 974371825 1250 974370575 974370577
    0x3040318030c09053d17030301060e222009100e0409061109010806010c03020601030312140709060f0e06090d080f030a0b03010b040605030a030f050d02071104060902 73
    0x5290711441e18441e003402e080018008010042136044545280320031790740500803c807070440700e00746500070b1174581c04030804042c4855081079200c4100100d00704907a05000f4008130560703040d6461032916002c0310803920f0025a12541e481c0214050442500760389041031030940c0200b2030100c42c0c1c1508811070140710b004002e01c1c0141d5140d190840389026030420007034401d01031409a20b8004000048a0303103142c0302c0e0001c4441e0203516110b490000200c01c180c56801c100031990101007488c05155400f503a0354020344914040c07000606004003030246500042081e0441440d89014981c890700d58540341700c000307100409902c985804a414020106c020074890002e0148010003d4500c600c0c004040c4140300d0014040b4005039107004040c041741c0300b0311245078001c5010340310011010401d02d03064420036007125450300c4220711581c0b42140800040c1c0b0081039401c00c00c1c0d09400c0140d91201da034034050f146445242540d403243e610024030307401004102c8151100c2d078001a941003001300e450b030040c4000c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 974373075 1250 974371825 974371829
    0x409020a0302041d102408060301020d09260c1504020d060207030221190c050106050a030b01180c0c03030507170c0a172502030d23060a0302010e010c031b0803040318 73
    0x28250b81b442c0083c000d0181e00c81940010018000519080f50751001e6004c48004410440d0310504d802c581183c01980d5403100c00390340d0703110b4204525000360302c0250381e6a200040f040b003100190300c0c40090250356420781e00d49562504560706650f80c0301c1e145002901e40107041450001c4505184503240c0918800041c2d50360f082166004c26404140c4500554022450000031202d964a484c00480d680d201c07156001c1c0114440d5070000c54a50402050a4512030000d02c0c0d48051441c008001c080c2950000c4503268060305410b0005258450110072500c802d419440707040800048000e20101e0768011004001088065507002e4003020040c0c1c05903003101013540c3e800c00304c04a00e1080c4001e03040a5203c0320341464180101d0b4609103500413082c0a84840700843c402e81503a15550020400d031641d4000d9120000301c4029414a0039540040c0005030081c1c81c0e2410080c1700c3c80c04000f003500603e6809103030031400d03080c104c4186842c58141c1a40d88201c2d011800102e06000d03102c0258031001c0740c101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 974374325 1250 974373075 974373119
    0x201141e0f06010e30010b1212250204061502010b030c0901140a080106080307061b09090e010605060309161d060411040b0316030c0903080409020a0302041d10 70
    0x100e60f144101000064940301036100b0007142c000483c903205820600c6904d44c074100750400442d000100c4002c20012490707000d134072451034014500e8039275003512004c02c031545418000c88100541c000c1001100c10405c001d90025006403915101113085201c00c040503807125110750007800640303428018591656841c08a10b43c10040300d0f40107101543c1c5179203c540314404094a0072041c035a603046103a00b0340c3d000342d208000541000412405010f4240500c1d19040d51a400b90000e1880c442402880a00e00d4410000116643c000f04580c0860a402480007080000c001c180c50f401c00c9a040c1da100d88070041d12000104100200242d6a105204c04c6650b40703450b00800c8004c0d41d43c400030300000e040c5440000d00b606004000c04110a1540320145010780341040602e50f01449045000c0c0489000e00500c80a121145800300001040101110180c920388171001da02c560800c5c0d0142c0c0640642e41180d642c0751074500903440244800908148200003940c420040380c0d94444909441c2040f1045000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 974375575 1250 974374325 974374337
    0x23031038040203131b0501021002070b0708060609151b06090a0f051e1e1b06070804050a0e04060c2d0c0c082d0d0c030201141e0f0601 59
    0x2503032890960301441d80100390840c843ea080d2a0750303803101e4030801d04261400351500000780600195a04015030201e05102c820110302d001050b8030307452010140102802d0800c0240307000107400c0e4854905941c1c07042c00c003403c9030703402e100d44024803c100e801036004800500c185469514200c10005002801404008090305241740aa118800a03411841c0c003521580315134510b10f410294a0071084481d01500c4024048103410303002310f0700c852001c0611905240d40140c424a04861840c1c80011f0b0208007107540030769400b8a40350140c400c3c0516400654440b6017820005007140300e16a41c64803c5129010401801c0d918034400e80d00c03180d0030341241030b045400040342d601e80b40b0001301e68141d01c803142c00c06d41200b4a8a907101441458650024021034100314201170210700240d00c80c5030102d05044421003a10051048941c0e14407400c11400204200da609100a00d4001c0d0f1101040b01c07544480807030b040c54002c41070311040c03480140d100030305401039000407500300e5042c40c650b004040580da00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 974376825 1250 974375575 974375681
    0x121308040605180a090c02060f0603061602011103070f020d0c0b01091d010504110a14180c040b0c010c09050618040f1e0504020117010609230310 64
    0x1254160090441d680010112207110f1100769034000142000b08590a4007186090101500170305015000e0b0442051032010000c0c48001e990204041c1d5000214280c2d00c280d030841d00e40228003501484481d0900e001000040c000141c1c0e000b181c0e0204000103408039642180aa03104690104403040c010f4103280050300140102d01c074a810030030340c00d046113081c2c007440c1c00050307a003030300b11842030700c00306d82241204091903264108041901c2c000c0c601508841020351a80c0d001c10104254001b14600508400001500d10240c1200b540c01810844c4c108944540781d10700c05074000c1c140780e041c1d44080794410b0400559032600030b04590360407121040b00c04503d22184103000142071480300740000e40f80c803820000d05140310403c02c0e25000010110101d464102400054001801400c3c40b20240c0c4110005101c2c1a410185610498191400b036032107142011190741c44c08111840b216605018403290400890a1f03030700000004240b01e07038002044c07a412000c0180c45400c1c2e44080c1c2d00c4505200d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 974378075 1250 974376825 974376827
    0x1218061b1736060a11070c0302040f0905160f0e0c071b09020a03020d051b160f0c08030705010c020c0310090f24060b031326030109021213080406 64
    0x2180480d070702894041c26560041003820b6000b10650700b0034036a039501140402c00821081d004118210f810b04800d245400c5840d101c48442d05003900010703005075284e0302c0140c3c103402180d020350009a0014183c1300192244400900031550b244500000d03051241c4020801c1019409540c1c0103200f05002c1c103150415030b50711003c0707400c1584e03d1110303e54940c80e40011508c001d03000a1140f0f404503500182c3e01c4000454004c116400548004903089401c0b088010b044000c03001c84942c1c84034070040c4401d92480b4074103417940c207803c034000625441c60098001600e05000001d00390151044000340440f0071100310403607a400031481125410b5010283d0401c1e502c600d5480754107414040e6412003541002a1590312400c1e59661307001d40884c021440c02c80b121310162041c00040c01d40700070070070302d142424450600c4905035584050180410303035581080c034043c44803a1207034018805440c980c60390303910001c001c0203401170b203174548280b03500d03000244195460003c806940382c0d020740403509003818000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 974379325 1250 974378075 974378101
    0x203090a1401021f27030206040b0921210402130c030b0a08030702010f0306060c06180b040803060114030103050304030b09030d2a05191218061b17 65
    0xd20301d815405860394030a58242c2240007440c051010b440c001c201004001400c0c01c0100032171080020a4110107140c0300080c2d40401c54507003007a002001b0b102252200c1c0344090400106400d400e1010280141815a1304103280260001250510f00ca02102c40559013810060703004940c001d501543c0100d4100c0d94108552209003107824a1800240f25048900440d43e50581c0350004102d9a10101e020740c01c66030702824804031034009141c01d002040c078000016003540804400288515200c200d00e206004404070021011504101766220504250409042940c030507109180052124040005108840c1d000c50341200c0c0c0c001e0045251901d1a200e400700c000c000380c8408042d000c2041041e10042d014003c0310401c0321090100c1c00d41c60280117401e051071100003e02000d1120a21110b03804a02e040882c6c468041c81e03051540100c1d0111928000030441d40007100148a0001d4100c4288181ea511111000c400034035021040100380c03000361480800b40e520090002c02000008201c10340b019 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 974380575 1250 974379325 974379359
    0x4030c060c110708210f0315040f020a09031e02060d0c020a080d0501230f0f010203090d0f140c0907030b030a020d051b01030b0f04050606040305060c0a030c0203090a 73
    0x220b020518410084006403c0020950054407140d2107152240c40040c828540501c109004c003155900d0440070a0040c032840c00014a4008504890a0418a20340710f6810126003400b032800219507642075080d003c1d1501070b10f4041694403580e40801414400748142172030809036002800740b07007411700d0f4081490240c0384420482c0e0441c01403881290020300070f60080c10302901a0174003c9015818160380c2c1004c900d0882d000c84920040c00d0b0382041944490b00301e070030750800588201900c03050880040c0d2541c03003180c9015412011505124081c8012940360030052441900c05100303596811114980d58410002c10070740c407561140c081a0380e2802940075200d1201c010b42501c030a007200b9000500160b10101060300e9130b403c5040d0306429040c1001507210303486001d080c108400000c2d200400c080c1c100d11400305000e280c0d1540810442c0d600c440079100150b0344101110020716040c11146000d03001441158040b038104040046500c1c008029070b400f070800035060741300030352800da41c1c4440b4800780 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 974381825 1250 974380575 974380577
    0x31e04080703050303090f0c09060103050405011e060302030c0415051002070905040b07021507050f160c0605130b0309061b16030323090312040c080a0b0709090504030c060c 76
    0x10800014051000d001500c01103000304043c5449203071204000d41006500508000c1503004a1050780301980c821b954540c00990038640041e03c3c1d940c0d03150541c010401c000c0e440b200c02c414803081e03210003070310b0760085070580303200380c0a403030001d01614140300540d614070105800444186400b44000e06010801064000d03003481202c00c01641d9071340d42001c82d001520165210700701441044525a010414400f49901c00003459105d031510010040440c02440c1e11b488803260006503840000800c66200c6c210f05030040100c21805583e81405805070f407201108540300400500001880401401501d00c1103140074041c120b5a90f482c1038003407800c02d01c40c02c0c041603070f40148009404c0c0c0a4008010042a220362400115400030049000801080d41c911441c2c095050303040054852020040c1c1d044503110b044049260b44641c0b5002000c0074803500001c03624800c08034200300340072080c01064050405503c400130200c2d1102c0e80c0c2415034a0071034000d0082543d90aa110000b680755005903040529 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 974383075 1250 974381825 974381827
    0x22e02010b060706320414061b0a110708160828171201080709020a09140a1715160c11190e190207051207050307080d020705010b010908031e 62
    0x20098245c00b0030901c10865840c203442c10401c00041000c8a0701c1120840f440c00000e04103807400c00d040014108903490080a240b90201d141401c20b809540e1241003803d0704010380c1c84c1300b40c42c1c52400e81d4902200901000020000d203000404080125900403074000c401240d201c0c2c4204c00c1000c013000000d80302e003142c1a4031107807820041c60400e040642000020f00317441141c25450145100e107041300e540c1124205900c1004090104c540066aa03070854001c10b084010441000d07001502c0010903a22840c0f907550082c002400c851004901ca843c0043c040415440c19180c044208244682d0784052101140d21403248901140380e81e40c0849118000502458074001264915200702c1e00b154009250366101009003e242040885011070024a60f4411402e19210742c94060b40c1b03040c03041d10000d5149001840409001062003103da400750411801c1d50b9a044400c811070027540184002e4a042d468100c0c1203045611030403015044900810045042c0403000340d06000c4100260011211440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 974384325 1250 974383075 974383121
    0x1208160522060c0506010e06012019050d0912080d0228110105010e040b010312141908131101121e1e020405030a030c0f022e02010b060706 61
    0x3095000755000b0b044503a50f0391142e0f02e807a1401c10b1500c501030b0403011107200340000704106642d005040f200b21a18151181c00c6000364801c074541041c40c0ca0708003288107101c42e10600140000012800c1c1d01003203076a213214609950b982c540c0d01310008440010710680c010016402c050300c880d005404004d072030741404a000342281c4090503645040303140c914080f4034251000000b02c4020f12803140103050700d48101016207010754a242c1501c0c8140402019007502500f0140040d02c1103042100090171070040998401181c1004110524521106400500e03800e0001d4101d5440700c000031001984214011300030317854800190303039402d030031000c070703e10140e0b64600181d09100d001030040203c0c030240c80000f00300700d00c810a5101c8203101c5490058642c0104010051500c2c00a40100495050318009039540203d16000703d02e4290b180c40650b2008606846940f443c10000402c0c249240003030036032109912a600c1a42a01c00348a84258000028041c0c00c0114036543c00118410307003030f2483d00c03800302 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 974385575 1250 974384325 974384377
    0xd03020c1524010c0812090a06090b0103140c091501020309270c130311130c080f0907061b020d050322090b0913020f060406030912081605 61
    0x2034000c032800c000045404044101c828801009002d41c420286800b0070000140d8940c1e4282d8030541101c942d10102200c00501024424048038080380d60054042c000344c42c55003080410340a00380403c2e0b4034010001c06903500706600180c130300fa5200c000307000100155034030400124a00202c040490660100b0003224250340e4036030308a0147c4009140804502d90320322802040c00c01d90007000020504e8003080716045c05042204e049040341e9000c855041c4421201000c01c168072141c04100301800c0c208482104030b650440e02c440c1c842c50018407450010f40e203070070445640d40300358803444002c11500e003440240180c0c04c4203070b01882c03070018000c0c40f0081d000d17a5401d0b01d5079105c51100c41c0c400320b0380c1614032140100030300341c10000c2c150240280b240000c0140020718014001c0c10f0b020301c1004840441045440d0541040a100c000030300c166110390b650000940945000401102c0340c921400012900500a2090074021614089800720802c40d940c1c09540d0b0354000c48070102c403c441b10b015001d041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 974386825 1250 974385575 974385613
    0x305012303031c05180d0212090109120f03030b061e0f0c0a0b040b070903030f030b0d050601121e030c03140412080c0607080912070201090806041416080d03020c 71
    0x83d00b41010001050700d0180c0490075010303c0004444501c2e0840c1c010142c071a54000750700040380007104105582c8001e42c0d4010703603440c242544030b81001503440710305006110b880d4681c072a03281e009407014072180750b00104100052090a2904078900821401e8209942c001006850441d094070385d95131809002100c264a03100d100002110114621ba0410082000e510415038004040c0e04240300900d00f175640281050b40050191420907941d1180001c182e175405154409494010040d20504d5031a0042071b00641454101520300080344404824032042030140710f0000d0390140e42c0c1d60303040300306590101c8601d280585080300000d0144408900028400e04805004d80300e40300d40d0b503844031607c0a8a04002c001000d400038458050200b000b880c50102d150784448103400c4c00582c1d60700d810310060b0703100c0460b600b100c4081c0c800c20081008206451101d54510740000e400c9801444c0440c1e82250030604d2405020030503006a020650710a00a0700900001c607c5042552020a440c685000316 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 974388075 1250 974386825 974386867
    0xa1e060906140601090914070807021908090f06040e070503100b0d020a170f010317070605011203230702090a0207140d030501060306080a0b09031c090b0601030501230303 75
    0x400c0b2814050000540c0c1048104004191011091064202483c00c0502c8a00300402003004d1042c82c4000901c05482403114124070680c00070649540c014a042c40c0e056608001441806442102c006600c0392504000f40c50407604801d075030f00e64694810760222891740016100d881c0f038400900b8045840c0520b039002d01b48208180900581300c0384000300081105000b0302c1044812820042402001c005022010781540d410649244070302c0d40c212030b040001d05c02c04070080d24061a040012500815881420071150f010303071741d02c40c920811050004000d610444074110310800c100200001803d201941c0c2d40d02400b00c50b070050030900e050f01c072100d140e50008020310300358000081b030245035a014440c4501604551600b080410300348400310380e558810520152040d01c00b2000203400d02c400b001101ca110000e80c02102500078004d4848010303100d030710402c5840f6040701c000a101941705c2c0c42158100c03042010102c25101040c40c0c54140c50061609003034041c08204003a07a1241041400a24 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 974389325 1250 974388075 974388101
    0xb0d0b120d080a1d0a022b050c0a17060a0f1119120b0a030b06060d0c081902092107092c0a050307020907170a0212090a1e060906 57
    0x103050b00d4003003a81000ca81102d84c2d503d00c82824410091210000003400480300c9034140e40755603c0b021511034080e07014115030030840e880010050b1083c10001c3c007103001d1040705e40583d04590b0b91a11a00700e101c0200c003007800040280e1100e8001036200c03407160000c000b41c44419200190744412540c444010b640071a010040b03010301c5480380d44005520101c440d5080001600411501303986800144c20261140700c041d1180441c42d0116842c0d0303441004854032100e03103107020003d07109110005060050201c401d81d00b0310042c401102c0c6203104da0b00882c0c00e000b20003801307808108107034400f0500142402030542d4040c401c4010100d140301c0288200300000c010728060307080c021701412096040042e03000002105411040000000130320000a40c2e803281c1d4111613118407130b659804111029080460f40d0302c4107210f004140100760809030300400c0184601b40f507aa01a5544078841030b520ba0344040014020010019943e4441d43d07401c0382140c00c3d0b4454076010844110f40e44411090341d4101040390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 974390575 1250 974389325 974389337
    0x50a05160f090e0a060e07020d050307120e070806060306070305040c06270f1e050604050d050f060123010804031202030901022b150605030105040c030e0a030f08100b0d0b120d 77
    0x102c141b034a028001d80c0d21840342c1c40100704444040780c00070541d0001030180320074840034080c90f030f081001e01e4200350312610f48107084580b05990342c4101075540900340d030014024042c0c880481c202a100340500c5200d04d070420010704180785401400ca074800b01007441c00045141b00d030010310941d051086480010605403008400f02810070101c2e010114000b005801c005074100d00801840e101c24098404413070302220117100344401030810030306100701c00301042071a0240c0400440c1000c022481103150044109840d4401a81d0f0001901d0031001910040d02198200718120114040354005641c00605040058103250150740240c3c900404911800540040c05e000702d000c40c00540709140d09491081440e03124949094130140c550300c810f0181c40c6c0280c0c4c13100090301c1824003e400440d40800e04904171040c922813418000e151002031444c2000180c0c0b05030100382060100001c03c001e071240140c21910300b014665046008290500c0c065802c46c0c2124180101841c060010b9503808400e0303190b003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 974391825 1250 974390575 974390579
    0x123506012a020f19090f090b07020106060e06040315110408011d010c1e1d090415050a02090303091c1a0403080c030112060f091e030201050a05160f090e0a06 69
    0x2540030f14648110740600f8204070102c2c4c045250240d0282100c0401a0000c0c2d50126258105d0191424040c042c0c007461040090000f41681507005200b150016694000c644084d6030401200e4401c0d0300c0045c010107441150540c0130340095008090100c0005441460039540714849800c1d0f030306e180e000810440b40170030140850b02085c052003030500564600070301045480c5042d2160304a0315a0084100a15005600100305860024050390300340206000c060f450140381c0000500e810f91400b03690300741003d01290640d1124000d440b19042c0c0100075500702102203041c01240032907202111503a14001211001081078400c142e04a00800060303200b107440c060030040e1280d2409020410709110400041245102c54900305001c035038005d201080351441a0020400b404601d0006402c105400700d2010000040c0b2980104ac18800e8000b4452640c40700500400c07105c4c102e501003a004c0c00d612041d810140708164040e00e440c4135084c000740f00f5485a08030001104211200700782c240d40e030081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 974393075 1250 974391825 974391829
    0x411190b0a0e0916050f0408120d1d07090b190b03071805030a080f1207020705030f1605060306010c0f03030605150a0c12020c0409123506012a02 64
    0x7a40c1482c080d11400500d05010b00243d051409030444201040008585038400003800c100311401460410115401440d80c2848080c80d6884000326841c2a031a03c0f4100720852209049240200c2e5007801405115103450902c002422291a05980c002c035803c1140324500406c04005000e040d4180110707440b440c000c10b02401d03030344072603100e503c10b0400c0400030001a5400585140d604de8000251034071440d05019204440c0600e66107028819180010009060b50000b1801c0840c2e0044080b1442c3c95001c03241d05031034110340e0026a1030441e03112801c0c80141000c400071900108107250861110119448044942d001c0142c1200003135140d0301300300a1490700c0c29040c82c603d500215214a408107805020f0170210981a000302080781c040000040e490080c0300d1038108050242c001c0c00300d13024500d0110510a03510048002047d44034111120b443c1d00c505007000c84114a42c40d082c80c9405048804942e16002415075040014445140088103504010103c101100c642590035003d00d03441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 974394325 1250 974393075 974393087
    0x603030d1a151305060a0306030605041a0a0e1903051207230a050d2f0c0f120f0705190b040b0115090302040e03070b0c030a050c09090411190b0a 64
    0x3120749102003050104100100002c0880c4084460840d680c135906d2241c0c141c1500a008140d0000c0d14003440c1c5800c01c001d202d0004031000d1b00342495201035200d80e070359104c0e41044a0500024140f81c0d4000c0c15000103580c1b00c1130002c142180203061450074540c0441c01030003088000c903415800111011006005103401200c07080300b049034554038609001815800410500803111118600c1d520364545c003072041701c809414020f0b075031201240d100000d603640740b11089038480b003859180351160308101034890030041500d10344e20000700c0d009c51400c0711195035085e85d0b402c112001e071342c00d0240c0c00040c08036081000c40c056450f48185004d000f01d24260618000413401648110ba8500200c40038140d400d500c4400a02030313a604440001e540c05100100350318500030000700501c80a01c0209202c900d036a850091072203a030300790b603040c0200e61703800c0700301ca1190240b1403020b50000b00c90800b14001990800401040c1c4002421418600c3c1c000040c032802c0b001c40703074400c2c504002e000900d10b06c06c80c0e002c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 974395575 1250 974394325 974394349
    0x1081620012c010209091512010c05071e03050313031202031006110a020a1205010207020d0b010e010b16060b0d15050a0b040509060723041e0501260603030d1a 70
    0x90000c505040110000c10401c80004160307c8180b0100901b2000c030f07680340c403a07903019a1045c5000700100040d01d40d0240c034075440400103481c18540c415404880440e034010141280c0c4c0e142da9480d0540c2c99910a03552000c0b40c1c224200d05005003100c0c5400030805c0e52018602c54890411080f68042c40e1013030103000380c0c00c4001b591182d50070442c00f0b503000d41c584140c5002110f5006000695603881c904056009000d4100001e5101c0a03000704001805440403003107040ea15024074001d0580d9030b401c1c1061061241250104400c0520302c01c0c003011402541c02290b600c20040d2514250728100d0752140240c819040448030a640d60b80140240c0c10290f11035080a0740041c1c6082145081c040c0c0300c6030755010002e00a900300480c6444000c10707103900f06800c6a0444122003c00d4447d0b40f68898440309208507001005010304140002900350720402000c000d4808a000300c0070790f049040d900c0000c000000301169058401000040310107030b0303244194090303040d8034100007503c814410100801c5d401d4103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 974396825 1250 974395575 974395661
    0xc0105130b010803030f0411011116050f060a08060f0f032406010c0f0204020304020d080304080306011e0507061116050105060907020106030b0c0702040f050903180108162001 77
    0x51041002c8031b1300f01590785070031070b03088680164005680401203c2c420081ca02030101802000b401400d03120212030020700ba12003c035410329210300458240038903401000d190200140010000c11514100382448500200014002e00304d40940e182c0424508980424a011880c00d000308045012801c1910103030000348c2480c106c030b401402501c80c03619060b0941d2010307203d60741c000049003c55541d05e6208090702e50000302c094481c1340604006005407c221480c501140140d440c4000703c5680410001d1484220307200c3c1410320040b5201c0c41c0003401c1e284241041201c041140b03149620f080b03040303030001500c218004100c40ca000401d10040d0400504000107581c10580c0c140001146002060740c40a9511802500c03402c0d5400010054030956203104016842c1400784200050040020098048600f41c02c440c8140034200444403d1030440388040c0c0400003080c4100311920403074039107102034900c00000c0368510300d8040e07807402c40c1c00042e042c4001001d07542d00403142d2030800008803840020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 974398075 1250 974396825 974396827
    0x6090c040b01020d110106080a050d02010b090112060e01090b0a06080c060301062c18060117060616030c200102070e0405030904091b0b0a1b0c060c05030c0105130b010803 75
    0x2400700041d5448060402c80b40134060a0700740448800d40c01d5100390001e001e18403c80d0254051820a5030b01c2d05482e0b0032a0740154203000e5000f00728144060014101d640750542c1c0c20300031f81192201001019904080e605070754854143e030021039040d00400d0300483c0045000039103280760603800b500d003201a260341809407505000410000b0740040c0801d0390203a11034403600c800189603980410005043c85030341d07807000c6440c1a09044421028500344298001c2c1c99000d07401d5400030b1072142003e821685075621010401615003840c41c019541c40e2a9842070800143c100356a60341d00c0c041560184c080084241c0401000d542583e040000e44024003a031005585282060b454040c3c90b03110302000c00303000340c0c2c840e490341080201d174803400030314985100507181d690f03901d510360301e10b0903444000010000303401c048281800000440402452650001e42c07048074924158081c2c807010103a0b8401c1d12603000030b008010745160207009841c8a8240160b401741d90340c420340743c82800c0d8541a0408419640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 974399325 1250 974398075 974398091
    0x20c0106330212070302060117010b0d080a0201060b04030503070b01050909030304020405070509060307030b04060531020f0c0705030610381201090b01020102090d060e071706090c04 80
    0x45080c00d69080590000a0300072107000c0c1030002da142c0340e8005800104244000b036000b00349039010800740d05070344a504010f4014610007020f54282c51115400946c000d01194805000440002c020041541140004140300340c0c0da00080030682c005a0090f0703182c3d040007810b03104000c075210782c0502601080358144641c6c1001d06295540e8000200003d0040d5030304d030041808940544259504c030003004041c1a52490a424010b025000f00c00046010f241041d01c082024900f014000111401840b8149600c0301502c0d1903a1400000070b2412101c164208230210040c0004030042048202e8030340103000c594071b0a000c2c113140440c0100801d003040041401441581d111b8025038810b00b00c000319041004048603000920b00c1010302d1841154100003400b441c1c001d403922082c50480b012550100b09407da80d20040e0b084c0d00c1402d254581c410411030920001944650010340c040003242d0031540c030140c4484001240c03c1a440810f0f85503402013003006071414040107142203420041c3d8061007555 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 974400575 1250 974399325 974399369
    0x510110c06070b040f030e100f0305010522050a09020a030b04050d0801030803010e0403020c030f010902090a0207030905401b0f050f1e030103020118060801032a0306020c0106 77
    0x2504c003d1030010001c1008051501c1203401d00d090f5480100300051001d4030740d4000d409034190701c1c0c6e8080440d0904000103491b01d07042e044004a43c1b41c8801c0320301e401c25400707540030090400420010210b5914030205025840711340c0c5040286120704540c003114105030401c80d241484031440e000c108441b102c0188001600c00b010faa0445440c010145050740b182c0c81d0a03804d154580305241c0d0035209042a01e031281034150040004180252241245502c1d01c1c00e20070185d02c1010b001501040300a402000281000c461080004030280c000e2808106410410080000e01e0941d00c8140c40d07402c46000750901d00d51161208951030030001040910300d140002e4240c039000e215103000c0c42004035040d540e07508000c089480320007107044000c41c6403c07400341c10040d5070003c1c081a800105641c1d400c0051425900f011016200d55481d008120703840c550341e0350440707504108450041441c82a01c686081045503060000e1407013008003603181d08000300c119007190402c2e4080c4000b4a540c1880403544 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 974401825 1250 974400575 974400593
    0x507140711060901030b040e03180108090303011203120f060608010b0702030d18120c0314070602120703031b0f02190b0c090607081b1506060a080702070510110c0607 73
    0xc403105640b81525010941c005a00501da060b44850b00705040106e9011401f9012000740354444a84041c410040c00b504011101d40108607030ba456181c2c01040140042e01c440c4403c0e03002c0d00d01c83d02e040c202550b010300240c070940c0c1904004000382511010103100c803a4120f450203014143d42c140003401c1509940001c6d0340c2d10400203400d0280842c002c40c045411a404803c000649544800c0c2201030100d0702c2c0411b020345840c4016640301c0002949842d40840104100040360f2030369009009100d00160500351b60b621500f030450602d41d488550100c95a0680d0540080d5074103034855542a81042002134140091040040540d07030f040501200082c240d485100d401c108404001030711401c605010a18a10a401c03010f0442d4002069400b520050104142e4030701030036200782c440c1442503030f469801e010303029140a5072080c010b010ba40f06061058201d16400040d034811a402e1560301c1c07000c559107252086440c0002941e50624041c00402041907502000040d1034991030840f803502c50b1034003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 974403075 1250 974401825 974401853
    0x615221424090a12150209030703060209180a0e0d080106020d05090a12050619180f110a06050921030a110a020a23010809060a240905071407 62
    0x6808005074030a18241a0300e094a10110024001c10303441da490320b0300080304130b90a07401215070320010b080030001c480a90080d034030600c030302500800c0c01e0342c2190b0b01c2401a4104a2800303401507003405400c00041c100940d9035014600000d000180f0b10b4800000500b000212070888050021160041140650009c2c4184901c410f92400a8680320b403080041d07a4103500340c0c405031605240607403110900030082640d5000b410500c0080344104a102580f005a1310004620412071001e1100d840218a0301c02040c0c4d400340c0301e0004030700f0341001d5000040c5013a1898100174005000032461001d582455000d44a41c80c0315a00b142e5050740049440365540d00c1031908800422210b8011222110f504101d61440d0070341c004c000800183d10740c6449003081e10103444130200c59509204c0f0240950003801440e0140380110041c100640d200e000ea6809851805034643e1401c00d00740301003040001160007400034009070400803c4a0406030340c010600c003004a100701c4555403c100b4400001c0c5c1c038442e4414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 974404325 1250 974403075 974403109
    0x2010c050a20010501030303050f010f080a23010501030804050312090f12100608101b08010611070e0405060402030c03060702060a050a1d0c040c03020403080403060506152214 77
    0xc014208580308040c02d84464030740e07502541c01c120000c002c058241d0081ca104070005407074494180e81c2c03810700703000e5000507110300b481e80d0300310603012400304501e006c0c008902003031040e2182c40000035441c098215030003684160f504000c089070030b005524041c07000da010342852440e02c43c10121030000107485441c241d94080d20030705000e081c5800814041c0045100b5000d002c204100c81a6a12142500c1c0c94421021600c17840c42d1014220140c501c0c042c80e45e4400100b60b80e5682c0d280c1c02c0c03100c180c452649003001e45031144503012001608003500500b030f51007941b02d00c010b00f1082c20a0301c141442c3c1446c000e081c074030030f030007480070465169400078121b5409010980b000c02c030758071450070f0301c0700902140b498140d11145400346c0021520f4002030350449404103a404009130b406221085040340a82e020040040c20300b008104042003680d00000c2d00900024200f801c000181c44184509138041d49101e50f2011079000e0b0401241b0020401c4030003042118259210303e40c020300051202c010a4000322 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 974405575 1250 974404325 974404337
    0x30306060306220917120a0c02031e071e020310090c03061109090a05010530190c050102030f03070c0f02061b0f030a0509011110020f030103110102010c050a 69
    0x680d031aa99602c1901443c00d100c0d000110784200300342007201810212900f900c0003001c00a81c40075031041c1508480c1c11010406640000e51903520700800500500960001148014450484000784c0e1149200c540c0c01400812603031070045140c1a00845502a4109504000d462406002d80c4000c61815000c01c0b41070b0001481207013030b1030505120303c0c940c0c00180940f0710b0700000610506400b0b0041c808100c08840c4034010f541c034546607d007a0b800034050755820052580000540d03c0200d010b04e07441c0c03000c0903541801c00c004101d50741d2814141d403407128040300c1016000340a1014041e103010107404203201442c0380c800c05803200c00c107502c80a03001c201003186000c0e045081c0304d29640c040da00c00d54003c01d416502c1100902100c201060f9009600c954000d4001000202c400002141d024000c19210181801d00440040d5585e4004100401582c05188070151607402c0c680700030404662140c0c12641c0b13950450178141280c5280c039650350305580c0b5102c500990309410400f5500e004415207032507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 974406825 1250 974405575 974405581
    0x270303040f06141903090b1305190c0320210304060804060e011a1206101502070b03011d07030c090323060412030e06250e061209070906080303060603 66
    0x34448074803c913460308200c08020300400c00d400f0384c160080c03c00340f8026519507445031200b901d90042e0700d000c500b00a016600001e00000120414000d94607803c0c05400d107951a1562929404c510800a000c0030225820420070560a4a410341d6032490403281c0d0b02c0c4208040c500c440b8810340d20300c142e004030b1061212100c002010420550090b0b0b15000f68003009000f000220120a000c1845221041d031088187c80c00103902000005646445034100740242d441880ca0101d0b841c008003204042e40f400c60040d103201286807100040158001d0030b80c42002c5c0800745901d0129070901c24090107071002c050030a54074014540c0d0120b4460f06481c0c01c40c441a61030b206018914400174440d004520503405044208410300101c05000c040030649910140025036110702015192142112222440d440ca821031507100c8810101b981c2d10110141401ca0b0205069000a900390700200c5071281943c2c0e800f004c21418510070f01101001303150a000520080d8100600517440780001000036011380808400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 974408075 1250 974406825 974406857
    0xf0f0503151807080c0901140306010e0a03050a12051812010b1003060e0606190305040204060b27100228060908030a050c030c0412050c06270303040f06 67
    0x41e12000000c01040308211403105030100440500803121180450101c2d800261410204030454150100580d10305e4420805204011500d8001415060402c28044100b01c669115510344c403003d180154028219102245401c00d40107510345048001c006080c40550310034450260740c01008081140c520014450030860940103228071000036038040b09020a200300d883d09544100103496240340950484d40c0c07049e0a004980c03181010f28100b030040e2000241b40b451007940000e4002c1d20007400410b44658a00f400d04c0c1c1500102e100318100048082e1120944200130307514042c82d1000d40d07010342c0340241681c002e500c4918010116040c0241c0460322740825522070601d012041d071040d410031446100b400c0080d6584c03c04c5490070349103403604000c549100703826400d80e44103411100407545440d040c2101c002c08980d400004841c0d1380b00d6511480d030269903002c041c262584a031041030207441c00c1401098020241c81a549000703400c100404d000042081011400f42c4003107080c0204c405101c680 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 974409325 1250 974408075 974408101
    0x30605210a0503030c0405030f0a0f021207090f0b18010806060d06060e1006090b04030c170f10050717040f1212110a14120a050a0908130e070f0f0503 66
    0x40000d02d540400410010050194009032041d01c100b5400c840414051025040e41c54140c2c140180040f4035001007100149040550926007102d00070aa40d8007940e261041130a5a12075107402401c1600e07071640d13050754145903140540c00e0408180381d502551601040b9a00c030500500054015502c5841c24000d00601c0e0b040760000384149000f150551034425907104102a043c001c00d0b0004026940003d480b1b0401d40a5400343da800071041c034012490480003007004500340840c41010300603040c041c0300e20513050050840082d03400c0000b18843c5840348004104c4007041c1e8425458001c120240000304450350b42c2c862a00d60b0242800380f41030700181080d40c0c0301c1868000c0354909030900340b2900c4a500f01c0005040061155203071413030ba10128170300e4034041c1e000d082c1140c1000700b000300000c0c038a00666084150041510200019000f40741c2d1204001c41d48004c45040340c04c0c1d205042001072502c00c0d0407042d030019451070305140704401684014000640b010708802007010210100700342480c520 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 974410575 1250 974409325 974409343
    0x2102101409120c030105090d08162a0506072105090f03041706060904030c06050408041e0f0806070503070e0f0a080d031109010527090f01090b0103060521 68
    0x10031107010021007000b800e40d20710450842c07034000c1d400d04d80400c0c2c00e140000360711102d00c3c00c21781305c00016030389521011000005c45041c1c01c040000c500040251000018003891040044440b0443d6103409410024944000a04050f041050014102519005421105c0504051410302062544804049502d0009036110f0b49405000c0041d000590700d900261591652000340142d074015501c1c14100305240c50300311006030118240c0042040010880d030310035075120344501c8945040540307030300f060642c6143d8440c18240c92804010705022140f20030350f010008202003802441240b070949001000d600014200d40b09110661440607100d564030b4414180c04200540070a8809569909540d661071541e000a0b010030310b00144400806540c030704540c80e0b5541a100c0c0d0789804c84080001208070320700036030840c5100700410754084580d180d4160070b0144040c0c0c001d801c07603541001010012954051000c0d070500d860040c2c02c200c940c84500740488034801c01c50107080e00c6181540340d141806904 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 974411825 1250 974410575 974410579
    0xf0902090a050a152601171902060304060236030f030a0507081e190f0206010609180e0d08060a0905040f0b0c090d0b07091a03010b090315010b042102101409 69
    0x120700215161004001c400030307440d221811614411504502212234000365403003c1c2d0003210410004004c200d09070010030003811001c583e410707410b0f0028040d40d5440c1090341114a002a560060f00991500300000702d0503400c90340145103002c1c000800035040c2e00c40d800008240ccc0001148090740f04409100410280700507000540d40c802024011030640001024528045039800060b44030707143c80003510394141c03030060301c0304291107041c50700700707151000d00a60801b21681c80e140850650350080c05140c11401c01a1079080c800d043c07007000c100c0b40a040c3d8221449941c0341c10f003088042282179604240c1c264001420301c00f681c444201d4055144508068030750416502d064180c204001801800d2082665a0b2681c0020b0b885045000c46103338440c0c0c000700c04a6050006000310000d220051400d910000e0407140c40c118409040040b80c28241d010080380d140c0881c003003245100084203115080c198142c1c89040d0505a800142e5644401c14160704104480c013003002c00780489000c0322451440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 974413075 1250 974411825 974411897
    0x90519270809131a0111121306020f031617040e041b05150409110424030c1106041b0504111b0102071a0603070f0902090a050a15 57
    0x145003040400e0380c0c0301e020994001c090800c20b030f114150007442945075030541ca101042c070360035003400115010404190020202d001d040781c61088443c4134002050150400890038100910301000030313040c40140e910002c0e4a4104200120b181c104c011802d01c6843d522080342d50242903a01001805070240341c20022038a6242001d00090065004210681000381d81c03007092041d403100280b01d40b25000c000d000001903000e02c418000c00403140c0000b076649800b901c1c9641010350350111101c1d040070480004c1c00d48440700f0142000e880d81401106043c1500b41414483c90710318a0280e80d03075810080c4041e01000b03141c00e44500b40e8041e40295402440020418007084a038025000c1d070759440014015802000f45103401c015480600a58002e543c0210300010744003e0140e29000c801d1000b01020340c5800340700b502203617200103400c1403405041a0340300141c03100090414428007924680205104803904802045040d20030100402c00422610b418102e0030800084011108070013501c070301c03241076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 974414325 1250 974413075 974413151
    0x803150a060c06270602030c0910120c0f0c06021c0e011401050a0b09060a02010212070918140606160203030a03020325020303131e0809010207090519 66
    0x703440076140c50301c180910001c001342444841480070a044501620550100030075443e00401c0090307002d164080b40d04075029241800300000142450341c5a4110000326055607041c2a02c48038034460304428496034203056080441c8000058011601504000c10f0281c0008640c07401c0075200001ca2000740a511090001e1082148680e01800f0040c104c00c44605091000003141e01d02810a5012503c5c1040c0d2036140c40404010b204c4181d005484c090259034081000780c1c0e2070314100452600c264855600d4420380b90810030541080700a240001c18103d05000d0489240d403000c2501d540c00c40f0b8111105540e640b10351003c40c502c0d24076042e01179414040032520946c0150590019031090700d07000c1d0003000361304101400e84c040071007201c82400160b000340000317003103450f40381c100403500341c01602c1c800d56400c4e04604004007041041d20881c2e28120201d00d4401950301008500d01a00207480c0c144941e24191101340c040c2914000c107440220344800300e8080409a000392104054655071140038121 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 974415575 1250 974414325 974414327
    0xf0906041506020d0f05030c04030b13140a120314061212191b0309030204200705100e03041a070303090c090b0f0f010c0222180203010b0102070608040803150a06 71
    0x1100761079560210704404d41c2000c17081d1252007140d01c122500c0010740d090070305584031494444401040902ca203907810f003401010482040643c2c603058140f1300189040452443d00c006000780c69807001e4141410a121081034801040c5d41d150b01110541d00091072045003c84c10b8a00700040200514518000070004903601c010914100040107a0b1194450440100c0300000103c00c0c41c07074007400164510b002400103180580220300d000c3d4404101000c101c4a082d602c3c0e42590126608a907194880b5030382c941d42101030f005820f14040380400bc0c50615103041440000c18511510f986a11b2600085090415001b94440a200c1d038001c0c2c483c81c0c4041d115202c403001001c10380e06261003408040e1220300c1515108803121703a48041a07651150032035580d400e12030040c44241c022140303841d5001e000452040c9911880e01d1420b810390511404030554010b0608445501d450300e030454104290502c040d0750801c1a1310703085079000700d03110307501e03078800c55141144000c08070620b40c1b20000300c0d4001501c0f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 974416825 1250 974415575 974415583
    0x2030c150705010b0f03070b090105090a0902071a1005150d05041a060916030b0a0b03090c09130203060403140702150424022d0a06200304020f090604150602 69
    0x7803042c80208110301c1c00000700012074800c0b07420980d0540c0180c1050101e00140c102a207080041030521a044c01c510300e0010f6144078258001e002480e9000c02e4110500814450242080d84188105407250804030b03642103104d140360059600580360424090602d4007004201d400c082c8104000f0401c41c10145020781175154107201c0d00c1c10351640d08000c42c92a1811711300050203030344c150f095541e00203035000c020741c06000800700c581d51020000d040014003c03003143c010f5220b0b0380d6540203000349408803401c004544001800840445510403145001a140080e102d1340164250a002000342c907801c0c1c80e100640f2071840000c1d0486958540b410034419400f02070302c207545d01200810302d0000340300c8012200e141c010304032100592000f1380c031985d004008110f10384c00c8603800d0458808a61951f44203450b004840408591044d41d82003141100407010964200c80004422410300e51304241c2c00048610010710b0b1141e03c94005540410142e07502d86d03000c0716000b0b211b0f00040015594405d03001c0d40fa = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 974418075 1250 974416825 974416837
    0x210207030c080114090d09050d030c05010c03020a14040806130807351e1308060f071e0909051003060c020c0f0a05060301032a03051c0503060d0f02030c15 68
    0x415481300115001c01c0c00800c04901030819a40c8021029103032404006558809820076414041040b10390404100203001e036650004007031314056500e004414008140403821020a01486011300042c01281c4c0d000c540c0c1608800e50404080038040716041c215018420440000e02000c1207146180c8242a03035490b040211274580a2409403880c0b12401100f207110728801c11090107030408084080c2c07074150026240b00c000c000c401c4940c154407200f26601d442c00c1518480e494032100e504220545601079203c940c00c04400120550001c0c890034058101915070092841a5480d03030000791816010051700d000558000c001070100302c0700480082d441e94a050300c000c0c055400313280039000600300218018101c1d03801400c07041c075503880d54031040e41c0c0a19020701003501c00c40000c0340c01c031501c0301c242c1c1890103140680d002d0b242c10041440110140110009e4403800d012003030041015581c0e503003403102030641d0011401c070611001d034400241401032841d48254070100304800f2142d48a0401c002d412 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 974419325 1250 974418075 974418101
    0x31b01061e1a0f030a051b070c0302121f02031e010311240a0518040c0f02011427210705060906091c020a0c060c0519210207030c0801 59
    0x107038040120703403001e005201d1018076041d0020b040000c541d02d203046070310566204407c04000369400143c02813a04040c1d106010944215040348000e10031f5141501c480c96042c1c125000a20310343c001c10380404098411580c821980036404800204000b8034540c0b41d1885003000a0304680a40c0c41e454403540040c00840b04034015015044070000255400d209190006000384003103081540c0c03200d0803907440c1d1000160140d8481c0c030a00d0314885440d903003d01c003c014442e4507041200c1b9400754000b03003154100140c0504800800c0c0c1441010f0140740101482018144011000e0941c202c5d030070fa01d00f0300024010124a03c80100140260410502608040d8461010748071a6114513a4540d900e460994100c2020742058004c1c003003012045802105100c0d443c0145d400b624074a48070800b4080e0558826001724907104042030400200b80312020313881c1415908081d811090381c4034203080503541c60300c406042c0780122960100303d000700a40c2008640c812070301081309032544c10140c0a4407080711880 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 974420575 1250 974419325 974419349
    0xa0803090f0d0816030e0304080109021c0b15040207050f060106031d0304050111161509051e060c07081207020117010311240a0f090f0305031b01061e 66
    0x8420701d90108203040c4003030640c0d0390302c0a1511000c040d4099055400200f02c145540c070106101c1503001880900004c0202c10000075428078540140700314011401060031140c1c403080111400504004201c50b085000c041d803c808100032940410024800c600001c1c1c110301c507003001e40c41c6010300084c400d410703500565400c1c0000c80416066180010010581d050240c00c00d01c0140084c0d40704d0342c200c2070b50b07026400446402c035480c0c0000052025164020034920b022109100407010741101d41c0e0001804191030f4a4030020008110540c040c0d07488a80510a06c400074080d41001d90402c018000340c07112000362941100d4021400104d07030b02042040340401d1003003406140000282c0c001904803030b00140c03a0151400c1c0201000300361103032074140f24507042c0c0c0202808003408581d0003a251f0101191030384041420b2281c0080c0c40c009031644010684059090709000141020003954003c0c4000070851407400002d100540c05000303580c00c001440101039140c203940742100d036102412503401030081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 974421825 1250 974420575 974420593
    0x4030e030312160302091c031e020c101214011a0301050607030509040609020f030907140d02060d1d07181505010e19290c15070905030a080309 63
    0x10649078000c2c00c015180495007040000c4241c0300d02c0c000d92180b03000600c0c1c014a00f407181800038548184012502000380d01d0038450300101600000c1c15040004031460b520a01418518001e5a030b41440902c18040c0c51000000416140681c004101028544006000383e1119200b4180151000d11a9180e400c0c0420224199000e456084a0503a41c0c0500070600d0002107860903644c41e800b00401710f82007980c80c0c90000391a90944082c00a4844441a0981d241000d0580905d040980c0c6c2045005080802905172140c1e0b82c60107141030141e041c0e6843e522914503034580c20040055440d2070034444a0140382c06249040402c0107000c0c0c480c001d80c82c407068500c00c1c070441c00301c4101d020a122140420340080c4174541c050500c26242e08002402411040f503100142d1410541da544403204e00b100c0080082c010a110140806084031034120150030b1000e01e0120950302d055498102c07120011040100304024814101c00001d0003000d0f08481204400d4907000540354011240035103180544912 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 974423075 1250 974421825 974421829
    0x910170703021e19080c0705120d0c18060318080a05070b0106020114240a0602070503010c0c3f050414060304150b01020c030f070306050c040f03080a0309060e0604030e 74
    0x1038400950558218250400700760f20245d980b030348013400d60a51442d01703000820000d00108465612000c02246207900d495503804664241c4010642d008103210b908108801e9081210000000300d07a80c514011424001c200c8642071844d84410014001d10300c0010801506a0040020801c1610030f200d401400e03030340c0d4007041b0300301c039107110305000411090380200d50800c541441d583d408005204c1d01d8580807140760000750800f000707039001c5000358204071000c01584c0f4003803082842d01402401c0000605030f2540e80c140004400380d2030036100d9484124420b40ca0b05035400d605038004a80901601803096921000c3d040f0781092213401e560380741d14551010765080c014141c9020f20b501141c1451000c241d941004041c01101c1c00c141d045108202e060000d5580420540c0801d0000300c019007025400c0d414280f05a0308010140d4084850400080207078099104280040300d4018189503160100c025088024100d0850007034005800c02035480511030000c5100c6000e507100e80c8499640340b00f1481 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 974424325 1250 974423075 974423077
    0x12130b0a02060408070204140f06010816020316030207050d080712260402040e100e01060b030606040b0a021005010b0315100e0d0503070204050c0d0608120910170703021e 75
    0x861001a00b000c1c000c0b41c009141c0c04082c0c41d981d40300510210f070040110844541c0d0110845103d2210105001031007190358020709a680c0001004864841f0003003d007001035942d100d1010401140f21000c400c1005162092049002030170006200050300c0744a4104441c41c0d42080c031040d03036011a0180307803e168030300030741100003420f01280c0c00010107031080314816510704d00144181e800c86c0e00c1d032841500902083c810883c2090010000191480c181d00c00b00d401c44280c3c1d000b440d0040c1040043c031606940c0da03810740e4122640e00ca406503407a003444000b00c3c1462054840c0340e019030300300400461a1071141d409107200e8101903100060010300142004202c0c0c90040f41c490224452498120103814084040100240581d080741d10700700381540030404440084a011410800200e024007402d4803a000c0c1a0040440c0e000419000d103a5004560081c42140c0400780305210300102080314a004841500009480340148882450a00c00240c003a600c2500c1030103800e030202c6090000103010344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 974425575 1250 974424325 974424337
    0x6150c160b0a1727150a06030206030f0a060b1b010b09010e1503070536010510051c090b0a060b070c0308030c070f051f0c021b1212130b 60
    0x10741c500a0107440c00c3c420040ba0707900a0403200b541846080c1d44070700b40e4250a11184181450b0000f44200349040b05e4a503c1020054400e1520b281465001c1001d0303501e8400750381d0032141d06480c0380c1c1640c45425040004014a0b404120440d501281981a00b0080342c00740d0400070301980280100d400103c02c010441100340140c100018000d0085610744880c40b45821070b103140581125410380e142c8000650407424819640704100b1441341c0c510410542c520480c180b58041c440c2105c1c19410000002d10024510113400c080090209550101820415072010040c09400041242e1001e508104d0b01821048540c5a2401e0030300000040c010080402c80710960b0300100c0002c44030f81036580d03241d11680090301c800c0c0d480d0002e00005010505070801000c003140700e003005203010000c000c50403140001f030391000324415140000200e001d50300420b00c00c090219001e070314000c418050000172014400f00f1290f01c203900c9507500042052464900400c0c0c003030103032980c0c8040159903c5103444c03a4840c2c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 974426825 1250 974425575 974425577
    0x50a05040f153c0306030c120507060206130b1e0a060e0c1809090a140f0607080c0d0e1603150b0f0a090504060b10050307030c02190b06150c160b0a 65
    0x41280800c0c0383c01d03060f000401083c202c1c5804110700d60b80e611101e54600554101101c0e818519210a0820104000381e40041c1941e0024180a15042605100342d01031080054007a0781203600050011038490380e0070b07010003042c00341040b060500108803001013480307006107503a0010b22004501141c2d40d0609449550424842c40c2040070703804c205000700d000000d024100d2622460002a00040014030751b0416542000d0040501640090f085454110043c0001003030040f94410701422252079012182c2160410402040450000e01840d00d00750710340010f010a00030354040801005007070440030403002103607501803003078503040f1003044800342401c0891548503111004c200301c020030759005036030f0090080e0310001e1620303003610108807903032549000080055800001c21a105800d1b200e0b075445c4403000e100601c128643d50b002c0b01980070304500040e0180c40c400000496075991441031036107848106040c551118401c0302500d54800344a810803a20082160300400c1c81c014400c15114000703ca = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 974428075 1250 974426825 974426897
    0x61602070f090e030904020403150506010905130507020f0d02010e011109010804150908040306050f10050616060209031009020a0e09062805010b03010f12020d03050a05040f15 77
    0x14200100e0b0051000c000030541601051101009960702c5101901c02540102b0604910720000d014800072a40010070150500c100030806010985889004046410944a00084640710000700380d00c3c181d00c80540c1c0d40c441c4221105401c10f107606412140d08440d6410090001041d18000203201c0c0c0074031125070380098a03603800a404140d0807050303c954200801400514041c1c5a110303c0359684c49034109445840d241c2040c421403c08076411507034082c5101510030b401c2400d090002d1002d00c940d112102045074000c0c43c860034050740b50704850340048020210f616403c1c0002540d8098038150400381e10414000300b0001340740130284c0700e140c421402800544940d6640c040003808000c0448825009444080c1c00a9500040e910689010344808e03988107440b580b5120201c42e5103820342e0071404001c2800510b03940180c131110300b900c145640c94140180c9420b040001143c49008903032040b003400603c0c1c600000c011303058601c8000070407001e5030340c2240b02817020401c414512041c00520040e0710 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 974429325 1250 974428075 974428079
    0xc0f12040807050a08121b06071d19092c01050708061e010c030e040c030617190809010c020a0b1e12060f0301020409060b031512102a02061602070f 65
    0x8007a000403c1e40300f164800c000d0b24080e14041c01d5103015400c0709c400002c580d01001041c80007141c2904484c0c1b44c0720882d92140d00d00c06201580c1c4004005114244140f600e0700300c6049040f0103000c90207004507240795004a0090f04003a0240070b8181518501c0c08224040e000c21810700707203035104c003075001e03058441c1480d00352035000111340d40d2002400035010814203050f8803500780d40d14040c002010105036004035074141000c08184c440541883c1c416200e5100304c08500701c011030206c000603219005150107407107081c01001070b1101414420002c0d40440c42c2440403da000301c0d90f001c3c10f2040e07800c03c0e02035680740d104442c4000a00c02c8681380007440c8041c10001c0d24900c0d1100094445032409400581000d5582e001c610580303400d81c200c603074268008420428500c9958003110800c140441d0100d0400d004403400c1070f11909251078848155481d01000600c4090814119000c03c00101d4100d0103102107070300080d1100000d07526410028007010303102643c5031000038040140c50034403001d840e40078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 974430575 1250 974429325 974429353
    0x4b020108040f0501021621021c180b0f0316051809090f01050a06140301092105040f0303120b0906060a0c140625050309070b0c0f12040807050a08 64
    0x6030ba128000c40d590741d000c215042a550f4948883d4081e40e100e008140da5241301e60341c90011115150b5040300841d230017030001c1d06c0049143c096070110034500b03090000c250695900c0c0380e0701d100041d41185062038000103004030000c04400040d442100852580548110000c800725003910030780c4140528504180b0f802c100628045903030b9504242940d044407800405c011901c0c0c00e4a8003142c0c000a40c0399202c01c01c21041044101c5109405e00440003080680e0903680c032040140000305486001c40c1d012034800c0c8420f80500b04130303800340c0740404030354540507a2490000e2009540c0d080d055056810030500304484d00340300004600910009083c60308100f92039504403001c0c1c21244d0184c03008142d14020500004045c08150701412122041d9040502c4040c1505841500303e60000108a410020032030313407401c045200000d80349800234007503071040005440391400480b0001065036001d80340006001e03804402c004c00c1100c512038159641581c0d541d04101005506126800c03198019503004c2e1a60 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 974431825 1250 974430575 974430593
    0x30f0e0a0b0d18080c070509040b0a0c050c01022205040e0709020906090607080903010e0d0e1309140a03110f0a0b0406151403010b090408164b02010804 67
    0x300e0000740002c2c0d640d6a0714860428403101801610300410005d058440642c040c02500040c4c80160740d1250701c0e040039a21141080d00017400c44543c20765419401040510400490350813078203c400030354880100f0328214503556081c0cad0404200e46003c0e000040c0c0341c01c2074054061402404000f404600707150950a6002e0b60010200980c031076003c00c0325402595582010781080d40c0518800783d2107000750428142160390f82d41d20785400358001040c51007200d520000c480700700b2030142ea005200c2070300e642506014100c420300042041c12201c40d8104a450002080702c40c2c0d0f0300966501e100c0c803e0503001c154564900387d6407100e80d030700284540d90100d100142c0c1c96030050702c030b04000520110400c156104244082e048010044103210f004c24442c502409682080c6808650000c0c203424140c2d200c1100303100b400d4840d89a60700b03001000062009a070141600c0403040801d00d5000501003008400d030041415104010008510442c4840f00506a1708003146606841d40b541e5030300ca50701c5500c00c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 974433075 1250 974431825 974431837
    0x130f050111062e0b0c1e070902072d3302031e0403081e0c03150102010e070807050406090203070903081b0a1a09060c16020a120f030f0e0a0b 62
    0x781d06482c503410403035400140401d00051048104d680d483e41c800c031400742d00340031042c000d4403454840007111800d80c0c2d501013802d170125101c500c4016138444541c07403c0c3c02604c08500303482502c102e00e808407078030755203088110703200c2903111780c9010b401011504081490300c030003000300c0504074103c1250140c80034601e6008540140d840b0f2102c252041900c3c4c588181d02808030750480006e05c0c0042800901d003a01074507032044c505001c0e900b10441c036084041401a01006080c03c00b00d10003500307000610f034000e52143c540302c8084070944000c2515410416552a060b20409015500e000000540003446100f40c07030269038280d5503400f00a145846100c46600402a96403015001804003241d8050422801d418144500300c21b001421529120b492110300c02059226581c221004001600b4202002c80b02d0904492984214a80c03050001c1030811030360350020315000c445440241d0a1007040102480030710b200e0799640341d4100d84010b08030b600111620001d50403030200482071000c80c00300303805411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 974434325 1250 974433075 974433121
    0x12030203040801050907080601080d050a080a09050a060c1206051e060c030d09061103090a1707080313020f03160303030903170a0b01080109020405090f061203130f05011106 76
    0x10801d52241c80e01c9007115810b0761203a400e584054070400640005022482c010034000e009001c85607045d40b0f016046104200c0e00d03104001c0700c0c42c0025803170a55540704690960b013101c11903100d00003a150506c01011051042408a81401d400c1c4100700c0321801400280c030030280c580034480340c00c855080c0c650b4241c5440154004400c1c820b00c4414001000a0000c902c05501d000c1103051032401c21208039050104141c040c0b020800410118071000207250103403a41c0160b101005a080006002c8103002d0070310001d1822500200348000d031802404c503220028001c489841000410408140d900c05062104441c0c022400000308007003800703a808031465038080c2c24624a00d14a030011070300700742d404540030000c2c550b603151502400d507171000102e405010940350440ca4141060002441d981000300700742c41004180c000940152a001e2804941801580442e603e40c1072000345003844901e280102d1410003503007200001c00390b10881e55001d1f5035003850003030301140d1140c2c810300940036070303501d5150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 974435575 1250 974434325 974434327
    0x504051504061b090b090f03031308010b130605010f030b0f0d0503071208061311040305030310151d0d02010201110412050f0606011e0c020a0e07030f11030112030203 73
    0x2099003004001648240e1151100140caa0058a8581440d074202c00d0120108034000c2c40c10b004a03140c4201b16600900101e80c0000e00300034034800680380d4410180c0c500f041c0d604182e800502c103401500076054061040703404900141c0c01d01c4011040301c40511444e80040c1c0201641c210007400380c0d00803003258901400c0c0c8603041c8072050101d80310311500d00003201c10f6440000d0003801c0c064002d480c070720783c0300d00307842c03c442c8609007000003e0300d010b5001c2482810680c1c030740c84944100505001c640045601106481d10303880e05503013081d1500600c0c1f04202c5403c80c5051901702803480390385039030000c83c944002c502140e8040030a0140d03000034060128150341d0381e40079a050040e10320014200804011401485a0480b403400780d0901407151a0a2955441581800516038021180001844402441101021126038102c0d00f1090440001c1d400412084011584a0300242c0302c900c00d081684042c0002810003003c0802c030343c0841004520800c040c0700512264080c0510300d07101038003c0c130440b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 974436825 1250 974435575 974435593
    0x303120f130c1d070c0b0127060902071509020307030f0501020d050c0c0c031f092402091513050415031406090f03120a0209060c1b041a0d0204050405 66
    0x203210407a08503046181c2010800c054a5000d250f01c000c500c0c0e00c40841e290502c12081180e03501c01048006000e120100310003021541289076041598407007511081c102844101c1d681c0988000035800080b007558420021082351000580c42c0c0180c0e0380240c0d0140003070000c0391441d02c0d000c0038418046c2017180c0554003006074880b00e186602880380140a00826565035030f1148060f0340c505189202c00070300940082d84840c06241703501c500340301124450800403400d090709140c007544058001c48522a030760341702c0c0c40c00c2c9946502c5a024013010b071829108100d03012840500f02c12580110801107215503a020001c0c8414249600b0264200f2800e041c0882c0d490744030f03941e00c1d00000900c0030030480c40e4012070420803240020061000c81140c060040d61030440400f019a2015000074980c5541c5a00002c3d5981c03603440d80e000b241d00d10031100c01581c1c40340b041801c2d14084d0b840c01ea41c0305445181454410902520b00c1040740b01c2810000300040200c41180e03080c0406041c0051098550380203806517 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 974438075 1250 974436825 974436833
    0x150301050702010c0e03010b0102100f140c040e0c19030c0e060d02130e010503030a2d03050405010b090105060d1512121b0206071b0510020d0e0303120f13 68
    0x529030007040307203400116126a400750020040114641958032036814444445c00d40d0344c0206001030384c130650f107501107071060b200c11a003009444042c06050340ca031040810400d1103080e038400b40003030780c6040c0625a03150f220380f4180d074418040c3c021016842c2040104100318903004c5d912802038580703d42081d11b100102032001941541080c0c00070312202c0e80000b144181c0d00d920000b508060407000088003800c1d410000460340d280550104901444401c0400281d0301101440f800412030840805000714020080000e0107401c0c2035904031120740c205090b460040c42c1070144070781624000b80040d41440d800c02411006050650011082d44d00510f0005c64000285a002c8038264090355802c4074442541200500c00100c44280901d205010000840140e0740c09007110140f40d0480c0c00100e90503907466052458501e958040d5620103401b0f40074124181d008503a214407504541c454900680108050588174071405d4000014038a0380e000084414200c0c040190300610b00205104480e450765513 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 974439325 1250 974438075 974438081
    0x60906010f050f222004030309051509060d0219020703050d030c27150219080c0f060a050115171f17010b2d090901090204092a180203150301 62
    0x100405200b500c03148006a5841c0340f6038036030904c2c01401706071841c1c40d02d5510020182710090003514072620305c250301903100e5110401901d10410300104032650306c0755010170910003503000f12202d4580503441400d010390a07001080c41c02c1141d400401600301c0059240b0114001c10303500740719109001d800c000f100b0005201007055001c0c1c16026000061241c1040898012020200035039002c640c0030203219481c0d29200740b41c820a056102105c9038448404820840c03d05050320950041c503c100e01c04c10031800c60641003a4100c8a010101d800000110403040342d50054411102207261308010100b044491203001034251035a0284c02c1c01d12142e111000d00d501c211440110850300d03911110402d0302450591131110741400324845844001c542486582d0415284d02d10035407240cc200c10000300d00740429000104986c0d4024010464120359140441f002c0e10607099042d00070841040e07841c0c0401c484030942c0c0649000496144880620300740100103503100520045404040f03850b5244580ca00340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 974440575 1250 974439325 974439379
    0x910050c040801050c0f07060906060b2107030c08060f010309021503070201050106030605010c0609060f0f0f0b01020a0203062e0603050912090a0e060604030807080408060906010f050f 81
    0x8208280d807189403807403403800d4420141c003501c42c0ca1000c0180d1500004104100c0d030300b039680418080b030000200d060040041003154032188503032000041d0b15117012150040185401425602c428180c1c503100821000c5500b0500442c001c00d41403070200e126842e110030440a907190515000c2603503441940401c00c0c400e44000041c12160022080c040f40e1034080c02900d000d841949020060390b490301c00002c080d45501900605481d684114220920207240c001602a401e00b00013030200c000079a0300c42d8020080d44010a441614024600010798030105030f44800c90340040041040d40c403818480028407441010b5500200302c040c812080c0801501100c80040045890019661824000031414880c2c031540f1550006010010008640e40b802d0228056410040c840b0351144d4400380402c40e0b03442150000b920791000801c03c441000002802402a03880b4403090701d0464a640040c0c80d0b989800780140e5407401040007060100e4141900402c070700c691300410100c00b080700182e40540b030152103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 974441825 1250 974440575 974440591
    0x403030806040f020a0804140d1413050415080123162601030b060f01021b03240610030506060d0b0d06060f140d110d0f05010f051008060609010905091005 68
    0x46c10001800b141080d075200690740440034150f030918800004104d400c0e0769040b150014400b10f0710314545840c910541e03000d404042c100300900d030000028851340120601c00c2c2c1e00550700746068032007914010704a103080944003a14083c41c5072601c5850070840c2d4a0840302e4020030040d00305445401d1071511484501180d00d00c1111025411070500c41c841e10707401001a801100c2e003060b040010303603002440900343c19034240c1c0310507950790800000341000c2130340200030034004080703941e0404020400511030140303074229038030f00900c14040e000f601581c104550480e031005090009000b4094580c01860301c101000b080c1480c1c00d0651307038695040b42c119401c0381e114100380c000140640010ba41150f41194403c0ba066a503400b010340d9114103d0304000680f40c0113078030000c15002044042148944900d900000034042c854100035040c0007020111075035848885202c400151032800456a280a614040c0c141e550681c200000f800241c40701400d00f0440c2e10814514010400c142c0c41140e02171306603 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 974443075 1250 974441825 974441837
    0xf060603020406060206040f030f210c0f0c0804030f020a090f0504020901090b09041103031e130504090506070e1315080d1827050f06030f0c060403030806040f020a 72
    0x441c01800b085542e10f801c42c001755841801840003080c06680d400301a1981441c110000b40c10014003140d40310b89140502d00180394900c000d02c20611643c00c4070340c0b06052aa54540c401c0c031110f0301210b402680e2440540340381070411080c00801e081203141c03e100c40c0003400c0512035640c0c1e03502100c11100d00200b030350440ca55680038081186882d07100c003801003680c84c0b010f005070441c4400140714844040c00080002d17070720320303d050070544003881aa0350300b1801f901781d04041e0203130441c1e800b8280c0c014080c1000c0210703059404200351500f841407202d80c41e080f01c02004103903280d40c8243c5284548404145d2712040f810b8148078960011300134400c5142d01c201e0328036491440e0898a07032905080d01650400d000300d10000080040a49000e41c044800317040c0c0714450000e8203170441030705002d01c0343d03907a4500d82010304010b21a181c0f00307401e50040000350100c0300004449040651a08000d85460ba40900c0401040000c24495008650002030003070000900311103032803c26049a20010000000c654 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 974444325 1250 974443075 974443079
    0x9061803060109021c020d0914070314160b180613052e120e01050a0b03060604060b0a0c03091d07140a020604021512090f01060f0b07140a0f0606 64
    0x18140300741070042021801c154107040304107007001d0400c55203808904105501203a04071024000350000c041141e0400d00c0041080b1080304099111003643c04181c540f40700c0c4100c0c5a1061900080c0914240c1c1a00908502030b4148403031629264011045c0c01807a403620781c0b005902d9a81c01005002888045060038003903171901051101c482e074900351b03801104180c02441038041045040c0c0048004441c45c001ca405402c048150004101c1903135203440942c40e20040003441407203a4848010150f00700d003210303529a00e9400301f1003036030f12034000d90180b041e0912001c202140034000e004030b801d10a0515622103a10340810380540030003e0b80d804c6000c1c405100340000150025501d516580e03082d00e20714686006480003a603125400303000203007c2e9150f218110741c0015803809507885400c141c0720811240c2841e8512a90b9407072040503404641d460020700192421f600354001c81152400c0120ba4145500354880c402c85144001d9419228000c80280b00000780c402502d100c101440b90000064981c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 974445575 1250 974444325 974444329
    0x2040203361b104e2a0c051209040b0d21121a1c0b1f0b0301090906140c220803040b0c0f0606010801060311090618 51
    0xc09510400c40310b6410503511100c6544550040d84242c09040c01d000b010741d2440c440000c0c1c2e007903920010308440c11240d41810403481c2c41441011503d01408a02d81a12081440e410b04484030b403003030050854415060584109050212a825842a820418000109030302c43c20704068180c02c5041d06640c0c00030380c0007090301e028440d15013454402d489427002c1d030310150b41d0001c0003403070381080340180c056400030800d81c180706041140072031418520074030940c01111214034642d045140c1003480780e400c10700240272900e295022018415041004003e860300c442100074030341e03030764510f03050000c0c0da686901240c403c198500450081411540010700075907a41041000c54036000c1001204404400c18086a00803a0040e154a4a8800710414000150120010100d14103500000271804041400100d442e1024040c0c03055108a100f902d40d0700342100801500c49000729816408a4018001804418420340c0804450408820010b10780344c04800094015001081d00d1704141c03608401c1c55000b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 974446825 1250 974445575 974445583
    0x17160f0606120c0b16020a0e093319091a060a0b0f280201022a0a080f0d050f040201020d020f060106031505100306150c030c0204020336 60
    0x400c107040210290000903901e05406426074820b02d2092580445e9000043d00c20381c116034000c0c2da0040000c1712990360303a4506006100f044400f03600c580548005c8280321400400d0521500503400341a205125031042e0f101280380b0040c010400d40200809a001e50600c00d10590454500503c000324512000c900c0070042c2c3c0c240100714038040c000b00101001034041e9001511044800340001d25243c840306040b03000d40000e42181c0d41c05e500c03a140443c504468041d0b00501d502c54600c1d40112041f5901d460300000440410651000d0780d00c0003d040740880c03c0c850260a10010000340c0c03920307200c400f109003402d0310010740303406134401c1c007410500c03045603010011400e01101fa800505025992800c1c8682c44450520424051680710300341503a00101100d81d51001d010001e121122220f1408002401054140603c5070b0035440100d0b4440f0071405041d800c81096030541d80c0c904402c0b82c980c2844040e4001810126010040749540a801c2840039064080b4403545070080443d070519503c03071850 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 974448075 1250 974446825 974446829
    0xf03041512050a020c1c020601030f020f130501090b01090812030c070507080c0f01020606010c03051e04231206011404060305030304060b01030606030e031e0c060408040911030f0417160f0606 84
    0x1c003c40014000001b2500401d23228112071300031081c40703802141070010900000540880c1644041c2041818110031460343c407590603604a01c01c00c201c0c00780c542c3e0041d04c40c54284d019143c1164080b880714000700b42c6c0c440046510030510b42046083c04015580c491400450350019955604286900221341c00d00740e04510b491071003440140000c1c1007640003c3e00c0c0d0030382d0103030140400100191400d007403410f012140781100801c21a05541d980e071085070f1100400101d0f200302035161500004d0280d8600a5640d078802003451000d08156480c041f50500581d40c0e000009401a8450b81c00001080090015502c964025140800da104040d0001000c40d00e85400ca1014585008245040100000182e0b9101c004078941c050141012000341210360054046101ca184141c008100030008400080e104580c0240000e0000103000038094220340000c42c1c4070002c3c03202000008010800b48010403500c1c03031041d0202e5103051451050750300003443d061002d441c0403068102c5441040b00ba0312a40d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 974449325 1250 974448075 974448103
    0xb0a0306030506250c051204171204030b0f090703080a020606040506030d0c11060405030d110120190e0405010b09090f010303140c0c061315020f03041512050a020c 72
    0x5100204c0d0959402c0d008410384400e020042c0405070481048410003000c015818144030340c42e11542d071407150041360300101905415a00643c4080c1401005540a803400e41b85e001019103115595442144940d100040c1082224491000300201142d80c000007060b14540c41c3e03018050b80e26200381031105644000e001c160181d44052200e00301c103030b400061020415400260500c1036880c0400040c030074040c60700b000303134980901c2101906036078201d00440084c0c0c851100901c0109416007203110f040d00e00c120001140c0c0303410003040501ea641c0d50100c00d460b421904125000c8081071001c0780131984242c0042d02000000980350500740350403032041350b2168401c2c202c9421981103070750042008802c400c1030400505d010075014a0380100780003040700300d0406814191501801c0310400c440640303a108051001c4e041c404048151440856500b103041c540c0001945800e01c0c04032188101c04c1d22580c038008210800c0600204400c440c003441c2c0c05000e1041d40942c8642884105904000c0718818443c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 974450575 1250 974449325 974449351
    0x132a0f1401171303120c05070b0a020301060c0311100c021b09010308121e04030c11090f07050c1509010c020115030b060f1f090f050a0602070306020901090b0a0306030506 75
    0x2ca01c401c02c92003607680c40100d061510380600050320381990300a40c2c1c0714030f6154041c01e090100307a00540c0800900513860040c1a80002620350b0b00030312040344070a0103400300286845c02d520380804d000c0c10a0100c00c0c0805001c440700c0002d40480442201c0140f44c4020068211640302c680c50101d041055102d460100e4640680d94515541c899052041d5180912a03c100320005070703105038081920740011542012500bc6840d003850000c0c802c200c6040d044030105207180c00d80180c0d0505110311841030048000e5200715855056003074486400c01007044245115000c0d0381c02811074041001c9020303500900c0040340749080904040d082d81d4000c44070214102510404002140c1e145a1094001000b0b03500300790644500310103e060202e0440b110039070081c000c01c41034080c0768410710040888000c03c2c01d640c4c82c0340d00c800400102c51700c144034000050780190b0b424070100c0c0711a80200f0300c035a01410800612542c660f150314494101116100110b41d40701410001d0207400d00c030301680056984061 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 974451825 1250 974450575 974450597
    0x31608060a0b18060418020a0305100608040605060a05040c09150201050c1c090f030e0a0902031608090a02031f1a0d08030a110f180306132a0f1401 65
    0x10342c8140105100365484403c68203200307003103450302011940034018a200711101004908540e602a52011100c080028a0b18000504003040304c4048400c1c0c8a00740d54500e400e40703841c1c40714805054003038202c030303804500d4480c002a150740b6440f03180750f00d81c45a12012042890003055031908041120314400b0359041001b000440110301046418a0240034851400440310560700002004404001003071511801c40200070300da04218419070110b8111030080c501c54403511180180e00054452001207c4c0340302082e070b0264020007143d98000480c1084608020b04e54000034038240c40c20b052464408100e0108103044420750096041a8501503a00c08803118100041076440d01e005030301408151004c00411800207858010950104000400740d85034048903000090f01d501c030511030389440d0003140c08015203080c0440e0580c4580c81d078035544980318503161a20080310810f084180381d50603001043c08489020003070400054480c2038120103401c6d08160400407600c0405125506106181e085 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 974453075 1250 974451825 974451839
    0x32912010c021e030705011d010c090305060a0f0e06040b100e0c0307081f0303050c0114010308030a2a080601030b0303092805063108030d1a0402031608060a 69
    0x204285044464500003d41080030303800c900f0750044440007000355080074008014111000042482a4805002004000d00082007990a1540c41c4402001c40d080f803c0003a103a40240e52201000300340c1c00d103002c140041000c07030141c100701d000c5170b08032203060034030b8107000d840984811404058034560415894509105030840b04500000f03202038200007032140058011001e003030030441d010411070301003442c203a00da18007d0002e80015100402540c680a4501050f280c5005960b040b40e411105083c99074890052040103000c1c2c041c05c189840404500800c1111280304c0e4a0450864590342c0b1051414000001000d031a01500b0151290b403040c88000110342c0c3d071010362174484600402001740701c03c0300b03400895220050f80c091a030040b0701154411405c00380e0640c0c1a68410300d81d940156070100d00e420a00508158050350107964814001c4000c1907800e40c1c8000c2c09a28107443c0130f142460140c0014042c0c1c1e1048034a030754035440c540303010014a40c009101c0ca030084400c85401d0348460030042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 974454325 1250 974453075 974453083
    0xc12060a14090601030f0c121109012309100c02040f0c0f0e0f0a0602070f0501020a03090905130f200906010c02010815061207080c04060e04050601032912010c02 71
    0x201d84115048800301c2c105a020758480e80341c24100e25010f1100603061600a007040c444148024421400c00e4200d0b68030380c01c410226601c0c80c5058491804000100110300300300540a420961030907010084a4030980d1040b1000c1c02e0104180e4580444004c94418041030b100505580100c0600b090075988510350000d041d0440800c2c0d900c2c1c01d0511284c2d0000081d001241d842906410140320038020130b00a80c045588800d80e12003684060000d59100012692919428409000501c440c9018040205560050b41d0030208e10782c80d2100e0907010762901c006645c3c0c05d0300100c3d0b01141001d80140340304001648190f0500003110f0341d0000d440c21900103010315900100c024100145000024018404144065140342c4050b1100b61240c01288044090001c00c0d01e10750701041185000a000c8200074003101d0540c0c0007942c9081c040704c7c1c030001b8040030302009030616051649810f240c68044500e00010049401e44000006140d1021020f00600040c1a01c1001240c1d040000385000303550001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 974455575 1250 974454325 974454359
    0x30a0b0402090d030e150c011a091b070809041508060f061c08070501090303090209010807080a5708060c03071110060e18330c12060a 59
    0x5c1800103004000388001000120a10f842010141010034100d04100341503005040c50406c03c18403d0040c2c0c09801082280b141c07c030b410040e100781030b00d01c4000d034415080152141d80d01c2800d1b40ca042c0409000050142c654141100280c1207406100700244c1c84108091900211030761040855418002c2c00700d105101c1c2020880d80c00060300311280304010007039088401142d0071500030480221780e80340040162044040c1640b08000403000458144400b040c074a0171210848010403142c4143c0e510400c00749580001449400340c00c8645903a44011070803a421001c00d00502641a40d41358545414449405a010121070b100500144101500011020340090101c00065144d0b0346000003101c4141c030240e80c429560017103040f03140c20240c1d40e0700f0100aa42e00d2040c40300c41c1d95650000655007911903168104240e01640b00d8020b950301c0c8115507446800c80c0b1651201d01107030541e9074604044142c8010030302c80030008003d240d1000c000c040076000007048400c01000e628003200b88034809207503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 974456825 1250 974455575 974455577
    0x150303030b0a0305010f0207050c030d050a200303130501050c0c0a0807110a03062703050313170408151303091806030605041101020f0d0f080901061703030a0b0402090d03 75
    0x182441600c03030b0b5203214800c001564403600a101c1262200c2021029402054084406100d0b181a2014900d00420060b0704000180d640b182484003011045030550641d41d0404030a4007101000d00c40001c00f440150b1280100b030a50140d07100305440d0182c2110001050f405044100f4410100e4484010a0003c1c0c4d8617013001d583d075194103103030810340e94851400200c01d900c1520940c00000b008880e40000c0359203a1720b0b41c103101020a14402806001a00ea2070060000c0c00c01c01c00a40d2080c00303003c0c0c1c0c050450051030720603291420704018480e60b5101ea00000115403100900c0d45000e070000c2c5d80d40b58400c1e1108a4603071103070020307500a0b004522a00074595404a420782028480451758801401103400460920232170401d800e10240c0c1c041c14025070703070050043c00b06c0d000c190000000e1070794400955584030407501300b40000c102d0301e102018164035080e540f1104002410345184900b1281511810040c44e41e03401e00e4170b0910212203046a00c0e82c05140103003c00744203641c800307581d19889501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 974458075 1250 974456825 974456831
    0x81e0304051501080c280b03010f080c0301090f0b0709180e0f071520030a050a02300d0e010c090f0e090304050108090a0b091e060121020a152115030303 67
    0x1034034084018082d07411681c8018408800000d42b0740f401483c0c40200c4421030252040121080185400d0f03803074024024240e85000041c903000078445110880e44200a03142c4580e5054407181900d02c0662071744121714206072250000036405c44203010480101900c42c00034110301d0301c1c3c03628030000300042c00c3c1120280b0007139017940750542140e442c10308440103140056a40c0c441011401506540000c181c880c014070130300b01580c146500e02c074071100707000106800943c0c00760034090400c04954401c0c41540d048940720245044803100c240a543d0014000c0d880c0c4507011414048805032071545684010401a03c0c48103111144001000b01d4082d25000c1c0713800f041e0380d911105841d1030308813905d00050129645004002c0360001c08910010305004010030024441054a01c2d170b0b94444003070090000c00301d90044481400305054058503401c07840030b012041041d41c0c0300d42c91142101c240b445080454603e002100400d0141d02503134122040250707041040001d03000c41c1c141e011000c1e000007810306507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 974459325 1250 974458075 974458129
    0x1e040f090b09340203071103030702030c10030f06030f030806010503070e0d030509030d0207080c0a0308090d0222052220041e0605032404081e0304051501080c 70
    0xd265121203d860302201041040d240c10030307a0081d5030350b00c21001903a4424020050203138503c1d0100803a0001a0010300400b40b00806804000c214802840810145584c1d9400c0d51408405401024025400303900c0003840a000323410003900000307004003450304002003041000300850b00500c1c0c4010590003968840d03020f030400d14041e075007841100300d09503061180c4105000029800035a4100703441064058444521a4006000d500500ca0100400e0a501030101142d20705148100c10340c00390000b0904201340c00c0e006140d4117049075201c0c001004540f903408120640a41520342000c075190f201030911726a0503602c61040c401e0b1071b2224a4141440c5540700c0703059a072150003e00082e089164880800b1a8040c040d0000b001c5602ca1240640946041c41c2c900124001004995899101900c42250340700e9450385150340c0000784426501680290b901d03070090311500614842d40c030500042030248507074145000d03a240d05030701850f4640c2c03040e8031001464541c1008101d100980e601c048681c81 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 974460431 1106 974459325 974459371
    0x112021309081b030c100e100606181a0d3b16080706080726010501120b210a020907021f02041208070204021e040f090b09 54
    0x140204241b01c6d464209500304d8140e5000000c2502c010410140001c4d08644113a045200010000c001588074100075146410140c451403001d40001244922034010f98400c0c4000440c0c1c5584074000c600d540d00c02d00c0300384085407590440c0d140c11000c541482d00c0401009140c030346414452406414103c2c0d85c481c51941c107540900014000f240c0c204482940e1586000c0e10200030410910501e54048080b41c00060840a02c4403500d01c19514042c0014040741d109144901c60520b4040030344425640c0078140c0c2105140b07040f05500541000320518184210144040e40210031310003000011a804243c81c11403100c46c20180740d41012540c030f400d0490141d40152015203000b1204007020a000714090001c1a200400243c40c0042c0030070450b4000071000180c0142240c0802c0c00c1c800c4200300700c240780107841d1501040118505110000704000e2002c1d280d00d821115020803e0840 = true := by decide +kernel

theorem cover : BRFrame.Cov 974280575 974460431 := by
  have h0 := BRFrame.cov_init 974280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 974280575 ≤ n) (h2 : n < 974460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
