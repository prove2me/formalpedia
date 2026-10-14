-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1193
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:41:36.636283+00:00
-- url     : https://prove2.me/submissions/29a7fdba-cd5d-41cc-b093-064f6af02fcf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 214388489 ≤ n < 214568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 214389739 1250 214388489 214388491
    0x60f0c0503070c06080a06241103130303050417070608040f030908030417071401080c030718060f0f022d0a0c080604150b01090510120507050c0705010203180108 71
    0x103142070342d050908a9031140d0310200542d00460010700014180000c0300d0b014450750b07005040b10110300c00307610401c140d00b80245120031010300c103014150f0080301c50170320b082c42107401d040e080307000b101181500c0380340141803600301d405142c9408850b03003901d1040d80d0001071440203a6200c1c0e00c0d491032030343e610354611820b961403601c21030802001e00d0300000c545a0410141000c1d06d1600c101205180752046c0451800101c1d03800b9a800c0c19040c02428482d907002144990401051100c05540c0c0d41e075034800740c40e0303a401030740a40640d070828031000411981c01050610204013136034804042407030340c1008a030740354020720582064680390300402c45115500101c1020003810380c4103a550301c04e4030b915018140242588020026001f203c1003000b007181d40070383c00b0980601074508001810310b600c0000d060612a025050007080c05501c0c06040b1402a10621501c05990304240007134500301d0b10041c100e4100421060845c8140c4501065070360010050b00c0300c00d22014424621070103103200445141d10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 214390989 1250 214389739 214389743
    0x7020109140c0d14150702010606020d020606130b150409150e0412120f0204091b0f0e06030402010309050a1a06061c0b01090b07081306080411040c0e0a09050609060109060f0c 77
    0x100d804c0103002105d51100c1506c0c4140016000007400900d0708102038104008100c2040840d0403072000c02c1025070b500e00c2505001c1d4940d110020701e498514000c1a090400c08034130a80801001c2000030f568001a0440048400f060515140346a510000e5100e221400d40e0b0003026004038501c0c6200080c07141d85081c2080000c45004aa0406200d00038001c90b4001c0c0c00c041840f544400411095a0060322802182c419170301d0300c0c854071030700301c2402003030008082c0000340b10760000408102968425041501d21a0b04403041c1c80500d0402c0c07030900c0c1802004c1e0041218802c030350303002844d680380031025038135043c104118003405450003c10000003028a528400e050021042000c94968072040281004600c940e02c40b940e07541c03207028035002140950340900c081240d08000c1000040a9418102c285e11080d9804103036105000800d854030200302d1003150700b044042c40c002505c41a80d07045540529000d48004100d5140c100044a6200040c0550380c0450b82d050400e0401c02d22440e40386d0a501c3c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 214392239 1250 214390989 214390993
    0xf061b060f1802030f07081c020319201207021912080d1109060405060a0e040e010204060e030a0807200d06020919030b2d07020109140c0d14 62
    0x3510459110300701c996810650035100020b1004000b10309042106101c00d10f80300c8000c0c0821803604920765a10306d45048092014440354103030320450740c020000d49400082000e5222401000074400502c0e0b00d24001c080130100e09090042c0e0141c08001c18400401010004030070703c1c041c0141c00b03003c40d1080b00c18030030500e45000c410024884484246210310588600d0515546109403440f010998002c800c0720980c0c0c807010000e440c19a520b10703003120f04a48041d6400d6858586900702500c0d030024000145410030b080c8440001d2040d0b06500800a460898403030440307003c2d070742041c1950b07641c4e517035402030441c203007004032131b0218010710340d0382600720303c840361f100c0c1080e00c00b8020450408842e07800b01d80039600413031003030000e00d046070050350b045141850b100c586a1441e01d07507000d440d00242c0911101c031071002070b29498400303014a09544401d0601510001e041140009000b0903840c0320541d440040d0032a0400781c01c00c0442c4e09006004010702003d03030300240f40c4941c0300846084903d81d8442c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 214393489 1250 214392239 214392251
    0x3030f09200a18050915010503060103020103110d0504050304180207081213080c06010302120a03020703030e01030b04060815011205060118020d050403030c080703110f090315010905100f061b06 85
    0xf10040e00c2407080e5018a454012509045c1703200940c0c42d2000b4154000044421540140080e480008000f0f045a40911f40415032480d0742281e010540714404070019001c3c100b0302048244030000000b0012240c1c049800000c0710000310b80c8104030b01a0100040c1440c10411801c031300780302c1d8008000e03004448449a0a000321041c0e59840240c1d200b40045c00480e0044001041545400300708035946607884005031500901c1a60700944450103400014180001c02d0107003800c9034840d034003202c04030b40080c000304459a1164615940c6110b43c01c06040c003021a02c00208918038000c1a042c00301ba031100062403e0f03400c1031003403604189492941d110b03581d03082c0503007110003480e40111405113003c0c0d00d00040c410f5500d50f005066020040034030090600300f0300b00780f0814907040c3c1110000d59844003202d40fa07a00c040f000a00742410030300c8020451040c6800410303000043c0d070000b8014149000c40640c0782360b40d519940c00002c00c034400d01022942e42250f03e00c21603102d50852311003d2140d0307800152 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 214394739 1250 214393489 214393499
    0x329071407060f11161a0108060f07090b040e0103051e0a1401140c03040201020d030b03071403120c07060801060e010804121215060206060f090c160804090903030f09200a 75
    0x5500162500d000700321035800080b09021b000680f44618118429000310151704108400795201d2024000c1c0c202200d007140010100f910503d01c0780060b005c1201c0040d5180d03603070401d03080044800c2c0000ea48a0045c9028000c00c88001c108035401c240390784000d0510040b8a803070340c00741d0b008205500c1d4055500e03401007014000f000c01401d80300340d190036511612230401b400024581030f9681d0340314051601c0d01301051140d58000622000f11140c1c40c00788103918079a28082400c0c821a00c02d0f003801c91501041c034035000400851139005803400d0360f813140801e0783e035808102d8018940c0803501c2e01017441c0340081400710f480c1d102d02c074003800424101003008942150400e07085401d008681c20801110728070620a056041c0001c0d070b00720034100c540c40310401305040000c46003072020782280500c103000156001c0d2903440d41c240407802504520300c29220b66070b424010015100c90601200002c0c41c02503140c190700b0f90f91103400b038140d42106441580c05400000174000c40500f00b0303440d0b440003403520000b034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 214395989 1250 214394739 214394771
    0xf0e03010c0f0e09191a0d0602030601020d020c1807030207051606020705090f15030a0c0807050909030703020d230c0a0b090607170a060329071407060f 67
    0x1031a250703a61400ca030800740c840b00400c00107660499a20408604091103005c855081c4a1030750007803c88400100c1ca40c10601c02d00007852180001500400024070080500403c1d60140d889000e00383c0075550010001901240c846c405050290750140f40c0960303020035406950b0001d40c0c07100c0d1500340149404000c1d00c60600e0000b465505141c0c0752000e007401d229a030b50500100c0c1c010201a10302c1e103003500700740b203900420603001464070303d441d0900d1041e260305035001c0000d90300341d039000ac0e044485941c03501041070f11100540105409a40d0340d00105020711400001c590100b48c2540c042e003003482071070344100c480c0c015440b03031410b00090403108100700f81c140e0401407035043c5804000f08820740482c500109042d60003800f21140340c00440c200656140c11403d980f0100b0f44164a00313200b6520115000005d0896401c090100da4904001a036851b42200030315602d0220303500354003659940c40e68221080b501d200c0075041c17240800d00c0fa5800044841d009000e0094170248045481032076039021710 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 214397239 1250 214395989 214396001
    0xa051b160201110f0d0905010302070f1b050a0f03230c0f060912060109060b0909070e04140405010506010809071202010513030503030708040c0603020307080f090a0605010b0a0801090b010806010f0e0301 89
    0x102003a002031000707220091b0840441c000401c020308042d800c001c2e00d921403101100d079041010b000b0241c003c0c074444111401d101e401c009000c00604814061383c807031203d2000042e480c00102c580e101c000d05400710f07819446807048185c88600004007116160a8240418500240300c101c1d0070820901005113130f81d45245200c401c80070140010030031f562502d00500c0a86400c1e41c060620b0340020410110540c0302c00c400a540300005007003035034040340c56102140050110217a115510301000d000d210030004103405c80c50150000b6600e007105920b0b1100c5254603180a07108041c1868903180140f80154000d20103040501d1240f055400c0b49540e07601c0e0f150442d442203620000141003001000104076080708846c014000e10302d421811031610303401c0503003884800307480300c035000e00c1e0340e0700041d20140200812504103921500c203105c696521505844182c020303030004004a0700c202c0c00412035005901c200000200c050f13407480f0558841000540d501c1c008011a4802c1040c5282000007030344003401a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 214398489 1250 214397239 214397263
    0xb13061b02010e0c180408130522140f07272c04031425291302040e0f06010f030308091c1b0209040b0a051b16020111 52
    0x30421552003c5224109036825004a1003501c2040361945140035030031079940d00a40c0000f089680341140c1d0b07a051003003861980a1940001c032443e40302c4034144a010001c0c01810004001d00144940700013402c035036842100c00541c5c1440000c00640d80900c1001c400501011000c6000c050f031486851160001940c6d07002a1b0010244610340c14003205544512408001c3c842100035050405650042c202103e41000217410701c404507900340400541c6142011100907981d611900c3c3d419407a05004500c0c1c4180c515200c007600c000d105a038840c2c108081403240c41f4114421501e034480380c0c20440108000100c4010300d03c00d10070149459802004594060025081d65140d0240b40d80f4006045003401440c0b111603804c400d02c01c041e10701c070088164044d1605406e01d11000400d00d500c40e040500c0d12140607510442e19803d210501244848503030058a03188400d12203a624407480340b1030108001800c1b942c94100b0030161032a01d81e40c8030b03090f001a205240140040d503207035400c00d240c02814200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 214399739 1250 214398489 214398491
    0xe150301050108090a050d0e0a05031b0406050f0f09150d060204080d05070b1812121605090114131d0609090106081002070501140106020d0311070b13061b0201 70
    0x41c03001d07607000742c01070383d0140100004180701070495940e41c2c1c903080c0440c660801c0c84080030842c203081d41d80d1410305001c3d040180488884a01d40034454002074403030341c81c441c06903103001c20100da503080c4012000c0030501c3c0600040388003103212051008200000b402281e10003a140b01c0ba0031944c2d070755084134003050b000c1c030703c0941c846060039146401c01c810041d048003880000c002c0c01c00000c074038490b1107511800d800b40e040c5403064400c0c441c0781490850030207500b02c41030008502280c6145552385c070307005140b1007105006c0400d400000380d07503920400540c40e002c15118140c00c032102503510020304034900a00703e0005240d13a44d5541200a100c002c00781c002d05844681004524240030f0b02d01d80c1e0180505009004280c03a000445403214032000100240f1600081c44000b401000d4110990b0000d8072100d07c800b1f507a560100035140d54404407200000307410081e1171002441003006450184e50803103d280341c20748a08501c0000328005e1902165019103070882d003005480751600c5118030b0420b51300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 214400989 1250 214399739 214399741
    0x91506270103150614120a0602130e100303081b040306050703050402040b040c080c07020a0f0f0e071706040b040e1015060c050604021215090102130e250e1503 70
    0x506000e04900c800510369180d407910404100c16001a41500d5101c40f0680e07000408080704046281400001f880c041c1505000190042818403440000001c40320402c0d02c4180e41e48808080c0001040c59210241c0050a224040f50140040890683d20607555210062400d0355035920030040c0e400072542100425521810001541440d000f0005204000c4408100581c0001005054010060a04001c40202080507411501c0d01c016034409001a006100c43d42d0740e0722440d80d140d0200c2400b46600c092140004540140e028501c50058103070344a001a1040d9141004e00000b000c40b07505869010351102d00400d050344003403014170046148600c021400d0b450820504405480d59842182040200e80001020a00210b074440e0170560459807031444070707080c441851801c80c90100645002800c07100380300042070305600905041d04124000303c000b503074621402c1c0d80d00200711003903040010f201441c0580071440c3d09004080d0710160404215480340500410340c8642030342202d005c031940c004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 214402239 1250 214400989 214400993
    0x1060e06090d06050a140c030103051509061302010917010608010b0a050d110301020708030114011209080d0e0f010f140901050103020d0f02010207150507120503091506270103 77
    0x451418000605482091a2000210104807150010880500381981e070f0400305900004680004805040020a035560f904082c0318042e5a0f038800e10080b1414800d0ac2c10b03140281c8039009285e0311500ca020064019507032075a58a5080b0150180120b042200800e40070940108030001c001056401000000c1d00754148203005084942d42e95105225250309141004039654038481d10143c190f202040401d40c0301c0407008280a401a150020100c01004c400803400d03a5112034046a009001d030381c1c0c5010308124041c0201200c600d143c0142a2020402c1a50704012003a0400c201600c0d01000301c0342e51080c40c401a074212640e159104166503100d02c030005864070564000c80c0c00a10000003000194510f5000448000c2524801010681c0007030500b41035a0003805104010403030548102c080c1160440010015401307080c013102d205526001b0307103407442e02c070701c060b01e204100440080968030740d401214048901d004020baa400078004803080e20281440c500c41310080030140f03031040954114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 214403489 1250 214402239 214402247
    0x2090a06030504020f0a0810020c01090b0108030a090b04030b060118030b13050f0606220906021c0c08040203030a0c11060705150c091005070305070c03050c041d0c010318050d080106 80
    0x85d603241e20401044c88140400380c07010402114400d0072200041e910444140454050715092401400704106000001440040800142242d003121b13a154034080d625900344480600441c017001d0000149000000c1540d400b030750a0907203901e0082004030f21186da9a56400002c0012640c50481c1051a04c8050030014100024642030102102074066450f0410100d04c0c034200001981d0348030103a20400c0d581d48030b1640e108585894001405555510f048054002003001c038180c6081030784c1c50512040346150ac03030020540690f900501035442c041040f08111010301411209942d0944038484801c030a584410007007240c640300d240600103401000d480502d071400024914151000c04100f00c00840d40c82c0440042d602a240c1000b5466507414201100d0500030b0043c0100f100340d0b003001c00300502200003944288850125400e10404204690b101c441c00010400c0002c29481000c64100030340c040d4204200110f847d0300d480160203595200d40f4a4500c0045100c004101b0181c0103000b21684 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 214404739 1250 214403489 214403509
    0x16050106140105090f060304080c0615120d0804031805030a110102060106020601060905061b0105040609060c020102131a12070302030105010e180a0507200304080c04060305100f02090a0603050402 86
    0x42403c01c41d08200c0c03241c000c10100d0400c039801910135600040014108030341d40c0b0039511009206c0d4101c3d41e003890195400000050708030f002170700c42c0c451520020840070340028104000c3e20700e0fa0306e001c110344071075070180e84155515102062a18000c0001301e001e48040005518260140a205104112850019091000681280d0110341100c001403007002e80203011f2900b1181300748c1e14a41e903140c02c003010b00800c2c50350301d51080c2d25508001c140030a1121a4210b403c0701805500c1c200000812000309038201d01c1100d007030b03239580303841400200103042d00003a614502940a00406d440c2c03801280400703d14000841e4030790040395010006000340d50340000341d49509501620402c0703910280100c15010010001c02d51912185c503030380019001842400000e00000c1d003c10030500030308186584c80d840c0e82107402015058410150b144880f4900750081804690b003000140688406030006000644a40500884816000c00189200d0340f1020b54075001440140d80002d42ea0070144108240500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 214405989 1250 214404739 214404779
    0xe060906150703050912030d050a02090a03061e0510080f070506251e03030b030c0604121a010e0f070201050708070c020a031506050112020c150c16050106 68
    0x224400400c5401c1e140e26a00d00072078104090025120b0b100c900e0100c3e124403079880855044400b082c40704100d030100001404049190701410f100e9030341c0e4880d0810407801048680c9500100c1e00c60100f02088241d4804503109048038060704820311446101d5085e580c0c10390b0003e440c040c0e0400308108a030001c0c481c168409241c00042c2c652285894005482409031101c4500c420009403202140000c14100100416500c010006010f1216440c1440442d50303c01e0240c002ca820060064403a01e03020898000d60003000341480d08050a0107511858074081c20000c41307012050039448400305040003145070080c00103c1c400c00052512a180c3e00c103e40e0044c010300300b90780c101001d00c00c00c190007980059000500340b8203000350300c2c200d000013480c80d001e82d800035000319240f0b0910b021210302a0040c40a90742c081c1c9034481c00741491441503089228001220701582c101100940c9101c3c0840b10068210242020b42c40c01c0042c0d0030070050754240340f2036007140e090390b40c0d0340e00300700c8000b03902c50f00341d0418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 214407239 1250 214405989 214405999
    0xc0302071205060103082508090f040605030a1407081006060f262206090b06090433141b0c03030f04140604050c09010b210703021605070e06 62
    0x1611507a9450343e148410b00000b00800000f1540448261030001207120405c482c41040034142210309041d407140d40601b062600a65600d80050748a04040c09034804482d4090010301c010300b40d549a9400008440202c1c010034000d0f0107000850f40c004015118018540d500c000640d24600305001e881240d020070141e0611940c404000b16403100001c1201622180000c40c00c1b141d550401003800c4032419101815a8410f90f07091001800300c0c039445401405d00c90303c885000b5031603c03420010301f10320450300203207408140740600420030444120b110814481c1780303151582039100443c01050702c2460198000c50003440c01008a001480c5a860104001510036a031400c40032900454580c8002401c00985036401704c08038007046075101100b60020000c009581e030740e0a045c0b80240c0c0722440350200c0d5101d010640004a402e014030f10031100308480c42260810800d1043c0150300c110b00c0300400d59800c3c19400e021101022810f0004080301c10f1140014181150a02d074200b000754201811141c007903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 214408489 1250 214407239 214407269
    0x909070e09070e0105090111030915120606040521010b091e06040c050a080603120c0a06060501210c090812040515210c0915090310290a150c030207 65
    0x141d03000011206c040c1c4080c81c2091700c00c24101070f214518455550902d402c04080c4400d401c1c22800c01000e059250500c644059154540108004030342c040c038044e0951240b8a40c902d90060a1501425142c0d40c8488001140b16100080042c00c404001c0300c0103541406281c0502c60074000030b800041d440b01040ba030420105035140c8000b00305000303510300c4030103009094002c0f440c180c0d0f08000c650143c04080003180c1d56944900c40142c0c40300034802007280c0940c100030b00032850b0340c0112440500c0414481c80c4180c40481401301c00042c0c88100000c009101084002040c400414404110102c01003a45565070310724102c107000f81000321300903004c1203e03402d0090044403000b9454009040201c020140125151850004400d105804040394000400d440030342d044200c0c034000d0561410100c0554802844281084c01912080921089507241200302086181c04481d0303501410000645001580754844024960340e1a40c0303002000403545c500e00d10320401d60f04200d40d00243c51004003e41803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 214409739 1250 214408489 214408517
    0x7020a0521040906151b030c081b10020a0e0d0803041103030c0d02100b1e060a0c2307060f09180b1305040311150604020307050909070e0907 62
    0x7034441d060a07032291040030440c1500712604036000c0d81c01a140f80b840030014695103017020000c281540e10b098001ca80180c4441d030443c0140c4541604141d00b50320390510306007555440740d501d036216147c0a82e00e5642e440104620500801c5441f1020015001c01659900d01c0680504040a0030b2100c43c03184091141c91000038004070281c3c3d4120342d21080c0e00c400b074102c00c40001d056004012810f000c0e48030700d0000f41e5485030b000801d07200d40f0900840822503100754a040c4592810202c0000300c0381c140a00003e031b0075041c00e4004050142a03807a02c500400d91580d43d0361010100054100c018800c008500c8128020501001c4000c0c0000d00b010b2041d1f441e42400034248007402d10424403099808807504000e04515000740c0c07041da900070b205445403a09040e10400501c019030342a070004482c3c0e69031905007034000031001d0b80d03641c1d0582e50b1219589d84070200000b075800240400104801401352041c5074075a0340c1541e00a0303c1c0760311441c4802c3c5048061000e881c078014030007801c009221100d1a2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 214410989 1250 214409739 214409743
    0x612061e0302091b09240a020106150309050c101b080d06050f1305060109050904030201020a02010e07050307050609121e01050604060f030b0703060b0a0c0219260109200102010507020a05 82
    0x80f0328117040d91203102d1076001e2003481c0005001c1c07900d040c000d00c80c00a0130f404203e9042d07100105a43c1c0340b900600828001403800c030100c0320821401001c40d403010340a00001c0c45c1004003898401c03614680a01e04086601000113800c02e03402048544200c08140f140c141411030040340c0c0a4031043e9102c0c605003c43c10001282d1406108071340c4030060f610800b2a680780d2140e001807010f010040e254200b2401d040c54024002d50001c8508030055203000c501849a0102240000071100f006004000d111304140c200100c0398409420558803100086540034940000d120001c40f04101c041d0354400740c1a001102425900002d004074840ca02c3d1150501400c1106154442a42d81111002107190740d280300c00c0e002011a500600c05039003012940e4480140c1c0701010301d0559209071074000525110600e0180f110f0320034001d83d00280d078449203203417402070a00d201040c404d00300000400e246000f81c5502c900d00810841881300c0e1a040d02c1c61122550302406003a41041e040d10007000c0ca10001d072540b42d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 214412239 1250 214410989 214410997
    0xe0f0708010b0f09030105040c03030314090723040e03030402090c070b040f140601090b1504030804060c0201120c1227030f0c020a080d021608070612061e0302091b 72
    0x1032080b004500c121500008106543c4010390140003080241030a00703005c03910720356034442100003e0516403c9048100c003000c10703d000d15403190040102a00345030103210548107007803083e0f08407034403210100066512401042c1c0714045003809580c0e0707800c1500600408000042004142031400c03c00b00c0009480d0380340182d0301036001032003110b01040d039180003018081700b149107000302d114030700000c01c060100740e1040c4003840e400c4030000030301c45602c101890280154800507080702c0c014801007200300d004100701c1c2c10319441450140e6903002c1140d2280c04a034682c94581001413a0746542c0b0f00c003500700b40324080d0300b0103580e4802400e9000002280342c05c9511244000c0400c011000c400c0790644c010f8a500d90015402003500e03e002d51110346003035451115164101c0140b14000e02d04501100c1c81c0c14030400d46407820060300d03104d420654199607004102000015142e0345c0d1a0011314041409030b0100e6011510001c1c00c403d80c03641c010440e000d00054810741c0d8903140002007500001e0300703200300c0d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 214413489 1250 214412239 214412249
    0x30302070b0f1e0d09050c01110a0f0f0c05030715030f0e06060f01090f08010e12040602071208070624081f150521071406040902072a0e0f070801 64
    0xf541649000710001e1103240944074414401908000200c01003000101c1c51045070380003a42d400e4590044c0c071513041d90700d040c0c2c4c0300064600c020003020354021982000d80d503009030b4007400c500799074a69140042440c010056002d585c6003401a21141c120342c0d450300584102084101041c40401d0040b803101742c603007170302600c1039226802a1a107403915900500e10000248013001d00c0480b040c0c0e40f10789140c041c080003071800345c3c40d014008603501c003410020291415200690b0040002c1800c1c41c001000311100308000703803002030f004c0c0550350025469000305c40701020746941c059540d038450014007030490400d0700512415003040009200c0e585118013a900e01483d2200c000c0f4680d10004042d8821207541d400c0241c02c601048110190326245005204044241e0411038404a940302014801c900e24410702c680e020301d042004200d030201513000340250750b0049005002101a80c141c001d4802e031481019200c11030b0b2a0b00c104800340085120725401f001b1041d00f0b074601e123400000101000014090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 214414739 1250 214413489 214413517
    0x804032607050d0b04021306081e010303050c0a050604030c12020d050306040f09021201050618040302030a0c060f06031226180a0c030b160c021503061513030302070b0f 74
    0x40303d5005a950400b1036101c0c00a40115030341c8070751060005002000d4011000415650f02c04184482070360a404000c220070b0146980c0c4590940e90121155440900207262038490b5004c8040810418094540994841d40300c2c4041c00c02c02e407420039500d03007031100c0190540d0400094036101740d40140440750b014804440008103410119a6140140b49040001c0d42103800c250b101382030f4032170550010340218012500307d00b1400358100aa01a020100e5006005800038018601d1150142c02c21a00b01841158041603284000d01c2210444140d030340140d910f0b500c0706180c0c1c284c2c10b402c0500c1e05003601038403110484620340e19295480c8a8805008a1580103150445056050040c460000c400764000c483c0610550b4a040082003044180e031485501032540481842540c00782144030501e0b0740c01307084c14440c1e41417107480c070f14580c100904440e0881e5900c40f640c0d0301046001c00500a1000e0301c2d180b13081b21411418000d2414103260000c0c044480100404242d881040f001d684501030304800c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 214415989 1250 214414739 214414747
    0xa17060303070c0e0a0b060703050f07060b06070606050f01020118020d020102031312110907020c0f19030302010f0f0903051b0705060708090f2413030b0403080403260705 75
    0x109140d03105903180038103025030f8601d0100e402030110340101d0045507500c4050010030085010448244a400e500601180c0b00300850180104030402030118540103000008000c602d000c041000c4c0d80c06038030116005996204144801d203007107004c48410031800e1000300800550381b4000b032441031a2000291065101201003801c680c170800c00c5448007000d0801e40c02a40c0d5444a01e804c3d06982d03050203e50001244960802a0501041052113401b1540c000d0140c0e0340c0b140144945440124551900300303d00c00745405586110005010040d4465800010a103d400120100712110301d103020341303010308028404004c60742c403c00351282e04007440407640d480c03490032103418a0202c40358001d0350030110204551051194550152640000a0321180780451241040024a4a06208080c00205415138101443c40306038050800c01903103850741c0035102d403252903c0150700400c40c0e04030f00240c41c0e50200b00415901544802e245106000b10042d10046a0642071122900030200810420f000c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 214417239 1250 214415989 214416001
    0xa031502190f020f0a11010c06060506031f0803070b06010f03060305071203030509010e19030201060806010b03160203030105010503070305041e060c0905010203030903090904080d020c010b0108060103020a17 91
    0x581110702070800c0e40048180c20100c0c80c0c1c050400c1c1c403240465000360241c0e59000300450408188000c805510901588092410070019a0386007030201003620700719582c4501051584614000311300508001c440d090503042001001020641990018422078106010600029840206407a04a5002d00744a00b0601c0311000450091615601c060003910030500c001070f011070450b40210001c2e000341d034184082e988803500325080c0d800900c00b2a60580c0311a80c90f141403040080110307500c900c00d02c00410b40503521040d262800e5420303004a00401d8001051000032a10078041a500d00a1070020314119031400d4006005030200801480a01d52101c2c0085e080003030307944040d00302c59074803d00b540c1c01440e1070914000400400e5801c20100796556070104040d0f0000041d01d208914450003946040201c405202003cbc0001d0b00848440606200100c4600d16a00151000c420036200000d4031059200c001445114080c081c241030510401041c0107041c3c1c400400c8010940090070b12503a52904 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 214418489 1250 214417239 214417241
    0x43e0d02030c1215010e011106041e0b1609050d050304050123070311060604060302090115020f03041e090204030201080a05040c08010f0b10020c0102070314071517150a0315 76
    0x4800983c05540c901000029880320150720807001081e82e40c0c40c02401d05000641da2801d09801e0307101c032680310400003000120340c1c2e2002c20104030381070b100f000f450015a4580355800020f1ba681c0e101140038400408104c1c1e800203240c0000c1c00201c640d100102460784485482c0d00c658002d140c100322011a00440c80048040080d8050346c10000080e0303907141c83c1c20001d004000904100311180034500105010740381500880c03082d02d070000d040d5504d5034070344815200340e0103042005034154003448400305080b0341e040c000341c00242a1464106856008040f61015442d000c0d040465410310600c000d0000d81d0340411147d0344980700c128000351580f0f45050007410783d41e00b9030210700a0340c244621000044013540080501c3d4a007640d03041c0d500d00e84008182e88411601d10700d140183d024420400206060400135030a401110003a1001d803600c070f600c070511500c2c408040d4004103040ea551041d8025541e42600e51101c0002519801c0c603040328005007410030b09100280407206208490b503040c1c24a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 214419739 1250 214418489 214418497
    0x1061103090607150e010209060406030b2b0c15140a0e1005040f09050c09090403030b19080c03060402031b010509090108060118090807120509043e0d02030c 69
    0x2d0189480321014500410358080c544000c10b400740c02c01c19514034510050090f034540380303c0107185a0130039042c200e04500901c641a003150780219140c042140102d0400481564081e40007a525028501420129015000355011101c1d240310380c0d603024461a40000880684c000100c0695980d03034101d10300301d402d09005c820350b903400000f0070381040600350050010411107680e43c0011400f03030b039a0f823480c504403402280c066100c110308001d40c2c441841e0688070168458440d0a00055400c0750a012508036003050b41c4c034229030740e450f1105004480d020003d140000c04102c00078080c51600741c2c00300351a100d95a40c05034154002c0300d000c24150780601c058510480c000380c665200f642c1d49008240c0d0340d42d800c1c85000101001318011440700080d9016840000303402200462a000540e59440d181c082001900b404201082c0a0001d603a6030f2402800300682604480f0070040d2400801010941458500d584606245024051031044c0100a548102582003801070300d07a1303600e0600c0455846 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 214420989 1250 214419739 214419757
    0xf0206010b07032607021204080604020d1e1101270e150904120906020303041a100302060c06060f0609030a170c0d02070801060902040b1c02090607060902100201050f01061103 77
    0x5000c3c0c44008014450313641c128030500141e401ca403c185000103690045101d20b00821106400c00000a005400c10302d008024161241d003142c810070b40c0e6010404ca40140040c0125185500b6002c80b010640c1e1020900042811564500c021800d10403545003e000c003d106482c2a1602c440025200c3c40402c1c0d5054000980584904a1031030546010001804403851a0001c540255404659070384000190781c8036a0344541c034842106084400e4048070301c001801000c1c128260741c000320040e2942c40c048c102602007031009115900308601000341400b04003030441d020f1441484030040343c0c0d40000e0320030040750700402c24120304030036010307140c0244c031440c11440a948500070a548406900148000840da034400080000700d84074214101a0700c284c0c450100304ca001807080782005501d0a801c00e00c00d4040c0400107285c5103d46001c41d1807500f1100007074920942d10442842075060403559a83c0515461008004518000c1d01e111f00281060282408014910100e040c01030801c02c12111040c4c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 214422239 1250 214420989 214421027
    0x12041506080d020a020420030103140a0c06050c010506030c010e06030402030c0a0602060106110109020f091e0109020702130b0303041e03020d080309010b040e12070318030614070f0206010b0703 85
    0xc800b40c40007030b40e50a10200105c0c000c0e4504418903001c0d444a441c2d4482000403c03c200d46180d10b140c9541c0076445260400b68201d0007407005c500002540061060024125078135000d07203a2101d8100a82140e000500e101d001e500700300081800b580c0c0c0311048001c1500211581522601d40d800801d00e45400c0304006234116041181c00700c1c985030006a00c504807030300e5542e04a42c070140d4005450031f8078890034000303420a1252440000c9032401038a80d0386d10100840000c03440c00c00401c6000016942a0b000010340d03540016040c0641c100308110100303845030810305100c0c03801410b011070b507a44603030b100c3c03114402c0c00070380317188001c2000c2c0d400300b401150001c050703400d40d01050902e60001da100340c81d5000c5542c41c2420071480d40c20140615a000b001c4080a4003110105281c110f4152384079440440800042810a9508051805104019600072240003545000c0b070403905056034800b030003401c1444803100e41e14020303a50006041d419160000c0400d82ca555039880e06a40b003100880e1040300003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 214423489 1250 214422239 214422253
    0x806011a19080f0709141219120e04180b07021203040606050907020c0a03060b0f130f0b01050414010302090f060a0201090507050109030b011a1e04050f061204150608 73
    0x116400520039005035051100f40c04952144007083d03c0c2c0c075078a8828a200c00c00d1140c011441d91814040180b924000300080d04e80c7d009000d039000644d110f19140032500c20b505a0121840960312994248120307000b0385003000341c8140c000c1404101ea00d0000b0050000c01c121000a540030710178000c44200b01030600c8015240d05180c40c0c054090309030707401228010030076031000650741440095500a0308002402e1614924115181c0714003a140f6078602d170360881144040582c082d21140014642d024001000003803a40030500d820701990407190340a030410205200520141c3c10074030912059800c2401c0060799100d140c40840c0a0001070130405a00c080042010078200b5019000b00381168820b030140d80c0c42c20385910040d682610300c0d020142c103840f805001444400641e12010405c0c00000d46250700741b00c40e01c1510aa01110219400003104001c502044079060a1103007240c40b0741c0c1100c04a092080c81802489000d9009001420510441064004003549980200d015110160076522a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 214424739 1250 214423489 214423537
    0x2100302070c170613080a0c050c1c050c0906061206180114010e12030d090f0f080a0315060f0815060c01061805070801170102040b030a06030510060806011a 69
    0x21100354028048003400b5100009107024005c030305190b21075902c043d40c2c07410080c40400840394000040f00485841c4521085031403143e9611103140e40c2000c143c65844062a098540541402c400c02c0890740640c20040a100050b503c2200fa10714941c44001c5005155403480001076400107205d1090f0b400d0b9040c40000303c0d0239002c0040c0281150800c3e03c071024010720072001c1c014100070b6100b01e941190424400514500a2034000303411007030040000905802998848880c259011b5070200c1d5540c170700150142005401d030061400c1c4420b000c40280c11705140c2400603003010201001e03081005001c1e00090724403e41e12420801c2c0d03040182c0302ca501c841c2e403910700034000e00180c02240f05460480342842140b100c00d00031540700f0700701c980c0c441c0c015900c1c0420b103003040b462160070465155000d00000c5000040742e0040e43c0720310240c40c0b021400d6495410000d08040050183c00c0059040c10003d100d01c54002980604480005441c9001c1c20040c2100142c180208800e401e406079007481d490038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 214425989 1250 214424739 214424759
    0x60c150204140315040b010902131e1d040f241406040f15090905100903020105070e060c07060e04140103080304031b030801050603130209040f0b0a020c060402100302070c 75
    0x802e500150b08980c0442541540c074890342a0464004144000c14401400041c01e10b802800703060800d0000c00d0f654585038094a2816480400e0041c00c15401c90003c006005450580e4510348103051000e403440c0c1080c1c1c44000d100c0c015840040c10104014824441da14644035424a42882c42c40301040703180340d440310f098505803060b83c08500c070b1800c001d000c101284062094100a00032180c800e00344916092040029044800c030640303c0707003e03507005802522090b000700008140700303900014091910040140010312600190b46c0900810b0142852203031002503000c06540c142d09000300e2451070078001801608038140a1841c000100000008101011000e540038901c02e80324070307c4000d01440c42c0711005041e000042c000600c210b004000300d0034040011608024644284200c401e030b15000b0030b02c14078040d581222a104911b100100748654591a242c01c50340b042d80035490003841a016982d264400f40c00030b4403a04804c006100328500035030450751a0750b03204501c510300c5503a441c9614 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 214427239 1250 214425989 214426019
    0xc0b0316020f010c0c02102a0b010b0c15061207140301051501050a0c061506020a03030c02030a0c0201120e061303300209030c1c110901030507060c150204 68
    0x34015100c1c0c48a50b0145180c11300800790f94902ca952180e02038100d44c1c08101040c0340b1000c6000910005018446004c2085011410316031100c40c01040c0014592428104468050b4080e02c20520144038500203801c01141607182140035101070a81500d9100004a414007440c0c1910040d02c25600c0008000202039400380d10014110000c012640d50703031504a02c04d0f070344c5680d46400504100700111ba518000e400c40b04440c0e024210000342c22ba0582041c0808100c50380111001da48184880700806626005284000ea0720384041e40c02c2040e5031304090000d0105001c000d050100c96100c40040c8225a44008000301c081800c80700a0b00b09400d000340701c01d90020701a00015031600d4000107002000055154440003001c00300c804071000c1840c80000d420409099915000d070000fa5042540c0d017200520400485135204200401c0c1403811006604285200d01e00850b0355100400c003141012902d80f089910905000307841c174585141c2120380100c2c13140400e6144d44041404228000711104403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 214428489 1250 214427239 214427281
    0x10614030109050915131e0b0117030f0a0905102c040b0307090c17220809040c03230402060a050708040f06020c132c120f030a050609040312090c0b03 66
    0x201d4010600552920036450040c00580748032490b2004200c00c0c00c15450f01402290790a02fa039040101c0b031250b54441d580051275610000c0c0c6040f9007404a4075080138810400401800c082e54042c0c2140350a0180751200550216050480c1d580e90000c1e46460f040318401c0000101550195622104044c000f4158a891080050f564a0758800c00c0f4041c005410701407007040080306100079140c44a040c000001290485142905108120349600c40b4001c4e44808071250310302081c203180070100301403040702442d50204020408010f120258841c6802c45400100300c0c0b6045542e07a24905288011b0b10640d030180f55402504c01c000a00a9404140b040342e4540848040347c0461072401c0e22000d440004990481e900e05913044403481d888000b0b03201220040c01d605480d9a103e8140f80b0750082c0d04401c2e004040c9400000401c0101151481090b60044080710300340c3e150305107514010014401c0c01080003c965440708040f05101c486d0038980e0041486080043c1c0d2440d040d181031489070030060715 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 214429739 1250 214428489 214428503
    0x705060106030b030a050a06090807051005010e100e0c090a150f02370c080d02010e0c09090d030902041b020c040510181d011b020601061403010905091513 68
    0x1014485113008030b4048550750b0010010003a0b64002e03182c140c01051140001c03900040104000000070794140400c5407400d402c190000350640c5000543c1c500c040000f050a6003942d015882480304c0c2c14035200b100d8114840250007608c0f003044c1804180f25103919001888501030740203545031441d0b8005288000c0d1046542074650003031f180c0058a06190052403001031a40c1c03014100c0c01c0c032240e4841400d403800c2c003507958565550750310b004943c1884da10b4029600180d444501e03a010002007046107248100b4195100c038590700d031100800c1e884040321081c410815468840150540d91140c0080710507050725a10031905044014003e5a50041045824019820400051155505204003104a401c1c03c41026980f07004000d4400060580c1000601c0c1c10752440344080c0004030034441c042c00a08000020b01c881d400c1d800300a850040168454010010b440c01102c20000444007034a045408817500414a0b480e5615114100101c0651311256800850104082e81061142000710305004040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 214430989 1250 214429739 214429751
    0x803011a040f03030f032c0f03040609050907020a15021209070509061302160503040501140a020a06181505060a17030f0703090812041d0601092702070506010603 71
    0x420040a00035449111000422040b00b080864007030584882483c3c0340385000511200c60b0304500c20f4601075200c002c412090705c001241d0305890200501c00c0b0065100d40213500b41403070314800508504050040900881607500461a2039000304140038183da804001108640000789011000790414861007e080301c0c1030020038001140071501400b600c00103003102406035120b034240710b10380c5041c501c0700c0507040c0c2c00c000540480c1c40550040c1001d5124a0145035294648400100019a171900c100e000c030700200030b1036502c04d0b00010403c1d0255408800410484189105d15902c00e24048018150306061384980750f10015690000784120021119400055141e80d8518000b040460070409503a004104203411500703621b0103403401c98800e103405c51041d0b84500780c1905048910b0080c0c81c4916002c1401e00192522400e1403443d0208001071280610b040b40008140810303a21411800c6242a9004500c841a100390b0b4006480141410b40d554070540c0750007603603400309101c0c00d400603103011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 214432239 1250 214430989 214431029
    0xb06010e27160f080403030b060403021905030c0105180904060e10051801060305060f1503030a080a050109050408030f0a0609062d050105030a0203090a0609050a0606050105040b0703080c070f080301 87
    0x4406503184040ca607070f13000c106550303a55040d0010100401090340c415001e002c000010f903100b0f042c0c0f00454a1714000c10092900c0c3c141414540104080d419044c85418031019800d00300300c10000c03404e100111281c06284d2680c0c280718000b40394181050f2064092030321010351010306500242d006201040300340700584e44121a032400c039851404010016007103407010540300782d000711900e43c01c4064030018408407007404d1b0001c0c0c61640181c0084011652410801c1a82801486103900600704800f050003989025907503200680302c028000b6804801110124007650b01c9a4000c0303018003054079080200da40c0710141c0442c1403841e10b8034040951014034030241c0d03180040c4020400c480060311064115204e40c42c00c24041d400041171f5084e517104801e541d0f0086007a03130041d0111075001e000034041d041d00a050640c00c3d92643e41100d13050040c01c2104014004031042114803031a01481d2510260310303000032001452180d0040580802c0d0300e40d5000b4103100c4207100450480d43c8101221000d58485 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 214433489 1250 214432239 214432247
    0x108030307050a080415020304050a0b0c0307090b0c1006080a0b15090c070807020406032114030612190b07020f010c02070605030a2d060b070b06010e2716 68
    0x1196684005001030000c0483d45011340800d03600148148034013243d20300d40d04c82c0d02c0201c0e00300311802d80d01648400c003184140508101016001110407542914510300f043c00030748002c481b442030a08192001420300410102407241d06034440c0240c000b4048159105866607a50b2a801429a000498000415034000b911500da00d0b29010251441d200c55031520714002c055040042c042e5a0308804001050040c1d0f0385115082c00355124002420b001e4091510b800307801c0d40c800d0f0b01d40092010600704141c0c590445003c0e2030340071100b114909510160a4059800c0000c10049031140d010590351410410400401072445220664201c945c03a1450b844000d00780c604104210000d60405142401464030403c0295482101c001001c1444810700f41501401004000380c4006021170a0424104020b24060a4002c200d000040c500301106500c03035044411000e080380b41032007009506150107032074440150900d400d0701c060301c102a803200031841c6030b5548101d070b4400500054125103e002402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 214434739 1250 214433489 214433491
    0x14040203010528080102040e070e01080f04060e0102070602041502150709050d0c23011404030c05040504060603050a050a0203010507110a11120a11130e10050a020d090f050601080303 80
    0x1e000d0071a1002225100700e400c0c1080f191110580b0f1030b103d0114002d1001d00042c030080114491941d207510300350130000d0100e6500c0e079200f410400c04030244035410204040480d0421341042000440403040417a03a030080c8690400100014000715000403403131140b41d4000384c9160241c0035540380690440380e020a00c0b004842c91008078812140910550070301d0501d1032111440b4481e00300b201901d5500c2c0e40c0b803175500c03420310f1a0004a118505641941d10058001c504690707000d03132600b0182981c0e5120144043e03809010301a90380e41c00014184412504800000c541203010341d4180c212a05107940c4030303e0256420f13070003507007030a022400852040200740100c02174500600341042c03080c0d03124031200c00342d190082e034405440c407078100000b2420712506510303500c106c0b295242011617205110100c0501018440303020302e8200c00703181d01000880c800044161801000400c0d50f100c2035000005e003d40d5030707145000c500c0c0c42c000c00700300070344548001c50490041c4111006e50fa61080a181e813440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 214435989 1250 214434739 214434749
    0x50c0a020a06050c1b0307031d010e0d0c0b0318010c0c0206030c07020109030213020a0306080613080a0311070f020102011b05090f011101050901020316020a0c050108070e12071404020301 82
    0x8072003180311011a5031540041d80210310210540d2600e030022005950421581900c5041604005549801c258000c09800e1440c00c403400400c0b1190341c40c3e40040c2030210611069402a244040c1d540c0400000701e881002400c11420f1464480c02c10014100b00544e020f80c0098040d8640001c1c3d00216005a00400406600070110780c907551300e43c000441a81c01c400d904030b0510500d0740f80480169502810031001d030901e2040107894010680000f4251091a4420050ba41140042c00300c550001c1800310311b5581c201d00b17107581e0303148201300c05c90080207060010010b422000c1980d07c1086818800704140034003da0090000101200b070300c00380b01c019a404800480c0082001540a041140040a28034014103149049014681d0f445003503400071220b02d01d83d65400010031080280c0704442d100d510f0310a10041040400c141c0d50070f040c9001d24001d16040c44400c1c2c2c00110340504c129031080a03544094100218045c0241105981c1c034494040c030114500d036200c00c100c160a1074402c0c0d078100d40c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 214437239 1250 214435989 214435993
    0xb0702210f0714100f020309010b040e0705060a1e0c0309140a090506030c1207030b01270f060504140403082a09060919081e030a03051005040c03060504050c0a02 71
    0x804036030380e81d010071000c40608801406034013018154040c07103220b2920400b60245000d80d4a2401c40181800c6808072203400740305524200078030b0600c21b03001890005503a0207880859551640840036079522040142c0c4d00000301c901400d0389a925032010984041c0382c480d4885880a907110114824a10140711101d03130008000d8a0810400384d003a040300d40c0182c1c024080c1c44040c1d40309030201d4001c0c00c0c285030700f46050307203d4141041080200d03002e003401080c4080740c15042100d0758202031112907680c890005142d8698404204d611a00d502280c000c0500801c20803164039a0800302802d41c6c000c903001c0d00482c4031000016140190b1403c08400300240c03480e052511418a050103004d82c0003484403580000c0300b130003800050f0b00d038805040500021040c8801c103140c41c0032419840c0100d001e41c103000c00309040303c0400b0b0181000040e506404081d0501140655039405800c01d0040306901007076000307003064015501c00307405031320110503103205450030711196403105a400905d00c55a1414001a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 214438489 1250 214437239 214437247
    0x5090c041a18210a03050304110102010204060f081e0a090b010b040f09020f1210150302071104090312020a031a04020c070b1c020d14061207120201020a0b0702210f 72
    0x180351905089500383c030594103801505110b0101d69181106218040740030560001c1480284007900d5525804000d003403000f03614041c14070800400010b034400305201400307244004145003400c1d000d12040050080c031300e00140d038a0070710300c0e180190480c0788007035405800300000440c0d03c0082c042110150389807094221641031400861800a51061500d104140e100b4003031820004501454240281c3c1030080050056040c41c00d1443d20b4140810746805041c41008904c00041008a9040c810b0713000f250001000341c0281010707074031181031604542e02ca900c00a494084641c01d0751041c03507808070844070b51001c2c2c14208103220891060f000007840c240c0c0b000b401040480041801480c451402c041000d00014000741c966040c0e07040303104074143c8640c5401c04001415460109280d000d80102c40350b00d00121030307204041e10b801c03260151003100e54a90b2140c4065900170420403c0741c9034032052880c198608848002c1d00c0b2503007441500070303003000304001c0d0601029140c10b40b00c031065540d100c2d91030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 214439739 1250 214438489 214438537
    0x1209020a1a0f040807050312040311060a030207152708030a0b061605030729012d0e1e15010e0103060305010504051b0a080601090b040605090c041a 65
    0x250010704014031040381d604024030700800d16180060030040140c0c8004148103824401050706014a42c911440540401d00082011070522000c091140f001079079115642d11402c0e004a01038440c200c0c000c0d01c4d10401284980c00281c1c29403101c0720504110201c58050f010042c2410b0038848c068402908110051001c2107409403168400046404018021443c1c08022061781c820100501015148c07904007044080c140600d09103448551784d203065000011032082c01c031002a50358180182c0c0e1400c0038001008581c41d01c035076a074006c402501c04c85041c405036541c034030081000382210491956000980e40b98141403c04100c680590b55003181c0091141184e001100c800307080380035107810103459500010116000384602030055010324064201300c4000e004212002e24500c034158010030204004201d9880f01007952419500112408a04d030341e003940000d800ba09047c1c0100e03a00000c0d01d0103001c840d010000051040743d003614410700181d00341555420003802607805900b12600061b0078946 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 214440989 1250 214439739 214439759
    0x90111120a0e0706020105010303140304080d09030e04020f0304020a0605071a09070e010303050310080d0c060f0207050d020d020606060910081f06020706030b030a05070509220b04031209020a 84
    0x2610410403403001940c00c004902c401d261242c55807000d00540d6641d4014000d065024a070881451480c030482d03407540c00d0590301d00c94244500c45150b00c0c80b1707a0f03604118040502c43d403840714610400801c25910356003003542504440d07205840c100d1041c00c2c521b0002512a000b6002d071141d6a400c41210b8100c40450641e06204200c020100d020a004480f0041414a48901103034081c40c0661f48542d181d150411402d00b0b41d0302960031541095008240d401c80d299030003903030110b98990020002c100f102e401e00604008c0c0c000c083d0010135a00131400c6425900d0740c001144096000b05038210740c011785540c01030021510500075001d81014107681110303c20b50080c2e00890300012251907004440080da04000d01210003500320b8401600100320030412103615014001c5296011405007042400300d9031440d070745e140603204641c019088440081c2c0c0340e50081300d00200d00071452000c1228030305e03a403401c0c4c03c0301c40301140e046020400392480404e01100e1886800502a4003401c031103806800c1020b407203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 214442239 1250 214440989 214440991
    0x105040b030709030b15010e150a200d0507031409060f09191401090605190c021f03050403080a0e0607030e0f01110417060c03070e0103020c03031503010509011112 72
    0x42c051010300740c4008009201c1042c55841115080c10300e4030310380d035444c00061070f00344442e4000d4440c20401c03041d22000d40b80f0204560803000d460501e80d100700e00c1114106a01200d840e02242c0d580269044c0c2000d045d045001445a00c0c82580c407000c90000f8403001c91034500424851941208052049102d8611210010504154018000e80662081c05c0c1d07003007240325981c2c0011403003041e00c000d5041c00d5604125101d01a110354101941043c051514500c4844840d00c40d900c10400d00951200c15900c0e11010300c0c0c11070080c812047c603150f00022003e0050842a103003100000c40c101c1c0003c01c81b800501c40d82644003903c501030240ca848030141100541103e8119440500074101116500c540900c02d140c500b40c008440e00b42c40d14030f02846210410b0702c3c000402e03110f401900401903c000c6030b90031289e00107028109272007210034060040b40207010701c00410010344000801c0c0400018650741a41c0e6802c401c03402400199910b103079043c283d501032501d803e1103c00078000d410399500d40800907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 214443489 1250 214442239 214442251
    0x50c0c04022a07080609151308072a1205150705040b0a2607022e061205010b010905180c09220e07050604030201050703030e0d050c0115050105040b03 66
    0x585400c01480450740416240a00010b003540c0c0101410401c0f1041400110fa000c1d4505002d00910004482c008178502c00003402c0302c011042142e000c0b030801451000780d840642d00308000c807030004181d800842c540c240070040d121440080340c80c0050f800ca2190340380a80b0941c04809000f1100840d00c2c0801100c0f006000c41c014030109000100b4850490f40260207070030034944d1102150054040303040c2c41c1c03410345856088848090760030440c40a800140b00702548099248919100020b0100d814541e0481c20914460701d0070507800003080050320810b5401d40c1d00039002005000c00820040d02c6512035489001d4000030955071541180c041561415880b0020045031480c0000303000014010400100303403107207a000c2002d843d585030401c620840e12144d81000041030210304200003d0020b0045d848028100080011080c0030940f19401144e038803e02081241c042000d00640a88950000301001c8460340ca0300480150340740c3d50440c190101c40d8180c40b081e00e090304024000c2190f03030000b002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 214444739 1250 214443489 214443517
    0xc130506131107020120060c0304051501060806090f15130906020703030903090b0a0504030f0203031314040c08100626010f090b040902010e010513050312040f06050c0c0402 76
    0x1090707580680340108101c0d032040794580c5541e4249132001418032140d4201c0c20f07018100701e680803061440006000c0390418005507581c1e03201d6071985002450425800c141c1c0056852400c0002066038202d20581d0103a01d0403500c220560303441d0010030031407080c1210102200d0f5445c049100150811018110400ca00c1d248080340c40512901c403501a40e0001038100c000a646182c00c1c4140759000b00850050a44890303500d147c2142c48800911a005500019002c1d8205005410071581c0c204122103002e00d140d45100e04055590032040081e01c01411058050b904101901000c5485802094030440041004800d050700301a012981b902c140e4500c8050303040084405002e92000c0c5c4c60040c02131040c8000341c1c10403410601d44800359801030361401e01442c141104040142c0e0006100ca45100007072800039120103130b48040481050541e803016406016810020350603083ca40b0003481681d40e80d58159628a82d00c2c00111110702c00e640460314160440c1450b54001d2406400030303d640c542e1120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 214445989 1250 214444739 214444759
    0x60109060e0307230f0d0b0a020d0609140613020403020114030702010212010e090c0105030610210e2404020a030311070515120f07050706200c15090c130506 69
    0x341600135155410407069500201c80341040302e86051a0f01190b060400d8a083e607002609590f00c4011b030401810b14918607401140c00340b401c0d2403507070040e0002e18003220306210340d8a80c10300b02e8107465000d5405500403000191540c643c051a4000c450031640d040e900d034001c00c0c800d00e4142c40e80b030304054000800c554013003001524610012948038040c015800724860300e401c124041c98038280c0c00c206103d043c800c0c28800c00c01c1660303812140c0c075640b0000b400c00741562010410342e8611905001c0e45031142c00c1c60400c450b05803403030010381d0404183c055400c1c000c008502a201540e00038044400079400204014144002489030703000c000c0400c4540c08071600da075207903c001a034256509400c0014444046140c1080c1880c01e510a070704524074485000182c14403000003031841c4201c45000d400035444c0d80d0107546408035051141040040c1565050722100081c80b0a510360400148106120180c503001c20843d80c0c0120b840151641d00a1804800c482c0c0d040d14000a804010600c951020385d0203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 214447239 1250 214445989 214445999
    0x20702060721031401050603040c08070807030b0a150308130e040312050a1103011401020f06010306090c0f0602060601081e070203030910021312021c0803060405010e060109060e0307 80
    0xc0203041110700c10514030411a080000300c400c50410245603030101424000b0300c4091048100030f0b9410b503807041d42ca483c0e03269a1030410301c3c524049980400554411303000001403030f000c007040d91f03810381c0d21a0800600d0307511007043c41c1080e03c4c00302d040f03140d201501c07980400024a03140020301c0603001c8107183d0103c46a031542c7d88094000100ca060707010820b494000801101944602544005441030412581d510a00040b01078001409040c0c0c0084540d250720042d6070080017940b180798201d07022100a5a100e140140142c034000d0350860382e00044117004a00d04800e11400c20549000d980240016612000116407601d005806003402814850365450711004003074200344035682d160011075032810001c00b11441d1918400502418510511000c0c450501a01d218411220900d1001c1965640e07070000510190940c0d4001b4800e95150360071904101016002d1803040c042120104120f0b0390707070260003441d604211480fa00081e080d010521202d40600f044561611000d42100c1102ea262 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 214448489 1250 214447239 214447249
    0x5030304060f09080d050912060f04080c010e1006170607050a08150303030403020a120e031005042a03060f09020f090a0b18040203011527090804090507091a0f0c01020702 75
    0x100d45c14000a00c0020404000c1c2000c510540c8840802c3c8002c00032440d280403a0414100d000d0001001d04c0c4002460121102d000d411001402c40740c0d0081d10345058403100382c103000348498482c1c8800e0815882080d0300c1e00b000825001c0c40303088607884282c506402c01034200c0340b100d00184a201c10b141040100758440c3c600304080e51240744030340c005100880081c1040b4010907420541c0c08104292a886507219480210300525824038070200850303151118604003141000919000480e1908020101c242c403c40344444407c0300d02840c0e040150200c840c0c00f43d001c5e5260902e0280d00881079245254481c103001c100c00b03a0041301c010000604495500014600c04203456555403450000f4040c0400d5141c28401c02240c8400c82003100d2125180c45c888006460795000c0c041e004400e41500c8a0481807070340c02844a4580c003151456a45884d21030340c2d4001c00c03056030401d00150b100d05000c180b0054200c1c07901503848c45c03400d00c5410805ca000301c01c1400e81c0585803a440c555001d100c035030010b03110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 214449739 1250 214448489 214448503
    0x201060b0d0c090b090d020d05010b090c0703080709061b030e10051809041101050c010b180405010b01110318040207170a0f020604120f0e030723060405030304060f0908 74
    0x1c501408290840031280060003407503260072243c0d12400402c186201562450700e20302d80c2a6041d9103040f005401420500e0041000040c01c0d80c1101103c820006003c8583c402044442e03c2034070f460b05151603102088801000d14015503000c40e00340c60000070303418611103103103214500c40e140500c642d02610010900c030400008489000c108007154844501c0c10b03a500350582d50005a601030034030b00d00381e120400c401010341c40043c1401400200751654240c29001107a80c040050f04804079940b08c4882060001c00840f000d4850f5480d2201110081d84910f500340c0754103203100b0055003043c5041e110403590703c103405003181d40b143e400c101076000941445c2100c08a091151012030b282c2c2c0d4031007005401e2100650181c42103401c04410440000c104030038000b403031259442d140424a0700603009076051541040940d40c140300d986000503600d554070300000201c041052a40001d1403100042c0049402340c0d00440b030741500148024404136200b1100b40c94100303030a161409100b66105105420055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 214450989 1250 214449739 214449757
    0xf120d020615090606040905090304081c1704030c06151206090506090303010f1211041a19050112200d0204060207060e0603070807030e0706021f0603031e0201060b 72
    0x818000c000352003a40c1c02e4400100c01058030400c24519242c070015000344902e000302c81440e5981e0010031000e050810556000d8044507003114a80000c032100051590541814140010420036003200d08104081b0464019903150b141c0080c242c0301a0340b81d0f00170b440700e41c8241035955040d120006a01c8045008014102d000b8080046c01020300e041941c02c110005202c942390703038001c00040044c540d900c140d090031a01c42400c000902c06841ca480004e2104410b00316034008d04120b401c03200356070002c261980d220350441c0c0e0000665002d0710503006803560b501ca414042003810781e1082075503141c2c2c2c0011410052808183e1300d181c95064a2604a03006070508510345540490140010b5404100500246c203640c141803c03500e01e010001606071100420940070000d0030004989818080e8002d040f0250460095400081d22004000c2d134034201b041c2e40820204000b0032800707052100340702d19020f580c1c041e99001d40512420722802c000c0d03144d9096400c110b640c1e4000000342000c001014001d442 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 214452239 1250 214450989 214450993
    0x20060d09060f06120c0f0513091a070e0906040506031906091e03030605010207180c020c1f080f22080d06090c110c0f0f040605040e0a0b0708040308060f120d02 70
    0x40d038500341714016085030b80101c54030580d203140c02c2c00701d03a4840280c00c8402c0244280401c45010529055004518941e803c0c034200a040083c1700700b02e0b070010860078850350152065015690313410100415243c003520942d4158001c0c030050340c5003404020740c00721454050607000c00c40309416650303401045512002e800c7d5005032242c64804169060052000429003403004000e03071410071494110020464081141c602e641e83c0c00311079818002d105071410308000030a5160312251280800305c00d199100100d200040f0044005400c1040107901c9500903210160441c50f206962460082074a25070070381a10b001800740f03e00d00a0f900d0900500f4003500c100c40d00031030309815841c0c2c042d002e41000e1440012a4020f00382810311915110b29080324100c0c1160150307640445840800c0042640360050340c0c01c03501782070145204100000340703040814410716121509664091046a003104103540c001c5c00181342c440803036260b2030111143e0101440003005d0030007100c030500c44540340001680b03046000d070b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 214453489 1250 214452239 214452269
    0x30304060b10030b06040b0714010e03091504030807080c070b07060c030c081905060a030c0e060a0e09060f1b030411091b1902010b0a080a20060d09060f06 68
    0xd00302903040c8429402c050400344115100c0310005101070045028081c0c826001044500500c09000241001c0c8507903680204500301158010756180c0d80721a050600603007004a0704040301002c0000c880440341c010746c204e070500a0596648403142c0c04040360080720320620501050341450f04006000c414414500003400611300c1201409a134002039801d81884190820800001c031a1440448007160075400050640d8511000405881e010340018005001e001c0c1d000c12004a156010f41c01130b10200c0380c04c0b21840d950020341404d6001190a240650401d00104890307800400e805074014000f80d642114002400c850780c1c2164004032030560f000300303540d075040c640703400c100d005141c01a83e49110110f40c0203c41d02650700c0b52003001c44015000d244190401600c0d4400c1d40051080f2800501c800c6a01e9681c0340002d68805d04e40c401541c0202074500820306544184403009010300c4094078107410a51004144030050081400540c1c0039500e41c00c3c200d07607400c0c884c4502000391500310001452 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 214454739 1250 214453489 214453511
    0xc0c0203010c090602071518060306091107021c021203120f01082109210303060a06030c020a030c0c0801090309060210020a090b030a1103090a11030a2301060b0a050a020c0301050105101206050303030406 89
    0x15541e00041c6a03710403410815040942c84508124039424000071511805040d03520104500e800b442003002942e00010070703580942000c0d440c1c8580180c64102c0201e0f0700c3e0f40c0f02d10f165500c40020190800802042205603c0300c0046003028200c2210004d01c2c0d03410790381c0818030030700c24580424103a641a401c0082001404d1402201c60b10240c241c9140800c80d0b01041140a0341d035032b1b443c071006405d12030000d92340327000c001c04c03881071070042e280c0f0030024882d05680e442c0280c4540590301420f0054019000307c8540b042c0540700752814840b1560700c1848092508170402e40715031001d802d00140340c0e02c9250780c0c04070505a60055005500074401405440c1140c28600b46080d58021007600c03c0d0441c101610114603c1c0f00c0b01c68060b00b101c5800250800101040340c010652036101e03020114010441c210700503080030151140424135000d6900500d28081054200c801c02d008107030388510400190b0329a90300c140c48101001e180003200050058440300040d2664008840440b620741d1101001c0803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 214455989 1250 214454739 214454741
    0x18080a0f1a0103151a0f040f0f02160b010e040206030a0e010917040f0e0f010b0307020f0f01140108011e0b010302090a08060a061203050301050d02040f0c0c0203010c09060207151806030609 83
    0x50400c0800d5410152040d00c200003d0085c0e0181b84040e100d40c0e11100d0711201d00b00380340c0c009207641c49810002c658820740b90241c941e4a400c0c0ca903065460200312000003402c2c1d2020310645200d41da00501e003528690b036a1565000034680e440c0703101c58941d070300c03000400024031440381c90034150410107100d5240da15200251030709482c15000072402d43c0815040c803504001100e50f040c1555100d00300c032034490b0b0350440101e1070300442c018100386522a83c0c049001c0028194001c59140000826402d0706a8076800c3c010f0a03180319401c1d04514040c12001000c1244035075000e40e8140c901450007601d071244120005250042a42200e48035402420600c2025003041c03040310018160020808445801614064150b00052180b40d0160b100302c0380f0082159180d5000c0300c000e49102100b007201d804050350090050710802d404034060340c6021255500d55004402000440d961680140f000c1820048104046a2040300c10b1090104070300c04100c401070000d4442d0090520303507600203a400c1c6410713201c0b8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 214457239 1250 214455989 214456001
    0xb090601091a0402092b0501140c0703030b0f030706171b070b04260304060f02040f21050706020a110619110a080f0a18080a0f1a010315 60
    0x8201e02d041241c840b0810380c00c0480510001c1103600688407150000403404c11400082e040541501d843c080101440c0100040103649000d80d000b04065075518030072502055050701e4178030001c002070064a000038032a810940d100c01000d004601c036800040d011034603184458109a0104103075841c1640c0e4024a11007440d80310030391030f61201b01134829503450380f110b01ca9000c000d820b80081200041c188054000c4207a4110301101c50710482c03903100090003603140c2080d2800c4540d1420610b000200c540b0600035503080e00d01070000054420b150180003440322544d0314112001d92a0000d1309400f01740c0034014400242080c2e00900352502e03081c5460449100f0300e990543c0301d50014844041021205c8010024010003814224001c0035611000ea10700041034000400d000c80004d15600740e2040700c2c014202d00c50341c2d0b4031a50311070003550b10004108103950284105942c4001d010a000c00d0a21005d110f0343e078001d81c4c100700d419540c03030b2004018440c240c00a40f41000070b69040100241c40b032240c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 214458489 1250 214457239 214457249
    0x100e0a020d18020a0b03151c05011a0f100314100608100b0a050c0a05070b04090b03070810111b0309090a0e1e0114010f030b0105030a120503070c0503070b090601 71
    0x5542000e0b030350025948810310301a030b044540700480000d1481c581d1002c084d580c3c4130014481111142e0410311207080109a04c3c0c126155400c000190103085440740341d0720b501e008000d00c0410b400c2c129006000ca88491502010100350715207481c00c625030250011140207102400c5071841c4c0314141300024140410251195800788e40030442000400300e500c0a541c48d0019a01e1f0050342c40414421551a05510300340c090098060884006840755061009104486803404140001d104c2c4008040c3c5902c100c0c40341300d0300c5400c2900c1d00e0300340c1d5a0355800302c1031403170144001c20708045a1705000c02c1103070382ea0381007643d0507400000c00e0308451070f0079205613a00040c14413060004100324902580c0300d151002c4208a04502480b002e041140c007074000030300c3d022017070300104055a0360b08034001d00d178200c6101c190350b040303919400412070b8280800d803060025000517101c000249502401c8580303600c010900e000f0400145020340004400340001c0542c180980e0317214200f4203142118074208030040c0e101c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 214459739 1250 214458489 214458521
    0x816060c080c121b0309341419090c0e120a020f061e03100e09030429040314070e070c080d0608030403031e0806090f100e0a020d 57
    0x108000c690b035500482d00b003101180c101c0d034866194422112507410b41c0c00302c180a201c5020040100440c070005030404074a440b0864030980f21000d44141d41c14024087e090070260185000520014480c400400039045014109444403262800200d4130386825412104240d5140c403110101183d1040c0c1e011000c44044900214038106069142d0351a030031088001c0c0218902c00101000e03039070b006c003a5240c074070050101134001203c0c000301c46407662085600840c0307840c407120003180c8904403030507482c0b007007240c000110316140c00e101e0100c24945440941080d20803e007541400c2034421a00540004d5226586181480c40603403105403c100154110f500120750000800400a520810b918030740b541028460381c2e6030403030385010401b80000d60424030451000190000c10140e00c52440e1006441b28014400740703401e0000d0844d11104182c0d402c0d41d00802001c04907401365280841242c12405268001e142c1c1d50b034841c2546c100700012a4000b4038181e011400d20400390250103011161504618 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 214460989 1250 214459739 214459741
    0x60a0b09060919051f0801090305030609100909080403230715092411070509061318240504050a0f020d080c07090c030e0c011101090816060c08 63
    0x81400450014241c030300c1203900001041005603400b0500b810080c03881401e000c40d1501c0340889081002c2c2c071122000410038100300041d443c4061050010706513141c0e803407910355113a400400c20842c40141c81c2580102c007420001070040d0302c51040d500464414060a901e0300d00e1800c040710b901400740b440c0315101c80030411901d40310b60041900d0065401404000e008039560900455101c40c00b074101e003010141d02294226180d04400c9140740303242140e540c0030b0311f2118281c1c1d040c1d202e003410310405402000308000304160340341c46d117034904d03031030143c141c000400301000300d2594550307032078030100f0740c2e549980c0100244040f007910340ea400801031030740d82841141065500c80c0d0369071007100c0b00901108040f624000c11959252501040035030440090754131103c01800302d94580e0307500c2c418441030910703112005512a019000c3d0400310300c41c9101803e0302003801c50055400000d100c1d00100503550399000c1d8400101c249004c3c0030b0800e03500040203102e80140c9400001c42c0c3c0b2030000d01c014011400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 214462239 1250 214460989 214461011
    0xe1b07050d0323042402030a1a01050a020d0c0303020c0d0905041d190501110d020c0105060a030209040219081207020301050c040308030103170d0f0504020916140c160b040305060a 79
    0x10f81401d820940c040054000d201c04030403491301800c0040028071920b40000188200f031003568000305540c40300481c860314000300420040d130740e6100305c144902c00f5130000da4003004030f94090301c40e03c203c0c0c500030309002d0300d09240d0850080c10300c01554107400208003d50b0052000d401d080c03050114080c1b15000040802090700d2204c0e0f529081c2112050903c0c400b8211401009401e400200c00f84808014017903c0b0080c0c1d441c880081d401c412031351403d562910001031000c0c41d00c20a0f00044035005842c81d044c1c0c0d22a034090044981a0f038072a40e0352010410f500103148801045241d070904296141540c603000c651040600f03581020300183c80903e42030000307001007100351088904681c0c0c0079800302100480c0400300960f0f03005041580b0341003480c00100c64a1528150402442a4821111098142e076812160764075a000c4d56039500010b5910320410351a251900000c0c90010064401c9075111400d14041c0301105980750028182180d01003010410081d0801407190004420304040c08024410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 214463489 1250 214462239 214462301
    0x60b0a171203220501200a030506151b151306051b0a1d03030307050d050a1b12060312110d0c0809010e01050d0603080a0e060f040e1b07050d03 63
    0x718a200b06440d11500301e80130407209505c42c503803c003800808130500703030b0f240e104003c41600324140c040082800c1100281030f03490320f04002d5084a5a13581e032281401c40c000b4803030311400c220800d207842600c03400c10140d0342d040d0b40507645e51059a8494101c10400102d141c60740075690094442010452000c031922034000c44002658804442c03454502030642074102048030f800e8008a10607050f0000000740015254810014450308000f80e2080c869070b1070318480c6404940d004060200c03418008000000a24800e00b03061480d03851303040001c18541c4c0c90341c072040c07140d0104c01000d2020610848c1402c00c04a004e20a002c100ca49504210f980f001c404c1e200c2d29458802c5884850400407032410007200c0740c1c052400c2e46d4992088181c00c103c0c41f500d07403038100001d510051070782d00841d40c400d8000030985001000c5410780e5081c0c9081d54203151910241000c188800b03010304900c1c0201c1c4444404122041001d07110140c092802003d804a0003030740502111581208110f84000140d008001c2c0851 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 214464739 1250 214463489 214463521
    0x5090604020f030709050c071719110f0106080a03020d020706080615040e0a0b0a1a0f0915030c0d050c0a080708090c130510090209090a0207060b0a171203 68
    0x1a200700740040410302c0020706004403a0880c0140e2442d10080c4030fa5441d4090140c00018814107464800c0c5401808408090155803c039151929001c440d42c41c00e103200d280d103082d0702c40001c0c0031107401c40c0c0e034809035509540c00c07074001006c2d55110b03641e91010705074104240c0030000418001380802c1e5080242c02020200010701c204c0c02404400080144125400101d0703004100e01074071000f450070100a1280035011140e0858822154800041044104540c840300200f014407100d40c50010300210384031098010541940d03002e540740301a00400e210160066202c0d52091018036a1a088240007108440002d0030781e5a00640c01c1c84440c3c4000e400501c0070f9085141c90800e400c4503940d4a507000c0c0760810f500306040d0400709024402c0c20700841604554080d4105c104402c0d00b0640b5580a8001c0340510400c0d203502c800c42d44081070301c1c4c50705035000384240d50281c0004107041c1904030110340441300c02ea203c011034005861803d0001f000038840d1000301809000301905c1c40c10020446011022 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 214465989 1250 214464739 214464743
    0x20c150a050a110a0f0506040c0e06310c09090c031e0e0106050307170601080a03020703031409091602100c120c11070608093a0c050a050c011205090604 67
    0x503c00c0c0392030706a1401c2101c20030440d408401c00201034906d04d40551100401d642c12965000e8280c00410603660484001e40300340b1011b0300800c001c2d80403041880051799100c01c9003841155410f89840c4040c0980503010780c1d44c4050701d40c110020304d420020700440710641100d60406140c112840c8844404400c503e030109001d00011400c000041d808070b005181d6648440d03814811071383d0024600700581203040403001c802c001d651082c0c1c0d840e941c481e12507083d010004c00681081d0024400a0b000c0c00a0442207200c0341c5040341002d99480205070b80203010741d40688052828141441d007564100554040d1000320982801140705001020300f08504001c0703c10845510b80c6040c0102e54801c40106c161103c10100700e5000c41d9840e580581031020548100121b03001d000d0061035090504060341c0804d400702d940d0004071560410307040c00301801020121003040714a10b003101c00700300100300842500f4080c3d0054070000d80e00034005085600c00c0000c50075800e0034002001044040880d41c207520503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 214467239 1250 214465989 214465997
    0x90302030c060304020f12012414010f0215071d0f0f040f020708070b011a070302070306020a09091e0513050616140309070302030c01030509032d0a020c150a050a 71
    0x3484d1440010002c000004000c1e811030754884170000000015004070001c4c10b5144024012142c1a005800040c1100d001d1082030304902c42000382030394420302c1d0281240e552441510044201081e038480e100c5001d40b0f102000600e600c0d620080511441190340b00c40c002140c815403003a0800d80850004c14400c0d030f00c1803099550f2480d00340684446d40481d031509601c94032495848030710345410300c0364480038018495218641305d11070401c804110100c80706e5680503001001c51902d10b07a1014065440310500508021140c40c0026a2021600505070340142e00b042c503194014074804140102d8400425003562602d05802c5900030800c0403c41d05d810039460454654031012544080d0340350300c070402c00076501c1880041088050480402c018080d031b403084069a508413103101c011000e6940960f00219241c00404c60310302c1d00c0052044500c1c419240102e40110450103407003000660304000724000258220000f82c08840c0740013000e01645500c100d4402d4200b011042c8002c08078010801008280 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 214468489 1250 214467239 214467241
    0x3060709060e010f0e04060306050f07050a080a020d0b090103050109050c03010b2101020708040f03030207080a0c1202030a05030d060e010b0a1b0f050a14010e0601080607051c0c020a03020d090302030c0603 90
    0x201344101082000d0721000f0f0b06c00e001c0c4039035034a04400108022101142d60141f5400881d5000f8403038000c4170045a415613800f0380913110700d9001e000940c84a00221441c0303603221401415503c400855030f0085000b0b00000a4400440c01d000d402d1144100c4004d03c280d240103d4000141d46050403404130f0195502c42d840000200b580050080c80380030340107001514081000500039507101e4500c0c054038421741c01e03100020350310122155901284070005202c00702801c400d1000700a603007a01c0401c10700080450380c0c81d03c1c40741c0390300741940e000c00031092145441c1c039000d0103803113200d940280c01084222156840d0414080d4020603078a0303000c10100c000c2802000d5241803120071107029620315042000c1e91000407062804441e40c0b0020818001e441d400d03e02140072815010490a040300d070310304003030207850740da2500131111507201c417511a0380004400b0741917901d20340324490034071400d9642e0014030240020381806031034420001000320030800e81d050107000580f40400c03080580da00a80d40701c0c0d00d0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 214469739 1250 214468489 214468517
    0x1101021e0c01051821090303040807083c011407080105011d030604030e0a03050d0c0c090207110609011101060806070206060d030e060d090f061d01060b040e0603010603020d1103060709060e01 84
    0x5621400b0174087c5d00d48030204000c201c036030010488400700c422400c00c07195001020100b40202285450b03245618000c43c5040320103410026031b030300504128407400042c011890200c0c0c4525175070155020340000340c8070001031210b0f50304041110140603c0d02c1910042d0003d0200283d90341e0f1009100404110690200140b581c0ba2054042c2c0910340c003000b5580c4488c02014000d040d403004a8094039804d60054000850442507c00c490b56946c1000c4001150036155060200c0c0b80e00601c0c08904000d20618000074040c002e124180c0a0007440002d007400c0d04101c1402450480c010b80000c6c400c2254208610009801480a034285002504d0150311445043c540d10010300c690007024003040d800071112000c00032540c0c4407030312141c020402440034801c4001e00e03600b2600c0c14007441c0c40d404410007043c0b1201c40b40002c804e0781714a0060002c106182c4aa01042ca20500c01c032040364911850042816036160071720002da44505581303001607840f4a050710041043c00c4013014a414030414940794030f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 214470989 1250 214469739 214469803
    0x60702031f050a050105150d0c090504020c0c100807170912040303121b0c020103110417070303140909060d020301200a020c0402070308071101021e0c010518 69
    0x4400001c14880980d000300005500c1c018040c22950901d0051802d400800c0c2454130513410b40c10342001c03034941410484140a070360b000741001c4829906202c021800040c180e60b0358002070081c420381c00041e24080015a040c0004a0b120140d4807050140060410014543c444486070804945024520068552440460400f805013810074941440041c002c02856002003031203000c690b04010801040c141c809814806080084019000500c070141c144003540c826040600301007500d0070340340d20f440c0d07580e031800b00000c4080031003181035001000104140b6812180c1080140c1811060700e140032803582c0010710345c0c0c05c0205027501c40d0f4485811003055442c25072000d541103031120802c0000d81e00c80c0420124035040020121f00612410a10505604090003558544c0c0d5140d1141410b40c0c0742c0352001d40e08155070100c40d03402507509204044400c208050340c002d182c1c1401d94a0fa640c0e00c44519400e0a5a8000300a014020004c549000041100141c00540002c60910607a022085071015035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 214472239 1250 214470989 214471003
    0x2d09020906061e07030309020306090706091a041e060f0518010311070b1017030408060109020a02340503010905070b0a0c0b0c1207110606010c2117010609031106070203 74
    0x3d404580c0d42c0400d90568400702c03c6a00890440388295100c040b17490340d030001d9010b02000200155800c0100801c0ca6018046246854010702e003002d0300c4204001e001c0d00020401604001d60380b01c20041d0580044003202c450706c0c245081d03071400b000c48aa02c00396150440c0e03560304055880aa281d0304107980c2091b904420b078000d030000c519040044c010307860105036016006c040c1d0000003420394040c0000080b1411614080081c1102da803801200900139004024907900790301881c04603481440741c1f481041d0111080202040040001d01c50400c4a689107811881c000da250101920204e070000442d5400c0303607184080540e840c203010320f044840424a080041c54142c080041c010f90321200d0002c0c104401407a220b100496844a0040340c1020b03c40503160055040701c4045103d9502c9240201030241c0100940c02802c13800d02ca202c140d0001c2d2040074800900502c1c1000345c500d2101d10200c0c0100000c2c81c00045250942d140d11f018496101e00c46441402d001600c2021900c0c1400780e8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 214473489 1250 214472239 214472287
    0x4090602030f01080f010213090903050906070501060602100b03030316030e0f06042001080103110105040b0f0702030f120a030203040c0806010305031305011d0108192d0902090606 79
    0x355201d0030040c0705125a62400e01800300c4e80d01510b99109021401442503980650315108280541842d100146008011605054040017410401e803e5203485d03010041840320b1280d0000a007051615400a0818480c0c841c03800401e4184110440d0990f000800c1d00d40229040e0781c015042d00d003201c070503002808408448a014016894450300906003c2800d910850080114080100420051102c03603c0c2c4400d60a0206440100600c0803030010203410080701c106043c06480c05455000910064112003c044603440d4000b50700d01c11030400b80000900515090001e001160441d8038408050041030303131100c10168088001030601400c204040c0c003d1038408107940c803950310390401c0c9459502c40c5d4042c3c5945003000d880000c4a51007510259010000c400d40e8400302140e1100446880d00040c20480640a8180028410b038030703d031040c0003801015080105001c800c1c062f000010b000c6840e2031080c071503c1c010b8104090b0f100c0074041580140301711903081d5039101020004040210780410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 214474739 1250 214473489 214473491
    0x60b03071502010e190b0f07110106170f061b0d02040b0a0504171c031a15190809120a020a0c030c03060608030306010c080c01110d1401050102070f05010c02040906 72
    0x244010711034040d80a40c80700d403220000d032241d00d901c040c041c0104480c00c1400401d8a041c0c1c5000940c03402c1c40c141c4070780c0c00501501d02400380c0c01e80348440d2425180306401000104905c40f9107100d204004206080002d40c4100180030289800e8080b11000f042c0820300c4207a00000094020b990030f13180d81100c003d44605078019442e0303007480600411a030054004d0300200030046812100c40400015170701038461200b08080e051000d070300400c4002d00101a20110442c01040f140380d820750b503109001e59103800d44042546c80f0700c00f640304c01d54020140c098043c18004440103010040001184540c03007120300c4580240d0b40c04844008a00e00382840002802d10031310404007100300200706000c0000c4078000c04081c0501da40310f00e007141d181d00c8207907034003404103100314107840019414070058030f41c99080710300010b2121340c40c000103070466000080c4da1000c0c681d036204510070f90301c0310f011a50140c1028801007c207942487c24070b045254543c054141842202854001151344175003003620700340d5200c44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 214475989 1250 214474739 214474769
    0x31107081306080903071203090f02120d03151d09070f0b0a140906030f0406110409050405010509010b03030f03090102040f1401110d0c0f0204060504050712050105060313060b0307 79
    0x1840000302420b4028100040d02c0b40000c26410f810000548030f1054100c151000703200100744055008000c140400c6a15001c240c03c4c000c003583e11a071410a10304841000ba02d910101ea54004003110b80c2000d101070700301e0b0f03c14020b000540707456884d000764810742901140c25131500042e4510f800860303800020305491007100814042c06060203000c41d4040e68030f40e200440c0090480f0741076802036007480d83d0400c1043c03002030482139018030b045800c6402900001001da503240c00c030394280e41c840c7d00000c03071050302d90080c88104030f802d20503943d100392140001c00c00710600c84002a22031044c4000610030b80804404907504010a6044500810000c00c1c40b440340ca56a4650074400300d046d40b030150104264030745480703603a4000710f0280b405075010b50f6800e052251940c0c0f80c8024840c406000d0340c003c0c0c0d4414020840743c82d5885080e024842a44a049040342c07940c50ba0800d03160b0581007036000d51018000c0c40300c0401094940e40006502420116900300319a002c00e142c484142d2250590b080d01c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 214477239 1250 214475989 214476007
    0x4031e02061614030301060e100917070f05060c0705060a030204080610031505100b0f091309021e0105030703020702010c0b040615290c030d050901020a26060103110708 74
    0x18141c00401da00c5242d03d500411000d0b40c005449000900c140c401141c40980c0ca9500d41c41d105007020f42c0f402c070360304107000229110a8600803c0018400004155002080a12030700e41e9100c0c18100038003089800a01e00440d081d10992524103d1040034003139400070402544072400703070b019039000d0a4401c04517035403480c0216038100c000a4a1205079244408a078048003400145e010b403a1082c0b020107580c0c2d581600c5c02600544650084080b052948824803650b003c0341d4805d05d010084094000313001c0740140c42401000400e604507000100c02a00c45030b0200314590b004070959078013003894140180c554890f400142c540724106000180a9120b4001f0001000840e41c0280f00d1900080c0d581d0780da0f81d454192004514000d200c05880340d81d080d1011040002404004042940810b400e03603081600804d138203c180d40c0c0a4602004503500416001503150340700f00300c652042c41c0714400d591070195101420201c0080506001e042580b0f40f145155400c040ba002ca40c0800d40c8458010303580e070856 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 214478489 1250 214477239 214477267
    0x150f070309080337020d0806030312180d0801060e060d0906020a03051f0305151b0a090302040b0a0e0604050406020c03070302060610050712050a020111040e060a06030203090304031e0206 82
    0x1c0213442c0c044d07010822150542c144c04160180c13200c15002800000d42050050318600300080c07000d42e25200400801400d098482c40d8103015204000c645210808013209003170820800034050420071042100400c0f081d58440c405201d91101903842c1552010481c01c010007908100002401d03090000542c0c1c404168107a0140740318215407000607204911038440d00c48010354a1202406642c01840e1a0300d011511558080d08030404000d149950200030140d90b0003030308074190550100380a45401c1003581414002e150f0b410341d00320303801d16003582440007003a901e444c0a4042ca0042d503079280002d0810131250b04503410040c1c00f00c1160788490142c030707000b99140d44c01c540c581d020302205443c51100f14000d000356850700794000300e00300c0010075000c400c0341d894212501c018119920f5503400b400e401810001000584800144640686081030912410509a03440401014070401c1007080b00c1001101366004d032036103c014020544103200c86942542221900070b0750200c07000031405100100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 214479739 1250 214478489 214478527
    0x804090515090430020c130917030405070e0c0406030915020d1e0504110603090c1003140603060114010518090a154b0f060e150f0703090803 62
    0x204828503500802c049503134000e504464007021001d03038012014918245000e000a10840d010200d0004080c281c42d110500d4080686088039a842d10000910051240074050300c0007400d000300a084040c1400900906140300e1445003904269485000100b040004096003050b500300140c107640b28141410b60038001d00703d541c1c4908582581803003003501441207004451281d50415680504000c42d0700a20560307501c000c2c9001480d0240c140b0340102a0754003c0c2c0e48811a40700d65001559500c0180040c0d000e0308007030517542c840c4d84284010080070000ca525040054000e1a04940350111003946048805008049550000c2d608003082031a040d1a400a50300c00c4596041c802c903141e59115081c02000c0c1d40102c1d82c5021203041c14540f030442c8880c190a5201c0480d47c1d00e2400da000031030f4210803640c1c00d812201d4500e0a1440801403641c2c0200014407a110440780d40c40b0b81400c0d00351103d10780c45205030025580201145003000e02d4091100f5034001e080420680e50355100381100040c1500e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 214480989 1250 214479739 214479773
    0x50d1e06050405040c0603090c09050109150e150411040506030c0c0105071706040902010912120212090916020c0d03020c18060d02010c050f0a060603021c08040905150904 75
    0x880c1800004452429009860095410940080d40c103410943c046001e8200c01c0c400307032626542008001a203605c14400e450003884405030014003a260640c00c1841041c840d8000422481c8050038060380b40c00c5480c091a41c03200c11900083c0049008044601c0d070300895010030b0740170f64080108091481c110000700030700c2c4000130003046140d4800d0025109002c9040d04180704010307040c0002c19034201588480540d5005040040d081d0760b44e809140c8500c14660703400c82e02180b0b01040760800d00e80404c0307145a058002c80060782000e04810100c0ca40603c010440240c0c2c0b15800c0c04446041d0090000c2204020041c0840604081e5410081d40d600040721209008004210300c0402680b815502103000e9040200200041501c58004642481b8110810b96071400303101c204001e152070170003003c18600d11440300860100d00e90b0040055907580c0081241d40b10b8604001c3c0700004840341d0480301980c2202600140320b4440c5400444406034001d50242c1000707080c4180300c00e1000d03075100b02d00804 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 214482239 1250 214480989 214480991
    0x210a0804030213141f05040f02090f040b010e040b04060b030103030807020708011a062215080112020d120c050106090e0c010201090203030406031a04050403111501081c050d1e 77
    0x40c002d4030004221920903c040f907404000e07001196030a000c002d11000702d40002c4542e078174440d4031000001c040707070031111140c01c81d10340c00286500e040c1441400030300d030341c941100d042080d40460000600000c018101480c8126513034040d003521a40e032503000d80e014201113012203803690385034500600002e2055414202600c90048005507500741406030310882c01c04076803210b640038a0201844941d800c038507507000002c040b004403800c0d400e8160002e40000c1c203030b83c00314400301040e07a440a030804a040c2c00030072000011601040160f2a90000c12043d50351140066409503801c40d402c440f00b55433080010000c1d4207080001134101c1c4142c020110544208017a1180601084016400c84440050094040d001448104441400b952115007100351103040f414903208030f0b02c00101103032800c880407004900300c00307000d0781c6890b810800b9100200100c0000c12031941040c26840c2d03030b600c08010075a5120344482c2841c514034400d1050f105d000103820410311812098100689030788000410b114070403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 214483489 1250 214482239 214482259
    0x40e0403110703050c010f110615010905030a02150304030c14060105120303070818010f0f020301080606090c070b13060e0a0b09070308030609130b040506040c15020606210a08040302 80
    0x901c00200d40601100c0c0c1c088001c040100780000103407100310f040c4141d0710600000e2000c2056200342803000601c100d600c0303002e0b001c51814490001d04941825000349000354000e918840c01621160600504420070211854495030703149404c580e001c3c00010010804041c402c2100340703c40340090014141c800440700b0104130420707051020f40d00c1c00100d4850001078082000310b442140c0c8001811403060340180040341404400100c50160b170a1124544030095002004000002d414440035070800c6c001c07102c1e5050303418400c041c3c0301540110f01020307204104110102e418400d8000502455652154040c4480000c0e2200283c8403441c1c4075080e0ae060700f224000410a01c000704286050b203500c03003541c0d41107841d4041400a4068024200342c0445014002c4c0c0c0e01103074840d004140b2a61141c00244078518181c6407076000941c00d58445103d8006408140d0420742d00462000e501080555107031441c139441660550510010340c000c990b03a406988060028000100002c1051300d0080c0c801c003c00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 214484739 1250 214483489 214483517
    0x70b011a0903030a0c0201140c07090606030905120d020417060a0605040c1706150705030c0d0302160602031302100c031d010f1103070803070e040e0f06010504020c07030503040e0403 80
    0x85105a03860160305400c04c0015000d02d80c02107040c09030f000d0061410b01d900c41c8a100c05083c0d660b1005200580c240d00034178003085811030b1405084050310301413805020540c45aa0f580381e81d01141c0d60500102e41e004070f01c0400310306881d41650001c00e206132080c41415020034206440350425110201030500f0185c0204180c20180552001d08000b0b0b030302c807081450840540c615589000d0041c5034410041e20381c80b80100340b075002406280b40542c02459885100198041c034004e80300c0001c9051600500200c01d158490342e5004800a4000c98050398aa442d1040b80520070a1258000d41c003c2510b0400a81e02c3d40c85100313007021901c43d869040d01100c0000b814000500d01303000850000d180c0038511000c491040d84480c00c1c1c000711000312410501e440c2da611582c0c1c2c000711b03888400106c109080b0300c494035140c0150079480b07203014003810358039040c2481c4c41c1d00e5031014001c0354010b580001c0c48500b240d03002c2140e84001e40c2c005050b01c1d1110f4403200010f085040076501600001c0c0c10540c44e00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 214485989 1250 214484739 214484789
    0x50102010c0905150c010906020309030301051207060917010b0a0906050f0a030c090902030f030307030b010f0302070b0c130806010306020702120601060203070611040503190302071d190e03070b01 86
    0x82500c4000301113848403008103801108a510144a6040c155210502c090010300c40d03001540c05200200c014584079070604050151078a6504211440340e8400c840070459541c000b51000d0955035251802448080f2230600b55014014500c019900540481c600041804240c0d01c20300a69004031060b1110507110810040b18281e10700020340b0000e081d24041010440a80c0b007440858405001d0f41d100007d9000700c14103540080700d020009c20384503450449036691000c0035032040d510605003141041007a440c1e00f100507000404030100b900c00003d81d115541d101d20290707001402420121a0710350385900c0c1460282d0441e05080b40180207040c8405448080850b0712416541c0550086040a0480d142d0201614250482000c00301e0104404100e0303840a0000314111100030703150b10380c05074030b81c90000d183c642aa4001e16880101002c4c420020900c0d00031260000341c12007071103200c024401d02030070041090101000d052310000501800300007100c074005040350080030055420070b61b545d4180b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 214487239 1250 214485989 214486007
    0x90115080c1305100b0409020309010c0f0c021e0402070302010b0307050105040312030b0607020405180f0309010c0201050d0e03040f0f050901030308060415182405030a020d050c06030a06050102010c 87
    0x15800000b1540602080c80b2960155600400704582e150801d0313074030389481040d90702540158015540020070407007503440034010740000400b14078060711a101703107820081040c032410800a01c41c0d1100507090b0350400c3d500d0080c8105a100510843d0346680600e0003074028612071036618068040c2c04000121580140140e0342141d401407248101e4124002080b0004c0c1074140c4020740c400000c0c00b050001d40c03942e2080074490040340620036840312944101514114800040401990040024800603684600880365090b42030030510b448144031000d0350302030151000b070b17145244000b05002038600d44881100c012200324004074003000c1e0322001404001042404013a000ca600d03480800ca990816500010021200022100626491302004000d1840f0302000a10071511816171444c003d00040c051411491400c18174001c2c6450080840c0d1215104e90001c0c0c0718200200d451000c0c4041403110920200313008020f142c1c4c91909020482c014880b030f00619005620304800d403400310f801180c4070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 214488489 1250 214487239 214487263
    0x11030a05070605030a06030c0605071a010302130c03020702090a05070807020f070b0706020705070f18050105180702100c050703031a030606120708060a060305060709120303050703110309011508 85
    0x50415282850b1050701c0c3d941c07001d04034040003650341c0000000728a160381100c1c003070000c40d55402c1c0d840c905420081c851308400c0599100c0300e0100c000420041e91080b800071030126440d11b02190000c00c2e03000c20b500078000c000c03000e03400101410030030400c484540d0005100d100c464a03111155100d81c03004903a10585c6c0020001241c0c41084117000300c010040280c5001c900ca540007500e425803076a21181428441c5d032200da08848070007003d00c152880348a1800c031f4520891002c01035585018000b40e0100b1000c12074481481c1c054004c21034452003489840c94409403c18240080018110003c3c400ea20180041d40081c6c50071032050000381410008682d031181c002e0060449480343c00030000720400301e90b45031000342305512001a2006050180d10300c2050040e00000b007042ca1401c1c02070030404001c0907030f0208901ea1000b80194a030203141d15200d02d4051400040c80c1c3da036200140c005001c5078140d480340d00008820840c10000541115514801c041d140c41030780fa0380c900d4602e80e907900d680c410b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 214489739 1250 214488489 214488493
    0xc031406090d0512060d0218011a070b061009080a03050a0e102f01060902090a050406060207120501110f0903010c020c0a060c0c0504020309100c0e0603010e13021201060311030a05 79
    0x4203601c0d0030f00114100c1d00810014100a046c1c2e800d540054940d0289a0306503103400160700040080d08030351040e40d1018200f100340203250110740e6640d0500424028002c030303c1114041c0d000541c2d944910320443c060884002218100c842d03505010b050350304038130401c100192241340c40e41040c0c102003c5100000841740c070b4a40303000642014060f0440440b20a14075110b100351074100141c082406858010f0102d07010050380e40c180f00e418088001140e0700624059400c1080c104501580001c3d46000c5030040400d040d0011640d00c0c0003409499075141281d0309030b402054040a001c2d0340380c0100a407001c11030080185c280d24650590711164040c089550040d90040100300d0b050040c580c00c103081e8880d018440e6003a4131440000c04a030002c3c1c6030803180340c0c8084011401d038540d82c803d00c41207180da8201503640c01c0103080040d0082c84140142000250803001003807121000c080c4500702164001e0240204880c1a5403060003131001d0302c070581d01070182d10f11440d900d08000c140031480c2504440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 214490989 1250 214489739 214489747
    0xe0a14010b030a15061701080102030c0a0f0302040506070c18090302030a0f021c081f0e0c0a020a020d060f1401050904060203090f15070f18050f0307030c031406090d05 74
    0x10245815030402030084420304d0b124244149620304000d2160080c00d1591520380c1341c3c4845c40001c00782c1c210140c000f50504c2e131042003400b40703590150054900d0b0039000e01d0804c5944105c08003c9001e4090b5a128641055001c07811408102600c411036013a0f440845400401c10202695030094809000010300503800c1041081c4441d48103400465094034030f0b0040704c2484100c08100d040c1614440c64403000102500c1c00e01603075514614481102800441c058089241030040340c0c009000081c12503940e0481c0005c01c01240360091021403505074005118003030b004090300f00b50001d46102c001c0c010525107484010003059180103c0c1c141a220b0180501c00141d0300c680d9410003d50000d00881e40074840c840c80c000403818200300d000c0c0340f91407030040c54100307091a102c050700041415066800b8065050f15011441c00072000400840e2021120010f558402d400403e0410805400c0030b0140200010084203210060321615481c01410040f1406541c4143c001501c03140c0b09000400090000c04c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 214492239 1250 214490989 214490999
    0x80c070312051e0f0105101106070810091a03010c110303060909010e031603170705031b090a06020304082112062e020601050307120318030c0b040e0a1401 68
    0x540542c1d4002d41500f400c1c65500442200640c0301c01c02102c500c858440b40e2801030055090180030650446101c2c00e1428000440503656500d52400600000400650400003000f141e891002c2c40c00402e03800e04c0c20007210044d035140001318501c001c1454000c0d030174004013907030f003a01c6540050707440340d07050700030754199180d032002c1184001024044442940d01d60340c0c4498030003010700081c4003140d030f0000502020201d40c54050049140d25444032005000c0c2e07410410155005800c0741e900600c2c014105401010380691030b1614010149000e4111002e040003283c0f0b290004010819591408120317285905104150b031040001c10540705c3c2502d405000081d0051081003a01c0c4d0002c6000300f4081d5541c00d2280c142d0900c8005200d9a41c07002c0f0140c6902c032000b030301401111302508042d0064010903090400c100c0b0f1024601a00a04001d0841c9002091502e9948120081c0d54880a100c24083d81c0d1100298540c00034054101e103d04601c0200b02031203540d00c01c82c40c022204070140300440c0e10341 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 214493489 1250 214492239 214492241
    0x4021b06091f0e0c090f01090f020403030c0609020a150c0b10080c100306090c170a0506090718032901060305010f05220e0601090608030c0316051009050c01080c070312 74
    0xca111480c2e52103521800c82e0a0b42d500c1d1701140c443d0488080d044803661414040310143c07000d00c0600000140704110600110f9070111316030303d64541040f40840c0700f403035a1000c00c9a92009510819103d100600c8004000d0707400325861a2040c041d204001d1591070711044607289139039610401140ba80301004000c62818940468841c4e41211300340001d416540714400d905544402c0c12030400941080c07081004142c10412a43c0c2000d4840010440b5260200106015010103030103c000d01424142e0040d025000d403040318065680314540c1d1010384003c2d181466441c4280214445a111301c0001103559442481040d048800800340000b8607403030300e0203000042c1d4901400301d01241d03442001482c98a414050f51865051280051400307601d4050544210346a640209501d50004c115040c02c00e8400405e0715040030740359881a40092461500c140745c82c0300ea05000d003540e07040020720018000049600348a15a0a80301c98815594a00251150b48101d980050114840c0394000b101d6803c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 214494739 1250 214493489 214493501
    0x2090414011a0a031e080414040c08091b0a03140f010605090405100507030e0105041b06020c010905040b030c030d02030a020d080402031b030f0307050604050705040b060706020304080904021b06091f 87
    0x16117084c0d50280c11482d2a000100e9209404c02c030070340008071400382c071242410b1083c0707584c90700203145c102c0841c2031201682c4d4441107007210618071500419403010581d501c0700c403014021036004228640c0715010a01c000d417654076060b0442007039445d200340014941007036082107110b5035001c1c0150980d02e4540c101d0320000d010240c40c5030201035840110301031240702441503502a6000d5169822100d020b44000503003500303640c0042d01190001c3d040c100c0c40d0b9030012074074000d0340c0c0c08035404140000503102092510012018955051050303020101413250044024620300c0d0450b4265074641c0200072041d285c1a201341c0380250140c0c0032a840d0030044036012486a42098024191441c02010720010713461030f00010010382d000e0b0040b205010030004200400300040030103403824042150f81e200014560b000e8a800074043d40e800100280c1000b03241000c503208850018402c42d101d0320a14906d10702d44030610168122441a000450a200b00000d07800300c12450800f81c0a140d1641101600080c0c42 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 214495989 1250 214494739 214494773
    0x30709031506090603030e0306010902090609040914032701140f0c1203010f0f080a2117010b0306010e0103140a0b030307060203012409150e010c02090414011a0a03 72
    0x19603510080344558603801500015802030366411300c540800781c202350801341c1c1a48101c150324070401c45014039454517802e03100700302d90485001408490b141007541ca2281c01d004014a00d0000154524890018a241030625080c4050503108181d103100151190780280b5140460b81030140450300f01d49110074002c0c080000d180064540a11013402c500c40309800a810240c0d490180c00030034003000009515a070000c0040c6801400110819140d1070203c0c440a001040c5280c00031925080d0180030744003521040303104c007001e00101c1d03035240b40e08840ca410551704580014050960002c0c1c40d03209004000803c4010046403110740c1f40d41050b42c00505a008820340c040c04117106140105900d0300c040e500030103d415160f0540c1c00d4a01c4440b885c0d034800d1140e1801e00503114014040d46551130580c1c0c800c1c80700f90800e0410800070300016101003005190003903200c00c0ca20704210820040840e601c44848601000703201e48040100520744101d01950342c1c0c0d400940d1141c042021031110f04084160607 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 214497239 1250 214495989 214495991
    0x9090606081b0d0c020f0f0105010b0a0f210b04050c090a050906150705250b070b0703020c010f06050108010906081b011e03090506010b03040b06100e03030c060118020307090315 78
    0x100601d50b050313400d210101005600008010204220140322801401c0b9182008028545c1019040744036400b82041810810032004074110000340500c2003a024254100c3d900e492540b440100d0305c9c064808441041c1c0183d081c0000302d00620843e50540e000004018520745050341810140245490010a91503104290611117684080c50300c008040d100d024401412440780381d02246a107550700b44140311000150390301d0400030b50381c2500a40342ea51f98054074212954840481c110040c2c0900b0500c00c2c1c141d4a48500c00107203910642c8813404a071801e0301d41a400b40e90326082c0134102da045200360852504030542a070486806050444918001414400103490f0001400032500c9444140380700482c0ea00e0f4101c40621004200803401814604e00a41c038524059a40c060100d41c0900698040e44009961000603801641c90b40800480501125114000b020009580d001c0030b00ca0442c5100407140000428101d07402140e2113960386844000c2000d1440d503502e11441c820000000d01a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 214498489 1250 214497239 214497247
    0x31415010e1609080c011d10030f0501050a030503070803090a0210020a110f031015030b090a051216060e0f031804050c18101107031112060610053709090606081b 71
    0x9503480300d4107405c1400956400144114ac50300c8000100c079010f0300301520824003840c080000950010407207021702d0b13020284948980385c6940741c600c2c00503c3c0394001e602551120611001990020303014844501a81c070701c2c501c0c1410503080c0003a404101c13090341d030136400261600441e00310781c1e04448202146a040304071099903980f00c400076507009036030f07801550304891200c0c030600800b000b41e00f940d10350300002c4502e0306130f95600d030754071b040d070746540c01400d0545400ca8008158000d02580001480000540365a101c09c0c0b804050032129481d400792086107044045150700407404d00f950903621440c420040d03450364400402c0840300c2c1d0989102d0810107042800d0070001c030140035100045104091468010398400200007214520011003501a444201080307215940c0980c040905050760401e140d96604924404009841c000c40d60f882c00320000c0d40030700355407119010441c005005545d80446040d00c0d481918292100c600c03821002440240c082109121910903451403a45603603545071070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 214499739 1250 214498489 214498547
    0x503090d031106040c2903041401090209090c18010506030c090a031205071505090d1b060608060f0f010e06130e0f06040b090c0307031415010e1609080c01 68
    0xc0e02604071001c175000c0800d01001c20202a1451035080101700c08541302c030f40c0350440400140e96010080c8041d00415030400e800030540400c2d80581440354011b0f048800a03c1c2a0b0410703507403007995044050068001e4800c00ba000c00ca0814960b060322001094079195403105549140c1c00d0300800000c41e0710a04000d070010004a4404850581001544920303840300b1141c104400740c0c0c1400d030400c039400c0303062400b0026008000b00d1802e503640c405041c40401c0800d5610804d058001e45038008090710b1800c1c1001c200c4000000f02c40380b007901c00301640506641e4400110007150001c0c0704001c03800004401041003490305580020034986140b00024504124407001c2e45090501c4c2071595584d0405000d11090042100c0704543c090b100300005e0595042c03030400700b9952860747c40060000c0042c490741c0d8441a6050014050424641c00c40d072140356101d58400c10f00c414140c4608981c1c104030040712100d80d000e03068010446030b5640160081230914801500c50489292a008000404440c01e0070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 214500989 1250 214499739 214499743
    0x10509280f1b020609190f020d11150d1b021506030c090a02030a1d0d0302030a0f05091b0d0209010611070f090209011803051905010605040204030807020415030503090d0311 76
    0x21403400c2d603000303061a081c251201400c14401c0099003200304046030040020561449400d1030b401e50548010103a101ca50401c20308000708441e429038080c0914000006c110344420207028504506441040900c10b0016480420007078585204050b8120030760720080200281180c40e40040013800b6207146403012400a100948204d40003003003141d000c801d001d41881144111201201c41c40640320016040565150f44c40031440c641134101500000041e0b00042150403c0c503030440628402d0069080c07a03543c058070380c0300540c03d081c086002940c00042c07501d804444041c03020f4000e00b19840d43d9003001030403202c4900003907443c44540302c0c050740060f4010300d0306000002032039141380062b21410320100040c00d08500d8160012200c1c0002e00034008248086500407803403035001d401240520b9103140180c050141640659031151010070000f00f8441c0f04401801d180e4400c039000c02c500268001030024488460001500c194401c2c000700340e1604141c000810030500904100040040c08a5102c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 214502239 1250 214500989 214501031
    0x302060f07030e01020606091f0302100201091506050a12030c0c0609050a0803121819060606120923030d060b040801202b0c0305010509280f 62
    0x241118001410000b403580c411090303144540240302400843c10b0280019030303072400c0903050f14407c1000d55120160358194141000041d9030240c407047c4100910f2070080c1c02000f010805617019403000c0740d404000d9035684165010ba40004002c000c1c428203144040c1108105400300700c007030080c40c01408001c504c00e5040d1100400c0d45540300804a403c0000f80b0440903110703802408254010710006070160403004210b0f07442024100e0b00004081c50303c031404c0c6480da6000d1554941c1c0000140c0a080c0601c9800c00e1003668040c2d101c8501d440908507544040b00c41d070b000054001503000e0380c0c80704080000412010714420f80030880b424500300b40e01610440f5540d0b409810f4494000808204400d0280a1810540d12090034421041c0c80b221a030711b070034451088891490031850721b144880c14040f20000170048480301d002c101c0182005006001800203010b840c0c4200400d00020714459a12200315040c550f41d5001c050f400e1840c801000060603d0306a85154140c444085c80351070040c40c0640c0e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 214503489 1250 214502239 214502257
    0x2103080a270203190b040b0c0403120504060813031706040b040608030343090b0307031a06040b120c04080312041505060906090405070504022208032d04030206 70
    0x1218a0a1481050b24003000507104c0c4036280c1c400103801c00810000700c00030764015040b8143c41d80ca5030741c9164091580c400d981004102d18501c45065580d26807200140060f01c8440d1141e05594840b25031140c2d00450550000340010101c00d00c01d500781031421201c03504880003810110f405200000041c0035550700348c02c64200ea80c00802044411210b918600e0b01d0042c1b1340c21b51141e1007034034910007180401c2c58500f005003072199460b1890010700c80d026407001041120031150f1281400d207002405003001410022840d403154841004614115044504607404001c0051800c05000d04020000d00d000b001281011818400045c2c948800d000030076488080b03420024840c40c00c0d103485203d01c02030503912401580341c6420481c1a84845421540011046503c40510b96582c904a40381403400c0c0c1003a50024008501d184990120320700446582d141c0090707541d1419129564666240504103464a04440c0150791203c00b2500035a4007107610106a0118902600e0ba008241079034014040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 214504739 1250 214503489 214503551
    0x60c0d200f0a140c032101051516050102160201110d050a11010608011a150f040303080c071209080d021203010302010309021302040f030b01051c02010827162103080a 73
    0x2d4144962900804006c0001c130508200a00354144004a5034401050121103000c420014100b001c00c02d407000081822076109000b59a10580705007095584003040c0403c0b40421081548001e101d02e011645040c3c078646940c0c1e242c207100c40c170070b41141c0341640c212032205255654000890a001c081c0506141c0001d02902080003070f240806105a4060190400c0c02c0301006002256400480030101c034201c0b9014500001c043c1c981409110a5124400d4003c01e0700e880080c120340c909070890480b50441d0701100130381e170b410030b140041662280c140003030261014004100600040d80280d01203504180060301002c520542c501162040741d100380c01040315a07540c00c004004002000130b1503400340030305581c000f01ca000003440000d850194810000d041c80b010500081c1d18039541100301d540712001001e2113a000094500c003644414182644103800c071000701740811000c40043d5401040e0403042c00450720f042007078400725034201e80a42950410ba4481340700b8801d000c003a10f8001100892116 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 214505989 1250 214504739 214504747
    0xb12030708030f180c0d020103271202070e0f07110d0306090f1a0420181002060c032410110606040507050d0e030408060c0d200f0a140c03 61
    0xf24400b501c10303005140140700c00c411a40c059a440c40445e00b0742240b201580c039251038004070310041c0d01a1412209172031a580c3d0105241c02016852034448440501506e25815440740c1490202c1c1ca500d00c0c0d00030710046441da41c01040c0b007003150411040c4d22000906e131200038000c901e041e80e82050a050514000651907020030b04c4030010300c0c41124482c009000041054444580a003a801e08403101e00300e1003142c0e40d0300540d0481003552005e24217484810050b50f0713200c84800b400a40c41c43c509100c1c40c081d25600369503400300c500000383d03d03000b2405240c1c054110f55a0ba0300000140c0301c1900100a0610f0300801d01805494503650074116a1540d2100060520314811241c94100000e1405224a050100f4050441e0b04007085404103242607001042041501c0401c0d49580310700d9002d6000f5115400821802038626006441a00b8800340c051000c00244100001500314050910382d40e80000c011012201e058030005001c443c0641c100112840700c042164011368100703020200c1a40c00000e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 214507239 1250 214505989 214506001
    0x10917031b030d0e1509010c1202031302060c15060a03080417010204031a1e0115111923010509060a0902010318030801151d041104030c15030b04020c060a0b1203070803 74
    0x1810301039006210000030001d04104a00041c41d4560409c82685a5503000000c42c0c0301440c101054801e15401912866550800d001100d5842c045c81b244200034003007090101d03000b894501d0b0200301300c0e5000407101e0306090420243d1040c43c19118036041c1e203076508210020004400480714421140c142441e061a460252045204031031084010717070700450502c0042c41000542c0c0c030340e0000480d051030089441c081d050003d40ca070140b404000380c29421004404002c10600c00456a0101c3c40d0b9640440441444c08100e82642c0e0300792015511500100000307011074103e80d01c5044021300514010500c0c2c07180c01245040e40044410660008160300014013294101c45101c413051020392078080d80d000c10b8124070428a440031070b4840c0c0305030749030300424000d204410241d0f805103411030906913905940b000b04c012108101c0c041c540101c2d0070800c0c1c0c1d018926003031003038800900b1204080c01055486803a10350043c094034035032070740c0140501d454120104c81003000c1c0510500c210701c83da903241829 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 214508489 1250 214507239 214507273
    0xf090b0103051302030715050c1209030d020304031e11061204050c0a0501050409090c081009050c010903080702090405030c0115090e030408030733020306010917031b030d0e 76
    0x5008002c026504060f1a005840004401d0100e600f490918248840b0042c01158a44542410303850141700340f281c1c1c0b00340c000080c0014400190210100e8003040e6007000709988038040ea00c03018020303130150380411512600c90700c4120215882558200741c48100c01c000101c0a41101c00482a5200400104410080b00304000320340160104c0e0701c059100d145c000001c0003032245020340b414054464050004012070307903145001404401068a500b84008003c00c001400300b5007064480e4841d03619181050f501412041081d603030054405840c168080c4c082c4020540d01030400c480e2484100050052603000f8400c071754111300c0304105c6c1101d50f8038004c1c1280a030750707190340540050b03001080104021140001200c0400740d010380009401601d545140540c00a90b80980010010105078140c0f4a0410344c0118869102600d0780901c441d210140100d81aa040182521a80c001c200399025a01d200f40a10840c80680c800c03a032030b001e00104000e00f590452946168594458040c0c1c075140708903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 214509739 1250 214508489 214508491
    0xf0a0201151202192102030703050a0813060503101401121508010f180f03140a03020301061b080405040902030c061902100e0303130f0f1407080a050d0e0a0f090b010305 74
    0x8061a4104d41404094800c4200124188180029420f003203011501c0038040f8030001c0d070b0082d040e10990895420040081e43c0420403c015011113414041a5540500141c038010141026406a018245071140c0d61024800103558141b02611a40354200c861901504004406043c1640d141030b00e414007490139940d00d100b0085045042c100014111a4036281a5503040d4212140394101c00d0241401d540410460302201d00c2c070a80011b4291945070150021412103000e561080c850004410303800b1030301720f152103004010880c00c200821851500d40c00036940c1070b0000303050395100165840055496400100314542956545403210f1b03203d901804040500c0d002c000d1f041c002854000f80c119100c2c8001090703541c83c18081038608043c01a503001000700160b2041e003000d4480c12509054420725480390010b4168428090089003241010964040841d40500202044071002d103040d0b4a8580c65a040b83e0070140c80b48000070140d18140142005020741e01000541d014480c00040c19204 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 214510989 1250 214509739 214509769
    0x510050a0c030606050c03070201140c06010605090a090e0d03020a021006090b0906091302060a09050d0c08010e1911011e050702030d08090a23010c1107051002030f0a0201151202 78
    0x5410f009070000501c000c070403101d403239a0900c1c0003034008000701071440d40750203a5201c9581c80e207d0500081b03043c0da0080010141c00300d04032003c0010303598411a08056403131240c050b2900341c00c00202d6001023030107034000d0030150410780182c0c0e02e02c1c2c20048441c0201c642c158000202e00381c0f28900c060030b6090410351142c1020096580001a02c1e1021084081d4110607400030300902c0000340d00040b01d0703c40d03903015014100040c200b141c0100641010155a061b501a46050b07518080d00d03c645444001003461900d8600560814407040ca41c85e070070000c42000445505000c441d2080308902d8a9486148000820a0b102c841c0c85100a0041c10301e410003108181087c0b180000c14015040000254071340026880500d040d02c18844d0004000708a030564001c0d4015824150310442058001e190010791403190b108440d00b250ba982e081110305101c081594005d41c004001c0720700da1103018401014a40320b140004203c0c101240038005820a06038801c0c4800030518503d0401c5144c00407001000ea2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 214512239 1250 214510989 214510997
    0x3190206060a0e0f240901031412190c230f0c01020a0f0605090c04060b070605130b2e090507020c01360e01090605030d0206040b0708040510050a0c030606 68
    0x102d481040c0500d4031380041d12000c00780c42e402440766034210b412041251680d10142443d11296543e1030260307111101c50440111a0080350928203204043c1c00558203400c0510030081030b480060b010a88424402100c00c0e01e002012800302c10661f0040414200c0d1180c1e502c004011040030080f0b42400e10f0010300d903030350440d04407044480c041010007504d04a8150460800565901c40300c401e140b520307500081150b0040d041c0380c80000c5610418020340070701d40c000c180912882d60307501c0740000b220042920003062401a070b80414a0600300d0a0003854102e0002e101c00481d03c05482e0401c409440ca501050f4200e440303200b001001c580c103000035070b0a0ba50030300b0442c03009900c071040110781e05400d4040051501e98070038541d11350408921544c0041c508483d01f12200d50315406038802800040c000c1500074803420074084401da1000500034031841c2c00001d008801e40700c03524202da0107070000d442518940300384109850340040600c25039015800780c400004640240b0403000d425200190b0012040c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 214513489 1250 214512239 214512241
    0x5030612060f0a0c021009080c010e011e200309030301050a240e061309020703090b16030305060f0907020a0302070b04180e01140910060b0c0d0e0303190206060a0e 72
    0x3450202c00b106401286040010075840e2a04008a240030748040c056000c2c4d905090000c1c1c18401c2c91401405280805070007804500500070580f8281c0d840d6100e203e0403040c14401003c160503140e07100c1d1900031041514506071100355045900b4030f4106807903d54840d000040100424a0040f403007100811610340002c070184621280e20000c2d28400d9000001d10001c10701e455000c0c0e558808940300c075000400303600001a00c40302ca540082d00204000c40104c1d90001d03000ca000180c0205070b80354900c1304e40d04524100d900c2d940c00c40140c4009030001350024001c3d504416540c2e14040482c1c0b02d2400781d8000c00303c08605080003480d007075881c2d00100303d90074108824014170b010720510b004004da40342004944120503046003801007421030a445214540c441c1405004080440d60f940c06035110361041c0019030315a0f6001000f0f200b90880131002d544090b800b04003142c05100e8075035001c04000c095a0901c45064900c50b104000c024070036005030450740400070107240411112002d061001740103202 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 214514739 1250 214513489 214513501
    0x10091e080a020123040801090506060f210109060203040f032019020a030602030f2a0702130905060703020c0105150d020919020f0a0e01033308010c0503061206 70
    0x944001e640c010b0304000100000f0b420401408011150514408000c20b9803955150400d500901030a0303000c907441c1c0110f07030106180e8580046040c0c804c00303005041c0480d088040c0d00003020001a000460195500d618a08010520718405948214041c6171003058000b00382c9001412210305190101c480100b01040140e4080b0018081c00f1850b803100d80c108480f039803400019400708650340020140c0b400003040048c59040c1c0520705000b0640b00112441c10000e4121090075092803881a02150307074144800e2001d441c1051070f880c0c10041034640012424065103910303080c0a001c80750040840c2d0001507000c0041400d1182c00c6d48140c106060001c1500040c00241d10280c9054019116020040103e2403a89460200102d0264046c00c11981c810a031042c51885411904260340411031000380900154020f0040c2290038000e0b001501144644002a20022210140502542c2030740d010114220500340f0944181154903103c294807462700302c04110310340780d21040220f215040b01041c004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 214515989 1250 214514739 214514743
    0x4060806041116060e0607020c0909060403020d03241514030103080a0302071a0115080c0c1507020c0306090303181b040209010c02190303020d030c0c020f06040510091e08 75
    0x703400d9075080c0d0f19002104403410311901800c0d61340c3c40403ca80c05001c0501599580000310f200e880c91041d00d82e00b40b03941d181c00d584c0d51511402c071000740260b080a045141424802c1c0e1107407401810b040e0702050482c001c4507a01200142640120030031107001c3e488000c0e025009681ca40d030700e4070061100c17861503040d035a801d1814002e07000c4034000d160300801c00704100b1a0000036400008607003100700c4074641e500c00b0620b100750943e0ba203d00c0441c40c1100880c152000f45400c0b00c044102610050407080e540c03100030035141d03000400e001e0841c024188051000d07a000c0c800710703001b59500e0b07000350740702d007080b54120864000c2802c507182c066000314824a80d140420300141c03807440e0200d90041c2c03650900e40041c0c03014110320400035480b10b0031b040d021907200c82c0c2d00440800d0320f00980c216106092103070001d9088400d07450182d0003062000d6111001032500400503082d1190151050341825641c002103030082480c0b4012501058110200f8001c0c0c0129224242000c400044d82030340d40351400320103070703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 214517239 1250 214515989 214515997
    0xb070201090308070c27060909080a0c0809030304030302070905092410030215030a05070503100302060c0a05010501150e061305130e1e06010e1b0d060b0a05040608060411 75
    0xb0106100411010706100d464682c010003004000b014400c012104600c5404100b00c203a03011b0a00c0b450128041196041b500c61008055805291140b03460310400342694a11001b0200b22a180303800c01c075001c600c0d14288064001181309070010301080381404134440550b900141117980642c40b07034030a07a008042c203c01c0680b468080d09540c1c05039444900c00d001221515070800307508000c0143c0307406500c06a0000851080080810030849a01d44103801c8802c1c0c4400e84010450a1b50000c081c00540784c040018160b580c0d62100710380341002c0b10358900342507035400d911031241041070b9801c8990541c0c001607a901c851f101200c0d00d500d8041414003901c0800c1c0240200380c018540700f520040138000c240d129034203949003481218040050301c0540c00d502207e1140b004038a010384000002e4501c0514070301800b501038078548440024070413041ca800703600103501d940415607d88100047c0554028010605d101143d5103103076660703040c4807021b0311401e4060080740c0141c5c5024801100f00c1d0803d01aa = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 214518489 1250 214517239 214517243
    0x50c07030f05181f021506210102121003050d0512010e090a0b09010618110307140706092609091915090b03010c02060906161b030f090b0702010903 65
    0x865120800f9042564074403d41402541d04201d1070a42440e0740b52a40040c184000101d500f1a080340700d1250070310030304580548881e904817104900f05520700c0c503c1d1003500011f4501074001818505031a00003229044107560b00e40c081203d0100c24418003100340540c0031106040d0a00c82c0c60711084a5010b10700306414845c00203d45204400f04015000901802d594207030401820300075800c1c4410300742e0003003119114030b21140180c4519000111400d001c1d800704120107100b181d096548007a0107550070a5281502120380c3c804001400001d8130a03c03c500c0d101740250f0b894071105e01d440c4400c104001e034040c02c03900048014004440d007996040c05880d40b1556a81c44c1040d26940711080002400025002d0244032000d100e01003503004a960100c50507080c00c4001b4400c1880c801c2c0140d8484200750740032001138210100141182011600716403091001e454101040700503440139071760140d82c900c0100e000812020340c4820703080c0d0295030f80300980090400b103450302030700d980081c1108060b4840 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 214519739 1250 214518489 214518497
    0x10608122d0d0b040c0e0d080d06050d0b061008090a030e04110d0203040c0f0b07110a1205010b040b0306070c03080a0f0e0304030c0b031506031003051006030303050c07030f 76
    0x41c0c2a030094180c045201d144030129041c03511811141007440150071500c0800b8007603460b20301c41900f500d02c122405000000060000030742c0d0300703181c3c8401e44241e0003001e0b022000e540f07840c400511a280d80300300004460195030b440b41e10b41490b40c20426241c0c00d9003680402c00c81c018090003007000c004140426032941c1805e14035032804440c00400d02038035a0421a502d0302401080184004a5071f8004510840c440d0600045642d181c00e400c2007014040c2c00385400081040c4030320000206d61000c401e1090700c008040400043d59030380c038048441607144089070265100e01c0758080c54140360098071360300342c1d00b03c014100c3ca2400c004000c01c03c140d1130b4009420003005101040c0c1c851080d900565042070010f02c14050382501440b81656030b4890711007160341c402400ca000680340c003c10180c901907454252a2820b581c52442040010f800180030218102c840200001c000341c4100549410a0400900460a14a5410b02408603900145010851803042060710006640192000600d6040d428 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 214520989 1250 214519739 214519777
    0x30d1109060f0702130c030e0f010921030204090504080403020103150305030a050a0c0212070e0109020405011407020f040f05060f032b0c12031422060b13090f02010201060812 77
    0x5000c0509640003031501c18900900c01301802c0d8035821011408801c001144c00c603581172124035080380c03480c08003e800f959034100633501e130382c2c09001601d030b10b076115140c09400e02d502d03100258119a002d480445004200180800444d40c15028926001081502e400d210618588076141c0b01d00c251081a01080030006820001500959034a040142c010705070003980401c2d012410f41c1c0e00e03401c1c0284130322035032403500008580c5114022601070700c106075201042181d10310a04d910f03940009100300e0b07200311034060600c4292518840d240b03d000001030003152906280e001e01c1015012030400318002e4000e10f000c010800b01e51a10340714010203103000180f2000d600700c0c049a0b0801b1004009005060b10990180c81c59855000070400c200308009542250321900180d112100000280100c4020f0707070400c100116006600981c0d4560300607105250100c8400b0900c011594174020881d862881d0f90680400e5503030901c140742c080d0000038003c001003d0f00d124510058004c1c00340001d20000c13424 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 214522239 1250 214520989 214520993
    0x5010b1801140c010e0c0102011506090303050714060702010b01030c0e0105030c130e010b0a020c0f030a0b0c040f03240507080c0a0302210a0c1b060e03040302030d02030d1109060f07 80
    0x80031160f10303803450402000949804055192690b0508007028019800c1a03840c0c20780d1300000c0820021240c4039240d51000514541c0c00351503640003114242d031490145009903030500414801d2504c08c041d030b54000189103088500240840c3c0c00040120200300b074204124200b030740c0080850380c00600e560344450f15079034007040e03001401d001c542084080503800000060b021055002501c04c440c50342d001c2d00c0020701061b041c420182700001c080342d810361007200d015011a000d039a166800500c04080c15142c15120380b032030725107030b01035910032a42032940080d51031350300781800c00c6000c1c04411841f0902643c01c104000030b1081901a01c1c140c0702c1103001555015260103541140c22403958100388014034034003e8034100c0d602d03000b11001d214880c18003081184c440c0c407030368840d20040c216841f1402d078190117841d10002000217280c840c8081c40304002c007001503901081600f1282110790300071507840c001b030240e03041596803000c90000b42100a2110f804140e560109aa030300800ca0003449480c1c03440d034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 214523489 1250 214522239 214522277
    0x501140409060914070e151021060f0501090e061518090403080f0f09061807080a08040f080105010609050f040b0d0b1e060901060c03050f0a090905010b1801 69
    0xb400146941c982100344c8480d8940811008204d40c036951900c3c1c9136544840002c481061022203581d800301d68404040300260040b51484e542c400e059502038a0801516404001c8a52076003102100d0102c2c88401c00031503074448800300c0039001001148403181054400704240b40340206002c4480c5101040c0210710a08000c9150b601050042003820b240c102401c015020007000d88151400c410058001584080044a8540246808801804955a040071064025136107000c40c2d94180644c40300000d1781102040340d12080780c014800c1d260f0f0385140481003122042c03d0751141480707904000040140300e40214255003210019901c0032600400d44001900418040551560005c0650304410a00c2494184984a214031206c41c2c0d00804404116184c0502c0846002c1c0d40410600b00503c101840703101d0408200340300c0c1c02e015050210b905e5541030660030900904002443d901c40821109800f070242c54010117031504814941450101140b16a0700c5030105c1505214150000388145101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 214524739 1250 214523489 214523501
    0xc0203091e03212713020c0a080904090503040b09010906172409040318060509221b11060117030703030b0303130b13091b0c020105070b1f0603050114040906 69
    0xc011a0884003900c81814900c0036480d100030103004170000f0030086950b1040e4800c0343c152025403001422086450f96551031141e20920100350051b48480d18440000e1080000e4406400031302041d6450b0110000010301c0b0300050f9100c0000c026403140120701031454003042540110204d40201c80601084c0b402044c2e6035180401c130303600b107915031041105043d0f008105400b41442e007084500800d59900d022105030007a403241035489550641c20800700307a000c206403480320350903900c0420480320151a11000103052610300c0c002c140310920040d840c900500200d405080c40c02c1201c168201c218090b03942c1c0f402040402010305903039090241040d84c040040e50201103046502c03904032a200d005100f40c40d0030010120003074a80d0541c01040808131401415829211400d84811040c0700e64021a42c0311004001681405810000760010070a000c080134413925000b28132520040c440d00144005000c20b074000010180380c0001440502a140030640100344120b50124141007141844001461 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 214525989 1250 214524739 214524757
    0x70302180d030e03100203070e04090606081e0f03040e0f040f0c06020102040e0a0c14031e0c0306030d020a0b070f02070e04050c0915090126010c0203091e0321 70
    0x110164901e000c060740201508201d59041e401e407003074210801030301ca080c0e00040e2451004152040ba4110709400c06a01241540380100004034505555004060404151000e142d039000420207117094110010010241d040920000070361800d0b01e000c0040700d401202602800d101d20655020a051200300243c0908442d0001d00c201e12040da1888064009d5116100c0c400004803c41f00040421519106503008404c0b03c1d290980e00c5e0192280d079900c0ba9000070800c41c0d0f440c00080801c1000031180014921550308402d856a13241407041c1054541800c00900f10b0465111a0a88002895074081d01e50412001e00b040c5840c11400802a42032140c50f81082c0322200c0150100000d100000450108500052b01c80c1d22060b1514041d00041050400d821900842090b0042200740201c160302120440d000710203082d503100660b205c43c01d542110a540300140e00c0440d00118134076000070414850071400075604100790f0080c0100f900c03050383d9002460b031050300c3c641c4c105100030740030110b580d030b00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 214527239 1250 214525989 214525999
    0x2030307111206070f020d09180c1e03090c0801022b090206030903070c2405030703020f0a0c032006040816230d0c031b0203120d0209120c0907030218 66
    0xc5043c800013050701c0d1035a81c0c0403005114410b841d45140313005441e010305480d82c0384c10452030043e11846e80002b8040c0d4031208403c1001d01c40c100306864541c066007040c0c8401c2d40e94080707035849403800c03c503003020956040800c082c0d1040012550b81886060282016001c6058000c4800d282608180c0200b5607554086d42100c0000100042003402100a007841486500740368100340d00c40001442e101d45c54152282c016a4040d8a1280240260080d5030b00c420f6a2030054a0024109103200d000e401144029000c1001c0356001c004041c8c000207810215020b4413055992610006420383c2d1380d407005007002c1d042100004414180307042610140703030115001103c140c0b01810b80e0b445000c481c482c5d035607030380241c1c000c0a0221f45440d21036140451072036010340c1d4114200d07100402948601b507081204a03410b00c1404004650ac409400280603410124000140c6450860007800a10241018102c3c03454020690f00c0345c0035aa82110990891182d00c0e0040e113480401500d20080c01e404444a0340c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 214528489 1250 214527239 214527241
    0x190e060403060f0f11030a1a280e160e030a08040b070b0c0901090e10030b01090209030f0703030912060e06010b0405040b0307061b030201060e09030301060f0c02030307111206 77
    0xb2101c2c1e600b00032241d0882e8081080f50003440341e009003c03640121980c00d840341c0704001107204038065030405038503c1c1e0140e110502131a452800541e40141d400010070841c1c0c289201c030a0000312003030000f00104201c0a03200c010b480c2901004501c2413080e0820401d00c40840c400e0740a030f480401c60584102d9010000d1a40c03503031111030140664000c0310307040394080d0a88000035009151a01501c050070410703120b150205c1c1c1040c00100070044010440c0041407250b01c40000440c0e5500304040c000d00d900000143d40301a85401d141c00e02c40c080c15030301002c4c2e00101040001950006007002128120585a100044940f0740140a401000380c40e0040340709040020845604084c004c00445504903810011403804509040d1101d003103209800101d10000020b82840880544141c0170038440d2000080d181d8440380c0600807980b058a603003500d68004801406265040182158034040b60700380340c0404840c0da4002903130f80c4140c503801800c4207080031102e82c0546130048991107034955202582c500d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 214529739 1250 214528489 214528493
    0x21c0c080d170702030901090302040506010201020d110306030f0304030b011415040306020306090721050c0c010f09170309060c071104020c06060918150601110a0c050108070e06190e060403 83
    0x200082c40c211125624201004100800d0000080b14010401038440051642ca541c080000811000344468190354080014018000c0c5902c6200c074920301c0c2401c00e645a040040a05103400c41030020140240d00400061011407060982141111005119610000c40e08000315040b4214003180543e20503000c10003008100c0c0b240c004e98401e800554405c42ca0b03a854400843d00103114481c504400703c00003655a00c0500540c00c8540e100d0101c0204500c0e0130381007000942150f604407248956156190640403c10980d60b211466500c8141390003825400c0200000392509030240c0810f00c42c0740001080401c0141502c146110598010310454032040b0340c4070000e0300c44508554851062103000000343d100c1440103003400040c965540104202c80361503102d1022601d002d44903505000c6c00050b1013a024204010032011148920008880b062900d00054041100503106005200c0042c011090760748440041d11443c0c0c0141c203c408444440010980e41c0e800351060941e00081d0004000c42 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 214530989 1250 214529739 214529747
    0x90a0c080105011508010b1815040e0906010803191b06092001021c05070812010308041d060907270f0f0b0c0c130e0a030f0806010c021c0c080d 63
    0x2040b9400340580b00d8080c00c0840c0212100e180074001c070010100284805152004100c00c8d006284801402031804161001108481d0f50041d40c480500d1030744407001c00545001c180306c3c2500500d04000218103103e118818010580301681c2c54a04002c032200d0a5900d400ca00e007201d24007542c000700100701031446406c000041040340c14a001014000d9285001594400075041900d60382d5100d1345420329010172402c990a900a51041c1c0d201d030030034401f061014640741185802140b281d020195030740c1c43e10706d2500c0c0c8e481e03004260003010b8402008001551721084c64259010100d07141100070402402501704880540c014203000c0d02c20300082c0450500c0007032001c2e40c150354196402c00803081c1d0300ca44001e164407452a00210640044541d2116814071818a2002d40902000403d9405881c1001454910b6002080e000140048894120300f070700078513420740200d028a4040d001000a4021581c0f04030a034031554802a41d192131003041c800041e465402600c4140261040c18040c40300083c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 214532239 1250 214530989 214530991
    0x42102010807090e01061107030204020f0702090a05040c0302090405010f1b20030406080414030c0c01110303062218051e06100605070602041e030c080d0e09090a0c080105 75
    0x3800700d441032021500309801038600c40200c0b0f910040d0402c0c01c1e8240f903821986004541040115881803681c080b005a40c1d50010300342c8050ba0000031601d0706118010019000000341c04003032498900418000414030385d1744c400b4246c1e50155819841d5454601e000350040040d07184a8540794640711440c5450711412038000c40603c4543d440a443d1030440d0046450940800d1a009065008120400c50303540101071003030340705015180e000154040e60001c541140d0007a04110003e401140c1d144410f50380004000c540504990000c0d411441c00502240305198280c6110020700d110b8140b08254606a030013414485800001507144000345250055580b02c50f603c500050541c1e1704001408001c0025030f86102d4080982003c0c48075141400903651a070140f141a030302d49800f0440880c1e800c041400800070100c607107001085403441c42c140045241d0b000d8201e85026042130400d16000b030781c00030a080c87c884046800c00005d841e82000b172441c00c131340410001c0c4803105003600024001d00650082e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 214533489 1250 214532239 214532243
    0xc221e090501060302090a03020f0319030f020d05090102190212010c030501050405060d0b15131113090213030b0c0c0a03020a150b01050a030509010b09160207090b0120030421 77
    0x14007060b40c880c0c4081d001d90140308512900f100010b10204003501e0110720b01050042c0140c2526001e00300041d00c080d10040c50b0b441640440c602c4140c608079075038100a1290b4125643c68a079080000c00c200007515420700c101d034480b401040c541818290350711002242c2501c9180ba000308040c0841c00c00240141501344a8a0b2050703203014001483c034108402070100e403c0c1c0c0441504543d640729050000c01a0901c140160400d0342601c28a8100700310b4450000b451001c0c00e00261543c1d41c1ca20340440d1260990010700c41540140088014180c41690b41c40640303030700210408207541c4500d0741092038050008843d0740d40c4a61000c050a00d9004542c1261907401800b6890084580106103415a1a03401720507000503400c1050780d010300d1007540304a1b0424080000412503880f84400205628419240d1150540a00411101d1190100040c40040551100c24450b6041c41400a04004441641d007020000c400d041d001955800340100d501802e0342c80304032426000c9140350b01c01000d00407081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 214534739 1250 214533489 214533491
    0xa0f06140312090f06030a0222030209180c130e03120403110703030801030201030e010912180e0c042606040602040f2718050316060b090c221e09 64
    0xb041206150360304031010640d029184804543d022024441a9800105074402c10b80d070a00c1414990360780b011a244011a000242090107411401048841600500328400848800300d5101e6400c002044a800ca0003080f0b4181c100340d00c0141840d0003800d00310300c105000d4040050204c0a4046c5007510a010300e000e591402604400e5139007040d03660115020107070110722028010801984a600040041c1c0851000860300040613910200480305084828010402c2c0030040700c00c0010782c4079440300800121a4111003400c200b45c03029400d00c030350b00846181e104102050f65100148000b6041d40110030f204883c210720b000d003443c100940242c0a6400d844200c0340d000100307000c1c3c14003030344800042d111a050502c078154902b10018100c00b1049114402c003291301402281c41071015045942d060001011100050b01e0003004454003540c00d140b00d018650f0500520060800690344c030882a40d00c14000b007034001e40c0c02c4104801b241d00c40008000405210b02211100d85610011188070142c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 214535989 1250 214534739 214534753
    0x130b1e0603070e040204051e04050703031227080f030703050105180403050d150803071a0708010b030403110c1302070605070306120b100512060114030303040b0c030a0f061403 77
    0x815444040324403030500340c81d03c0e00000c5405072400d41c1c091b80d046102040468141201c0c1001c0090a0341c084809803040e40151800304245504075000c086028200e05041052071500c191000780c44041006000c2d41a146075400e4003001201e100f02c41c1041c5e520402d172516840c240c0001000380c4000d0246500039006a51590828503182c0780903070045515445090401d5000a00b0070000c0c40034149400c41c4240748100051407541c1400109041d5020703001a09004c1014002da0140080141250003000590801041002494005e03660025490726050f144508140c581c1c9280840b100d04d25540b02900403d40c01c0e040403070b81c1c02001014400d41003441682d8680c8016411601c2e60320071031204902100182c0002a8a075945561088920b140d0034440358035000400c2d030135400c41244044503441000103111240d000859811f559504a004628629050b41c520b000305074040c1910b6070304403011001c6035240015401203403024009450401000c3d60f200581d401d1207501c04105406402018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 214537239 1250 214535989 214536001
    0xb032e14030a081b1203010603020717031b0c0c0306010b030403270510031104030602040f0909150f2d06051207060f09090f2003070e0108130b1e 64
    0x1180c0182000e8102c121142400c0d544d015101c14000302140c0d40b0b6113405200300e80b05c003010711040554042c0c1072070350340161102010700d0080d8507142091030420a50310240108042ca2404542411840750b800140c0b5803503405040545181810303403042035605014400c000f040072441030700503500c624029503683c0056004051610064601c007420800e60141c2200d00f4021801d183c1300404620140b40743c0054000024145051240c006070070803904030f130300054100800c181c4010a640a0420803208000500440d82c0c3c03a406400360a1031258510707181c5007560f55407050340e4045131440071540300c651120140090070403892082c0021810350603103401008111810001c2250781d20034140402040c4072401c1140070744581030300290382400c00403481d9000c15480041e0050b1814010b403500301048500e900184642e4000800050b0b42c200441481040011940840c0c5d80c81820400e007420f0f0351a03150a04a805c00c6403050f0801342c610820a0284504008000c0100203400d601d08507007621601e9007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 214538489 1250 214537239 214537243
    0x11031206130b0906010807020a0b0f011703040803030403030b0a0909240b010e060705120a020708060f1e070306150203030402040c02060c070b06040906091406060a0503070b032e1403 80
    0x785040e403c804420300042d0a54043d01e00990807440600444800d50b1680d503a94140c40c2c2c0c01c1340d0582d04600398000400403450b844101d88552440741008d03505150400310801e40c2d901000b00041d0800da100d00c1e41700c80c641c607a04000e0011b407492003820300101159052001280c54500080740701d0072815104110800c0441c0f05840c0c064105a6a68150003a003100300301d0540c020b03950644403405149000440410f0440040a82003030b5034010344100c52a00307024500b0700d10000c04600c1007555020030800031300309003502c00003900026046600c0e141c40b03460742100100541e4101801c0010000c0054490a030000050351099100302d030b091024003000c0380b0480c0c0300d0314141c40e0080300c05800e21680700002c0c3d159200507030203800035000140c01105916010151010031105842200c1e22902a88981d8814010715a11800650b8500c034518078160110350740312120311508003903d40200c01300d4100b01d0505031a400d03030010304003c43d06107000c24031382c4040c6159034440c0c518810038502100e4154100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 214539739 1250 214538489 214538501
    0x1080603010612060902030c042406020106060c0303021b1e1902180405240f0a0504020f010c060204030b0108070807120f02010c050a060c08090c06090d02101103120613 74
    0x300040034008a9507a942c1c440140c17100034412a0705029410304440951290b02c0f40c2c0d800500d00340d440303004850391100000d41d03080064101c48210b90600005004e5140c0040c01c10a2040e418980140e82e115040c54104604c04400140c40241c01964040d44019605030300c160900c58a41098800c2d452104111000811111030002d4014403c9000d0a2000c10484200c5a01c2805402684c0e03100d200002ca10300784444510207004603c01080c1440510544180e545034080d41c40d002c10415400c00f500040e1520754442200c038104007140d4041d204200258040c2c50095500c900070920f42d50f15002413649900b150700a12038188076841e000202c601c001c16483c81c42e560040700d04150900c00307800460b44079482d41020b99142c810740b000740c4c001442070720a000c81d04049030303188900d41c1000c691850420000010441c4503a1040c082d40c84599240c66a07094113070b13170450341c021000d05416801d0360002541ca0341c0f180540404501d0840d11410600b0031072040000b1200c5e000d5102c01d100d1402c04545e8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 214540989 1250 214539739 214539749
    0xf030903060a0b0a080a150501080c01120c0905030102210c031509151207030b0601170c0307020a020319030e150703030e011805010614090f0714091201020702010806030106 76
    0x1000a011519120050f4420195a07001800c0b0b9403d00b80c4510402d481c1c5040503070200d408111004204481c2d181911071540507150720b8020300300c8444918002000240d062a02c1d00509503100032000c2468010301c01d000040001034004c0d07403035103070341c68060550214043c100502c0400c0c040c0000c40034206036089a1003a200e42c10410b600c441030805124220500500048240081c0302079002c40f039940780c8039070100340003501c0200101811440c00580541015000034180102040142c03c2010494400c5902803c0d81e44111307141c1d52941d404a1500d0316803403002e0340600a4180d038a0075040c50a1490058030300a4607103901d004102d8060006019001d411100b100600344007480001c0e00c2608106005000f0754000701e140d4500c010000342c560000d0030b08845076035540707400300300d410040c42202844100444e40075001d454500380260840400030203206c100710481c80f08142c05000300c1c1c181c9480c490302402802c2c0f6a416580581e000b51b00104041c0d02003104c444c0020340d02e1405010302c0064031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 214542239 1250 214540989 214540993
    0x30705010e06190b0d0b0109051006140d0e1c0207060905010804030c0b0402010201090c0b071e0b04120c150606110a02130908090915010f031b0e030a050f0f0f030903 73
    0x340780d030303e0316034020420342420640c071910704900c0c04041001286554085c02003483c2c00541400c00e50300405d94049203600401c18030104030b03442c50300041d40800740e0b00450340e030340e0010a410050b100c01c91304022a4500c1c080c90700c0241c000c0b0710785035070b80082c03440309441d920f448180c04262034200540740395808403001000503d8807032201000400c7d84086940092042c0008110f25840f90344081c211b120302c0c1c0054000007800700d2164103001540c045802c1c00d907801404980c25910549510040500052001d03100c0042140c120000070310030074840d6842900071810009614001c041c050140c8028841c400014080b500000c9451001080d03140c10164020143e80d00301100e00c1c407141c090000c101c0b05907103000d0240300184103504c407040782600c00d08a00c01044016261140058410344104c0c450300c041510300380780b0a0000b95a40c000340035010244c1800118000030782c001901c1c04032041c070018424040e82d21088440400080c081c0f010082e4070013501c4030001d0088641d5503c1c024144102d0381a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 214543489 1250 214542239 214542271
    0x6020a090e10090c230d2d020f270406082e02040308040b09030712050304061b050a031707030903090902030a090210210203040f140c0a0305030705010e06 68
    0x100700c56001c58101c2002c1d050110603018200b00888407501c0614000d0a990340c0006d201d00c0b5061070384039800d94141543e0414911072083c9091220104101c0c0c00c441c001c0340d000401c0201c000c405c10a80344140405882600ad01000080450294040c064254001c9041c070300041034003000070801103040310301490b514400049605503102c0a1041c0000c80298603820400030011519000c0200080c0440c074881d9540c410200c1e003410310b005250f90004075520754a4042100140004c8202e4044500c035141120720300000c003000d8401c24041080c010001d00c40c00d54030000301600811020b4181032036805404003aa6020b00a40a40b07a08860050019440e01000c1c0101c8a46074003441d04040c12102c0040c5038801a03010800300721140703002c1c030081100022050549581c50641a1032070354400c030f09508504041d62000f00b203000780b6800410360f10741c40c15155803011040100412505005113500500f964030300b0036a41781e600008040e1819400c02487c400200c00010f00d5034002c842050b4030480b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 214544739 1250 214543489 214543499
    0x901170c04050403030e070603092013020a0504050d050c03060702030901050406081009060e0f070f17190501060e0306180703030813050d0302040518010b09120a0204060306020a090e10 81
    0x602c4014800c5007030642c3c0303203040980c91200300702407001340050b5100002e21503458107240083c075200042d80e0f4207107030491a9244403515498011071007021004000b40c5c440d10f0301582910b540c060f46d0042a000030401d1440410b00000042c4142c0c5002c0c140d05456082d101d002c012610392050aa4031808a10208020040f20f0300c10510554840d4034050400030b040d480d2202e0405a03066136100ca01d041614409205d030244442400ca44c01901e10f00344080244040030001d0268070109a038042502210750020b058040101e00c991030404c0d08010800880d03845400103004404d188420324028401c0c000021400c6820b030700c1c207244020510780144401c0d85941d808698000e00240031f804c0d00d10000001d80c0c0021010020302c210009662400f6031a14144424040c0c440001034561811424410040014905280849040000c00e0b95000b10f41c2c01c80100203490440b504100a4100b03280c00790000900510703601414180c1c0856031822815a60790700c03082c4c0c03540e40650741d851001c400c92504020b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 214545989 1250 214544739 214544741
    0xa06061e1b030e060d240f1401120608070f0f0b120403121a1008071d040227010801050303030106050f091315080120070f0812070309020901170c04 65
    0x884140320340342c49603181c3c0c40d0f140400e04680010040d100c80c2512440b00e10780c011030b041c1c0b407a04030400a00100110b1858882000903c0e80d1a03c01e2001100c4800c28202c1246d11400020b403164614402c00d21180e40c0c0c074150700340d880b801c3c1c2c85148011811004042100d00b155040b100468504101c180e003030000040c4081250140903000f142440b004140d01d81003c40e0798015400c0040c0c803d28181034005100e010320003c4015900c140f41000429410801d0598100e40c10004100c403661968140c0c480301000300c0e000344a41c20125040c49640e5140c566404499080244681400c1e23980041507640c030010716a884c0000e01411002c28418801c202c15960a4006000f50000c018040c000c0248000c580e441215035060750100001038194061060220034026121091804503140d1240343c201d054a040f02d0254500040403c0e41400599082c0880942500c8640d0030b0f1201c44009401c0000019005094040040340580700320000000c00c10000c1c0180d09076a4030300c0c2c014158210420003044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 214547239 1250 214545989 214546037
    0x6090f0f01180f0501020c090c0d0506010905210d0504030503030103030e040908040b030603120a14030901090c081e0a020a090f090524130f0308040602120a06061e 72
    0x30304200e0400c907059048110b08460340014050304102c44015810100024200f400c50160b260148034071200b442581e0345690110780204201d6000065241c680750012206404541d00180e0301c40c1004994036040c150000010580c400a002111010550300400382d80380d019030b1001800940044c001000460300074034444110900050000480005640d5440c82541080d08610043d44010040200d58242000498030075040ca00b0070318204010104014070030f0131030715200e44003960040301040d0a040d00350454002c2561100721521026100c41c0495501d00c03940c1c040000c0100b1582c2a400030110100309400300a4001e00708440c85401c10102c1e41c0075140c51035603151420703039400d000c401140080c0030020b8038030321b4480d17a00040322040000200d240c5010b8101c41280c5100304070040022491548130380301903410305005903181d5482c18004000d000e0300c9409195611968100008124958401000e80d840340d2501e504001c0c1c940720141b9849035030007510b808107800e28041032190065032812 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 214548489 1250 214547239 214547269
    0xb1e010f0506030f09031c05010e06010903020306011401020f0d1e080c0a03020708070516050f03010b0307120507030b250201020a0917010e1006090c0c050a02040f110a0801060201050606090f 84
    0x22440d04480d2001c07c070511003100c0d0802131030381d9030b070f40180a00c0e2070001c04150031003024644044d0603419500040d0301d42d1818460606621700b6501c60042990007445948540b018150a4481031a40c07690f02600440000d101b0701d41c800d1819070800010741c082d9010754022000822842e00300030040030194000d6210340815a030960081c4074090000b8002c219196540d1000b00e0b224034280e02c0d00b02032082d410310300c408191180c0d040c070000e0b00190714000b5111003116000920440b0051250a0a90a0040903040030b40742030501810895403070080714008003400030103580c0c8106614248000c9081b0b0051000040000740d24542c100a50310540315034010301494003000080d01c604204200703240c6030f00b00c0c200c100810b4440c0d80030481002c103440360040120f0241031041100819540300d54a468041200230b20031540c40f1035803032400740141d0004a401d502c18840554907408080003403c108024030440700150b08000000d0494140340c41599205a03010f80b00c0014180031a08001c0c0c00304000b80c0b6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 214549739 1250 214548489 214548493
    0x90702030702100912050c030f010608060f1305030703020616050306030a1104060b1803070b0903030a05071b030f02030609011107022701151713060c03090b1e010f0506030f09 77
    0x4080380340c0c5245e104420f44c2c1840359008004019811050505101050940e00c525074134140c0d08100c420004503600b54800340d8540c41d0005640c0350015600f01c00d40c0190094102e110100b0b1000400d81c00042d030381e0040c01c40360999154401303031007011901448201c0d5443d8064020540110000c0e4440700320b8210f184d00248041100e6460f0344040c112500900b0000715245034041070403800d81010710114000c1c0c5840d45603146480300c0100804c0d030b03134030a04c0c01c0c000410000040700340501150380464540f80300c00601c4175400e00d641e403c04040410981d5004e82c864045e210201e000001c0521902c0d21000c190440c20703003060710707640800015281909071079142550b4007207440e603900003140300d542c01b8001410440b010310318030400040003d0b03065843c2403004040c04050010740d00000d0300310b00c80316910000c00324010b06040c4044000e04868900240243c080c0014440c10382c0e480c1004d00c0341d203205404901d03040c4ea41c41030a1a40d07442d06205454000000b000850014040700401544c03203081d03d41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 214550989 1250 214549739 214549757
    0x1c0801330320131403030307050912010e010c03021206040606140c0304092d05060d08070f061103090111041a03060d1401061502010e101e0905071409070203070210 72
    0x42d4412194480d461585050040f00c400780003c00603450800e100402c00d8000b5411840d00d445c001d032161103000d02003842007131500039100b2902001d4100c001507000c0140240400c3c180e0350300150284d0000d0300c5810317013850000000b400c1400c0c280b20703034001c03510b0550f01c3c5010b07110804417105075035000002c030117001d0008000205844a05004e13454881083c04001908c1481180100c0340c00c450b5441c1c814407a03814002401900c0e030f9486a0a41303215040440c142e528841403800202100b01102c2c010100da0401030714812001c46003000d54451b66002000780712011102e10058018441d900942d41d070b808104001c1c0c180c60758288095a0702c00d2000c0d017030a00030050386d196031089040321802c0030f1090b0345424003400b00360410700c4141803801180c00240070910320031160035210080003e0001c140c658980c0c1400400c03002005262500c046442e0802501c01c0034240a40c8400d0540a800795103100c00101c80c0080c2840f0710454491007082c1d01a42c10255554204004402c58400070070030401d80b44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 214552239 1250 214550989 214551041
    0xd120c090512030a0305160806011b2a05041e0203090a02060705030d15050105033103180503060708131703070807022104030308091c08013303 63
    0x78101d200c4400d1031070019916403804d194010140c90005040c00450394001050103e0140c00c42c0285401002c05d080c07410640d90b265094540348440c042c0c0c090094402c6491980192840a9849880720721701c0d01d400e44010b40303600600c400c0d1060341c054141150220951800320041560146404c40344100903140d559586400250040c3c001203070035101c0707400000e8202140380141c0b107194107002d1a009902052450030001030141d01004101d4101209507400c3e10120311440d903c2401e00c095070721a4080301c41011308000f8543d81503941e40543c4110594004146486c1c0026802c0c41000706a40d940d0b0103903a0b001c29a0151103200408a600d90308061b0b110070800800380c081d6124400c15600d1010910349030100030725000d40004240006070403140c800828030b05810854041e283c01d418026042d480d00d600c030600c0d152680c2040014245544c0e01c18041c0c0d94010301c0c260481d500d082c00181c01510001d00f061710040103984451640e24506c1c440362138035019400c10b44030b080c49500d103100d00711106 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 214553489 1250 214552239 214552249
    0x20f091203040e0f0412050a030605190e010e09250504050106030e060612060604021b0304030305030910020c03040e0c13081c0309151d120d0c020d120c0905 69
    0x4004908094201042c103102c80b410150700e16500212140c146200b9051540340e0384004480d0211004c10050f00059500d2080d00a41103440100b0010b06410740090300b692054401803064084c1c1d4000c0c005020000074000e4a940323685003d000e03060050120050010b61040c101c003154511040f02f0344070702100117030560359440743d14000c0007951004500d181c80001c1003800c0c200c0c0100342d144a031500744100440980c0009550b6844841030340d005a5030140e400c2c100da0040e11074403c8450f24800040d01100301540500510b025020500440d110b0132865441841a805a1407040c141980140020000640d0b0341182a82010714101110b113070120007810a65851080d07005a01503600c030b1440041c051544407209002c004040c07a0803c0485400d070b45d01c418582c6298800844c040e101c011214055401c01104035200c0c0f0a181114542c42003402c00040c250800782d0345429507403130000161080303400030541154601d0f03aa07403210031000d1520100f100801008204804028460740c01140d16121 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 214554739 1250 214553489 214553509
    0x30c15091a030103020f011b03052b0c030e0a120f0e060c0d0905060f030a02071a0f09010b0a261e030408070506120703050604090602120601180b040504020f09 70
    0x144107416500d40c10b60050200b42c0c642650716904104c0b940c800000b0426081360b04141c83c550500d4001d1f621142c0b426030b00000d0403001c010701c400100c003e20340c1940c0300300341d4060124542e160300c0030700200100002c4207854070510b42004d4000d640c4031021518151080c4905200600a810714041040140c4049002c0b904090000c0443e507120780a01598503401c40b2840c0000c00c81155003500e800408404c040e99800f026104003c02e0740c01140c40402c0122040030848040c4160b01c86005a24010400401c011004e480c1d00040e9403902e0251082e5040c15032039101074070242101c1c040307107848030214001b00c410081d400c42050f000b20811a111048038103079206040105034002d41e100c5060a20392030920b0600c2d80114880c2c2d000300001e4402c00100d40c40d0560009041c24001242d0340e9070030116001c2d20500100401051001819000300070540584130b010300d4080c0d0b51074103c000f408401c55400b00c5980121441c030030062104025600d4680c004064250021041c10305261440c0d010403074060b2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 214555989 1250 214554739 214554779
    0x2010512010e06090a0509030a12110a0c0b0108010911010e120d0215090115030215090a0b0705010e0105060a150e06030106171b07020402070609120e03010b0604030c1509 75
    0xc002c81800b0003460b04108260304503400807001c00c160300300564041e90f00d01c54850608140044203003402012201540703c0d20030207003640c0c070141d50b404031084024180014818100da161040c0e10021030008814411a550780d6440390350340c4a44600b03c0d0041d907a40b540c6250031541301f20300392100c9140c02c0090008001315610f0350024885d40003c0c040552400100074001da003560725180d45500d0400314030315001b00300d03501504c0c40c08601c0b660022036810303842441c02e034a03040b080500c1d00044907078125000f00301c0b031402400208055041c481c3c50500741c0c5e00607941c40c2e5001010360824840c0a801086000e512192814040c140040389004142d468200341e000f44e0214400c0642041032004c203050b0f2a6100c0c2c00418601c400c100b40605040c002d000d0250040d004927800700306c0b082048010390140e1807458100e186404009080781c40100b412029070070380c501950901e40c00d20a00c0c280001a1001e6a600182c0208041d08080549101d25a9800a0410400940340014a079549000d040303140c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 214557239 1250 214555989 214556009
    0x140115150804032a061d120d1d0303040c030c1d01050609030102090904060b0102060106051912060909060c0327060203070c0812070e060c0309040c03020d0e100b1014070201051201 79
    0x5950108006c000400160003c0b5070f074004100102ca503503481003c03200001080200040d000141c1103154211044801e0328102c1c40c400041400300380042c01c1070402c12248114810320b0003688441c1203800403540d01d400c0d50724021b40c450041c0010700e080e402924600c04080d0006081000207400101d1171402600c040d1035265944c50000b00f5564184406c0d8050816400c0c41454000c89581c19072208a0201d035607820000307041c50ba001903c04942055000308910300c0140032501d010708029004000d0030019001082c0703000041040200d001912400c1d0180080c10190b484105403030f0782029500c01000c0c04100034000e460500011806c2c1c01410800007600c124890300d181030140034004e629540080b6104141c1800f944100300b07400030850744101c40596021401000103101680a40101200304610a0418031020000c030000101c81c42d10203c0c800c4240807100660302440ba000036112540d80020740603100300110800c0c14801006210320626180c2c0ca040c0503030407240b10940f000e0f00030003024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 214558489 1250 214557239 214557251
    0x3150b0f040f1e09020f04061a130f030305030901060e0702070306090807020607080a0306050405060607030e01091716120b010b031306050f040302010b0a060e0d02030a140115150804032a06 83
    0x76080ca0140c4082e46c0f40f042c0d400b04a580d003064907221103181180c150700480b001c0002e09009041c104002c80c0010311510843c11081030f200d16014040390403c80391390100d0343c41c3c1100001c043c2c802e100c40c07c1c01480150007034640c180c1540c903450043e0100d40003e481c0300d0000c00821005032610b80080c0701c00307070088071410f49500e2080c500500391216503110611032401c18044c03116603964103084400d581c3e41800c01d8030061144500585440c2c0f86a440540c81c0200507400003418100031540b8409580d5428052102c182ca030044840c1501d1000c0001d4030890310f820050091a11000045400100020750360740f88d070505a50301c40c241d0b8000c48010700010200c42c10f01080640900800951040c102c1e64030103620b0400e02c0042c6001048140c0d10b04c201c1c00300841e0400d5490501c8540c40d00d503000200c1e002ca5400d6080c40340d0203041e584410925a41d0105400942c40810890354210450f850361080742d25121600e040302c407640448119030203c07240403080c07a001b100507011a0084c0c1c2c8904408214 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 214559739 1250 214558489 214558493
    0xa03091713051801030213051504110405240a0f1107080d030506010e0d020108061201050a0506010f020a171c050406090b0105100503012d0e0103150b0f040f1e09 71
    0x829041e24041004026a5600610050361460031f040000081c0440000c3c107030f620449003d6101d2041c0c416140c02500e030201006e400c2a904008200391103090f01e030b0121030400d050490010950050010f401200144140d50180380300d16940070081030207261005100a41160307550810105030322482d825401041105074050f01401341e0344c0d0242e02420140007101002d80810035207070080400030304002103440003a850366120340c3d02d010342090803c001c0000389402c40340700e4020a0140e03011408503040c40034155003039200040c043c1d152548035900f01020b41e210078900b0060303001800310196000c1c0b0b0040647c0c42c0714040c46074074410f50013504040740125060400300f002c0501038010600410144080580560f000f40440303044803401150301044450f08243e218060f015a0a85902040c6180d0009106084002c100741039074025240c11603881c0e2100d114008540408401c250000349102d602da6080c0f805030b100d160914110f1001007402d02c2d1001410f00c0b408221041000010ba440d800041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 214560989 1250 214559739 214559749
    0x3020301060210020403030f0f0302040b070c23010c0609020a0308030406050f0703020a170606070f0c0905100620011401091a0303070c0e0c120115230a0309171305 72
    0x20010b101c1c001149003a007503441c008d013014108000c405c248804201d8044c081442681194003d203240491140c03202100c0c0b400c0c01d1505503510070300c3c218045450f1186103050036600f29041c6030750141c56401d444507141c0c0c2d44d1406003060010581c1d0198030207c000002c514840d001b144500e10841000800d841c1c14800c040410314003406000801d481444000f00d15034000344004002c80c1d07001da009059035600b100180d0300b403088050013802c170b0040f01c00000400421480750800d6511001c01417000d940c03400030075940d02c1100d200301400100c65040248074145a00e4005110902c900d00108001c080075821a00c610820b81c80400843da407420f00001a090aa440440c0b141040b0042e42c0340c9034594483c05a030058500a02e40860344800200b02103401110455100d90818003030601a0740e512486107408541c07814900c0040b07400745090390711000ca4100302c0b040400c100340ca403500301100b0540440050000e60b10440d00310010811540d00811004054561074030100214411035080038140f003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 214562239 1250 214560989 214561003
    0x302061503071802090d0f0521092b03090f060903051b061201150e0616060f06031a07021c0f0c02010c0f03080414030f0d09050a02060406030203010602 67
    0x190884100152a03455a40c020642e10304a40b503000590501c080b95142c0d56009100e8a10415030000d850b0751800d0400090445035506240528203075020000c0300c0181250021155422000050080101c0caa451170032240320550083c0d80f4074001c0c1104002c190724581d080c0341040550204007003500c1008032810b800c1e40350001d0b009626000301207a00e959603a5a80b559404003083c11121201404410398580005032142840e64142402c0d095039a102c3c6e0001102c0035080e0200040e80c0c980f101520f90403c4d03821640083c1062044801e800f500b600d8100007811440c0c010428140c88c0c080003c0420b103d9002100b801a0088404000d802c00f00c0d4007030714100409100b00300c0484015290819290030100304006450103042c407203c08040b03480120f840000c604d80007003c040d100708400c03003415030100081d48694416400501c0110550021a58a0240060700d85441c1004c010821006034540c01900c8024420000c48295072312030b43c001103554005802c8840004d80c0440100907043e8104141 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 214563489 1250 214562239 214562251
    0x3060b0d0206270a0b0301150c050c090408040906140f09091905070e0c030910020f070201110106030f0812060409020609041e05130b0609010501051e040b1204030206 73
    0x11100350595021078140c0c000c0c0141c1c60503004010384198070300085610358030b0740c1e440d004090248040d01c4103c410300c1904207000b00c80200c00000c00d1044642d002c1c2ca21000f000350460010310f00c8000c92005c01201031030080c01101c43c0441030100043d01c18040c000c44010f01280f0004072040d209217414404c034003040001c41c0c2d200d840c0c01418000c600e503003c50540248001d03050741059400060400d6860701200e03a2101e101000032004000341c0300544000345015500c81800c1e111044610f541e0380003640181215400c8480040050000642c01590500d404110f0400085240340c0d4948403401e013401090000e40c0c07264000100866407240d00e101250384041c00b00c90400c1a21429008074803207000704030030107002d20343c2c072102c0c080b0944100c0640b08201c00c4500d824010381c0b400c4044480041000307081100e0640a001c0070522500c2c1444000f81078172011396999003048406403034040c0810007107000506032401004045803070314084c1e000344502008110170010074201840c0007840c1603002001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 214564739 1250 214563489 214563499
    0xc1b010c090612021e2b0c180f06030c0c0f061d070303090501030507030b0a0b131d070c02060c060a021c020a08060105090a080307120201060f03050703261303060b 72
    0x3100e8030a120480500a0710070b4074010851301c86800c2481031441135406100c42c0c12640c0900071500c401c1b8644d400400841c04d03550f40d4510103103c0c0300d1415000c42000c3c040d8144181c20f12000b03200c0e45201c1d07445040505000e2502518800c2c40341c07180c1e0b10588040b90300351520381d02c801200841024091510300320040c904010720341030340745880040420450340542070415840e1008034104034070a401c070080d1820024514120705694102c0b00c00303980d202244181c8a00c0000b00000b442c41c41d201d03c51010381c026401c01e40c06c0e90b901c1700750480d0503e0138002d040780e002c5024011910402001c004061240000341c07001a61221048100c90350340003101c1c880b1082500410025071000c1d40240980d1300480c0c20308120b03403a454151300003590003605401c200b00782e102c0803690300140006802002c1080c1c80940081001d035807925080343d021881c41c04090b003180d02000c0c0c100700094071244001c2c0c400300e034140c1108008015950b1030780207922401d11a2281500d4800c103206110701c612840d100082c080b0307070b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 214565989 1250 214564739 214564747
    0x90c070c030c0515040e0c0306040618050601121503020f1813050c10021e03040b0f0904150f0b0304110907110c032802060405040e030d060b0f030c1b010c09061202 72
    0x10020480300d0014070181f034441c2d011000c00c81a445607009600a411524031080340d810780401100c0003484112945400503003403882c2e01100d5461803081d1450a241c0c0500040b1242c155000c2c0301c544145028020741010b408244103904100e441800342c000c080108070004454040e0078444d28108446401d00e2007201e6682e42d111085030009899a9011a800c0300030040c003400303400c04c5003107014581c012807800200240761084044003100606003020100c800b044250890035030b110f02c06445008800d03103100c07440028000b000c80790014561192107403100c00601070000300411121001543c40c903012401e4941c41d041903d030305111141d00c0d00010b400605d0a07012181011106250410303940803405100800b203010341d151441100c01900018000f80701415007090016580d5100540e100700c0107113030010204802031000704990307070900c40e02d60f0181152580c19401000341d2002c0e881c100c101d0a0038002400000e000c1c01441001e80e51622034401180c41c040300a0a1301e28440f06c5418403c0c8108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 214567239 1250 214565989 214565999
    0x90f07120c0504050c090d02010e030303161206060e0909012307122013030203010203310312020903150702060115050705190305070602030a02030403030b0306040b06090c070c030c051504 82
    0x1903446d080c03001c4a510300341f00d2940c001a9050000100300d503415002c000200180c6806891500c2c0034440c1541e1140412000480c035201121514000c0390001040d4640700d0100340b404081854000120100016820302e2800b0480042038004000048420545082210082c0c200654071042203001c1c1c414031140e195140104c102440300f1451509032100071442204010504a803000a181d0181c0219030360b08044810244800b00040d06801c0070710b44c546180d07156070701c1198226000d680350301c60044104551080304041c1d040303103003956010b00c1414024205140e90020550084109801a06c007a5060a04100d0070440206440040c018100300c4d440000c0d2000a5003a1102010002082c1c40350b1036140403502881a010060701060000c028048060520350045000e5446901c0400c21048074000b41030321190102c502401c0c2c281180c0c0019080d05144112583c080100b00c1000d103020051f59540c900b100340c54005490117104104284160700f48031901019100c0d641c0c08071420240f400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 214568345 1106 214567239 214567261
    0xf0203070e270109061a0a08010e0c070204090b040204150605090405070201020f0a020705010f140714011d070e0c0403020a1a1903020d060e090c0108090f07120c050405 74
    0x240d0406c4040c0d036400402c40d0184081a1240b040a03845d11503100045640108814011a0200b02500040c3c0c0c0e24030401e401c2c1031003a50814031a0038a40140030450305141d54900071f89134130190512419400c0800d43c3d032584011180444d4540c0c83c014228003901900c00600c1c034120000c900d5541c1a0b070082503c109030341c030a90310700c5501f4940c80c40031680783e250781d07001d00c074199020058400407409000b22940200c42007030000c104600d2030203102410052030b02c0710310303100e8114940a10032840644920781d04609101d007a1400c0c2400c5800049550300584039070392510184001d141c000c80d1550055030910210f0f00406100070541450140103035018004502b151890b06e440419030341e1804032440c2c06144440000d0220810300310041d1141203014110100358440d80001c0c0b100983c0421096014141d01144410080000d01c0c0400c08503d440d007140c2c0c0310303904117020440c400c640c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 214388489 214568345 := by
  have h0 := BRFrame.cov_init 214388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 214388489 ≤ n) (h2 : n < 214568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
