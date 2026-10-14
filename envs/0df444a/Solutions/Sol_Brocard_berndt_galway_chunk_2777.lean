-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2777
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:42:47.544304+00:00
-- url     : https://prove2.me/submissions/6c6ae932-c61b-4a63-8ceb-91abcb7da8b5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 499280575 ≤ n < 499460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 499281825 1250 499280575 499280581
    0x306120204091b030b0412090b0945060f0306060904260a27060c0204060510030e070e06030318041b090602010e0a0f0210090b0f0d0b06030915 63
    0x1520f8440740e512803070f001450300c3c250000203100e22009024010340c07288008444000c5110401c80360544a40515080c0c0541000111403601e414150b1082c0a002c0342e0b0500110b0941c03c1c403010140d85600c4109003840c140c444085c500b40c280351401c0b0f1313001c0012500352071032510900100743e0340c50000744018091500b54021606100c044440320b0014400d40e00301c02d642c0451002c01001d0703500681e486102103580740c0d0741340b040d130140090344034003002e0104024516986400c1e81240d802c8038012080e81c07c43c0d6100300c0416541c0750340680c01d40c0048503490101e039603543c1401c000d1811903103030b001104136140c0f0020b0080701d030360203c11618550788150314500c144050f5000100184500940c185202c04946100d2814541109c5540b0880b540740d00200711100b40035500e9a11104250740040200900700d40c0c500048c50041039178501c41d00c10703240c44041c00e9291681940c403a0b0200144a2002e4400304103038803c0c2261340600f8210710016200c09042d4208100300c60f5840802c807640fa000100f0013000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 499283075 1250 499281825 499281833
    0x10c02011107080f270405070309020d02090c0f03090703030f0c0c090f020c1c0f0c020904020d05031308010b0a0f060c0609110d080d0c020703201c03020606040b01030612020409 78
    0x2a204030251440d801c070f4101307613422241e4220809071707404a4015414040001d01040c0039214480d0f0080e0050302e90040c5039a56403c21004d2003005001281c410411700100c2c40c110140c002442c442c0c0c002d0704c0100202c07403d500300505030320240d121103001c00400e60015000600107068100803954021000715101480044501c043c1c041c06802c96260b205140d6902c3c041c40415446400a0a0075150105c1c600076081c0121002120f111010b0342000c2d402e0046030060919200e0b0801050068054904000003107044861080035640b00700d401d44e44451007000903103080100480141004094000110b182110180400700c21980103007150b950b4205010501010044031500d551000380381403020710162900341295000040c0015403646020031000f0100c2c000110501580e4000c40c0202040300c000c40c000300c101140c2c00116030413580720641c0c2c01e281c200c4950300c0e081052007038010302464540103050000b16a0030060042c1058248101009274a681c010980d220702d406071400b02c0d2000b19420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 499284325 1250 499283075 499283077
    0xa110c152b0f0c0305012117040e0f0412050a1418031f0e0106240e0604030803010e151e060f0304080a27060f1e11010c02011107080f 59
    0x5480d038038506000d92020400b240c0d5001502e50001c42c1c508014a0740c07110090429010030350220b521601c00103d081d40410350701000280078002624101f80b0313058441102d0003407a00107a0f59441c1c4102401c0900042212580c41d1000301459072402500b04164000f00522203411520420180040050811030034035241d00307102b19980d0068122980210482d80c1c04200e035030000103e803805898100e60004680c01030181c00c048540707400129440c04070a06030301000310341c90340e00783c0c00340301e02c0301c40612040d111034010384015030050340999242c1d8548000450301c1d450040920250000c5a03c1000541ea42c031100d500800e1140e1003c200039a00240100c1d0350b40c443c0c02103c000004000c17042104004000c6c0041840003441d96462800304d0500b0306407030306c40709182c101c0c03598034110800500003144100c4106881c01036a280403900d40c44030304000e0118100800712000011120402408001c1090003002c49035080c0c0d100070010001c2e00c1420b00028041c0c0742d001081e61a00180146c820350980d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 499285575 1250 499284325 499284397
    0xf03021e06060a061d06090a15050307031b08070503191509060b0403030c110406030605150f0f031b0316060305010807170303070c03140a110c15 64
    0x30103200c00415040203601c0e03441904898151080c0d01c0e090300441c9131403051800c0c4c100268600d220010201d00d440c108001c0d504900b45664000780e10040026000d1a43c0c10300300440c01e4591980c030b640341071201005003920040b11350000304004252450410503400303a0602c0e44085a860101d49a4440e40107115001c2c0c2454035014146080c4079642c00d100306441071040441e05c6041e0700704a1070360f07581d420460070700071848007402003100d028000c00895940301c524100c0100061000400a85030342e03400c0c04031030b01901c2c4015820210414922241805206100c051904584a182c4140f4100003c1e070707180074940a4500d0822003600001842c0c42c10455900c0320003680404400707068441500400811007403080340385a00c1080d0000500000300851501800b0002c8090351650307a54090989519070005412000c2250a030104032038a0039610103446012090b6452411040e015000c8601d800300ca4908188146601c55060007800c0c10b100c1211031800240f03440714400c0c2001c018003088900a8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 499286825 1250 499285575 499285603
    0x1180b0d030e0303160b0f09011e022203030c0b0708270c100804050709020a35010b1b060601170c0702040504030905091602250b0d14070203090a030f0302 68
    0x51710503134100309a45c00310610528495052030f0f1680c0d01c00510340c0c241c49601542e01591401e0300d44030703002c440098004042480c0385074924409007076054044089540e641c3d0043e80080d28885c116410041803001d81c940011107031a20f07001c03504006840d4000381070100d00c0c0c11008520038031401400b840620001a03c03100040a5001055812101400c242d00c112004c1f5428054180085802c42e001c0c070a65100500e5a5a5801d05046829600c0030100e021241011010b0f90a2072404020f507111100f80d007c0e0950b03000141e102d000256818030310711180201c8480d11f80181040180c240d074040b01a50b141032104008000d10340f120b689220b038500c50010701071342107030800080105060704245003d00710b801c162a1415141c3d035100e2030f1041078a800c0c55a100580259102d0302891401c240c03000a55403001121603103041d031341d0345c3c41e01465010607180c480168550881c1002d0030503070040964032081900195140c05801c800140c0c4180c0f02e80002001031814501b04000d150ac204401002d005038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 499288075 1250 499286825 499286857
    0x3050705040902131a0306010e0903090618030109051e06010515070f080a03060e2a03062d091b0a03020d1e09050d020a050709050a150e01180b0d030e0303 68
    0x11204941c01c00f2900d05c032141d030080c45040300000f800ca0320014840e100e055603201039800c000e0441d0802a681d170048019402c0500c2802c90124a55003e2244203019031048008200740304200201c801c003c603140c5e0721721090703030410001000705440760541d0350529001d06210950700c1c01c0b44c0c40c11228904064101034101c11000c56201d1a0940550201003038031b190b03001c01403050792801041e01509448c1c1e01041c1c42010460742c00440440100051070300044000e03c0c0411003141a21010803e0180125081c0340e00f6940c2c1040c070355814602030f12a005450181c500140c400e008050105501ca038005840030168001076a180700d41881d40b00c004940455a596500d240400b054a4007801c07412509488500480f01c0c0c500101e07000050048940f0340c010080d128181c502403012004010041545090030f440301114180407810209034000740180c1030500d502d40d410040c041e540c10840004281c00c00c2c0c03500c40101368035900c181e24072090551604e8081f180803440f0340424203500032000c52540b8041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 499289325 1250 499288075 499288091
    0x702041e05060a0906060507030c0302210d0b060c070b0a0302130314011406030d080c0708071a01080d0816030b0603010f1d0f0402060a210504030e04060305070504090213 75
    0x85500301c03074064401120320030401901c42c01180708564643c41103030003240d802c000c0000000d00a1781d41c05c40850190060791200781e0301c000c4003113220816000c1d10007038102c0020808203002407480340c0d400105060301c245050a06120b0441d540d4503103030203810801c900201d0380300034a5100390101e8580c180741400300324243d6668a0101d0030104000e1480d5015400d00700c212030b212200c00741c05440340c0c40007001861b000e1307241c001c00e03200312001030149554003900704142000720702d00034001c04076035100e4083e401e164412165072104418068000c1200c9030003500f080650540d04c0008550403429243d00303480390025510040e0f0051046100b855049100030000103090803180b440d4401b2a0818080318202101c0550352582c0350744221740c004801090480880c0143c180040504514617650900070484e40ca001e40c00e50541648a01c00c602c043d071a00c04110405a01001040c0d440005035020321000b400e40e640c039a15002c0300d020f00d9014030340c1c2d000b4003070541da66642e01c2d80704806045000c0207144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 499290575 1250 499289325 499289381
    0xd060b070213050c030a0209010516050322030803071116080705030c0d08040303030902190f0f0b0a0906050f120906101a0d0203060d1b050a0f0503030d02070204 71
    0x40c11041059104808040b04142d40e000d440c0030343e601c1640310340b900c507140d0398500644200a40041c480319040100a2011820f904075100412605600600003183c4541c01c0e450342400340e90704000203401c0014080001c00000703002400340c9422a0082c01c01a1002d691a840d451400780d40500c0e400b8419260301000469400116441d001d6650540580c4c02419045081c0401e09840c4035004249102c20001007012030301c00c1d40250b00103440203007801020080141e4280e400202500031580c1c0c0030414030100020a10b55206d0401860040b018038105540754030b002c1c120348a24400c1c0c0c1d00344100001c0117880c02d00b0100c12140303205240d012155450900c0740f03180d0b996250403901c130b1210a26419010070316416642c00b4041c18881c43c0360107850508a03503a1540a90405130440c0d4000c08603139841c2d00000c07074141d880d21480000303d9a0040441c42c1c441088024082940803040c61100e03214188100d86012040754030880c42c8401c050780d070310a80e00c042030041210f08204000c40038008040e0840c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 499291825 1250 499290575 499290577
    0xa1a09030f07060903030e0d090807050109120b0408120c0a09170303150a09090309090b0a080307030e27071202090102070e060a030b071e300b0901090e0618070b0f0d060b 75
    0x91941d101c210340f0bd245c0c8560040d00c401100740120090030041c0c514480002c3d200d044503030307885886080b03101d080c4100350040c07841c404820794181d6078020001c41d20340400c940c071000641c000d00505031031840d50785000c03039126100d00c00504100b40c55450070601000949664104000502120004105400d00781c20000c20315405401030380c0c841820004015034034600300d040c000944188001540c5041c03400d0350140c1e0b5036800a0040f40e0400c0c0c0347d040c6000841c0b00c030ba09541081c0203504003881e00f860003400043c00b500c1e4101415107424418080c0a2881c1d07800102038040c1d60603107400347c405460300000100d40f185258002030000e080542004032443d807090368004503440c8443c0381d500c8004009400da850b01410b254401030000d6035090400003109030484140b00302100071001a00c1081403010541441090304254596501e41580045900040010f5940705200001000e6405100115180c0b1b400140c4151642c180b408100700a41804000448a000300214410490540d5031a280c86075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 499293075 1250 499291825 499291829
    0x31c020312060d17180d0b0106021005011a0c01090819020d0503070e0d02040906050a0617070e0f22240209030c10110a1a09030f07060903030e0d09 65
    0x1000c101e940201d1528286120b014051941c4140581d030400c001d14114152508843c0700001401120140380c5090348a848803019801d000d80e500181c15070400c807002e85060000e644007a082c52510004000c4003111408ac51180d8607000c46075070384e032007400040781e015202451024080c0f00300040daa001100300f220481c0701161203074003980c9060086080541d141d00040b00c800c404a1002da40e18880ca181001010413640c1c40104006549003103500e070001110b00450b66540e805644038410b100499071000c041c80c6501d5094000e1108a00301104074122240c094407803584694980d0205500c00910021340701449880b261040c1c4203100360602c02248624000c1240a0740442104411001400d0088840074035002d0004c2c140c080c2d0380030901910f002068452000c121a0b101c042d02442012700042c0d4081d03000e241c010082d07900060003080b25071030103030017080d8640c000c104c02100e103840d40c2c01341c4400c690002030014045940d42000ea000d40001e80740820b56000f40508006002c1d009420401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 499294325 1250 499293075 499293097
    0x91514040b070b0105010c050703020418060f0b0111030f09040b06160503040608100303022d1207060f090b0c130e07122d0e191a060a0b090f031c0203 66
    0x400e80d1740c5034010b450741d45155802030020340009900380701505040d001400028040060a032402003582c03101c030200c807000007400c2c0c00641c035185804c03155a070181240c1c0f44200c88d18081c618003001003030203c0d44d520488071024061070300d521400100f40d64100540c0d0b03c03900000c8100034410250f180c100c4c1c50341d21034014040400c10352400701e000f89401342d4002003680d6050300100101980e0452141d9035440324442c80c0c0a81d152001c00389201c9030184400c040c003254030004070381c0301c00561810b00c00352400d07004982061860720605001041c1f450528540001c0c0b1460100e9440d0300680320f07400603420039000341030140308100a000e10240d02c20b0030641d0511070180100300480e91000328850a01c0d41c02440045103c1c009201801c00c03e07142c1c00500c10191907000c0320b04400e46903800c000559000c003c02d54601c1494800c81210f03105958000798030007411600203110318104591150310703016490130140205004078114a05440c1040b032a404c01d0390892104d402004001002580d0340e0221071045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 499295575 1250 499294325 499294343
    0x160e03010b041416170408070f050f1501150806121203040b040b06030c0310020f0c0a1103060106170703020f072003070504091703041b0909061407091514040b07 71
    0x1c00d00d03072150784401c5d044040d003c080101900e498803001c0040d0800d0340251541004400348070f000860400c5960191481800a00b60b901d08200f401c3c04800320580c00188028250214055010f074015209039100400710744441100d440d9001413032500c440079940c0e00301d01c3c000009010602c14840520fa00c240d22682d6019030b55030301c00c1c0905803182c020201460f015404031140000c0e64646070085e0804444940c50a400d0260000320103141115003001600d200c0c0024582d5002400d043c8849405807117070342020744038840303181c42580403a07800926078030416502140e140049940300041303541c056082454101084c0165002c03524050401000a12a20034401300050504050251a500f150403081460300050294065107541c1c0c001001140c003c1004032a0400d280f1041050402400e0801c1e000181b03540c0a180c9001151040030080c5007440c980c100300b10286038408000c10546d0300e019031140300202502000d403078081d5091800c5e000c06070042004921952171314041c142c1c65000700401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 499296825 1250 499295575 499295611
    0x506010e0114032b03020d060f08011508070e0415020315121203011e03021c1b1206110f04080a0c05090f0c030c09040212060a0b03160e03010b0414 65
    0x140d841e03042412804c402d41989400c01c5038441000c20841c0205801c0c1805880c00040f1500c15085841e9a0400d000700c40081c0e2007840661424030071401102d803118481c0d1010b905004103d5a1030340c1d10700c207001340b2142c400000380c04c10808114060994219683c00d640300d051061071103440c0141c40b82803e000e682d01175415030b01d031180040c8510050041030402e07440c690a0442d4403142102061440001c0c040c0010004011780f40c20440100f0742600c2d030589801d0101d24980700300d908401c4416030107003094115042c040c00006860000c04160b0144000034882200e0070601c80034018001c1c954041d80c800f0600148040010602100040c420032208180071f490360104912103e040e0381c801c800c41001c40000e40541100b0700210381008100740d400e4100144900014103036031100ca4000d0100e040041480200e040580b6030380060002a00468111b2400c44103600049002100180c10002003487c2e041680d202940884054580a00180030038041e5240c0c44030050b4068a4150628180b1080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 499298075 1250 499296825 499296829
    0x301140306091204090f021e0406090e040201080117010b19060201060905010e04030c06110a120e060412030c090302180103050f07060c0305071b030b06040b030a020315070c0506010e0114 82
    0x7400242c60143e241c0c5414503050844c0c900040005003405611aa401c010040d000403c80000741030504160030f1a541d614104240244101242d80c4051090003451050000503a0800042415200040200c00c1c0117100511514054008034a08070307004040d003002ea4049040704c00c14070041c0d501d5a002400f81d0780d942d800c0b0604079402441003403c4070b000d400c007280020707115104041d071550141101060545440c0b07030310805580450011808540c03100006407640290740124505420306501802251400703481d8202441e00c01d900002c20181c0d114298516036016000210103190090034102e2160303030804804042c0c041c280404d0ba02c41c4522212201a48400107515050b21403c0d61820741d44010f5640545513a0400301c0115070b6514003451a402440501680c94001d41c011400c80c8020f09040d4207100403501d494200702d019421844a40d00941c0b4002081c100b007601c1c50041800f1030707480040864404124100051060088000000c0d440040d641d1182c1640e0198058002102492003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 499299325 1250 499298075 499298083
    0xc03011d01031101140c060f1501030b0a05040f0204030501060803030703060e07090302100509120703030f05070206041403010e06040807030f0801060f030b0f03030a0306080c1c06050a020d02030114030609 90
    0x10000746034110302002c0700c507154452041004045400d6201701d0030310640e00019820020300f00c2d03070880c00103481c00401c0720780345511010102080d42801c040044004100c00300318608071502915014079140c11840e044c0101c55070440d8011034004000704003035074481c2d503456102d0b4420303104c030170000381041c1020808a480b01c2070709001d0a0305850f0610740f03030300e558244240f0038960000e4906015082c8400c3c6059100c045c44a0801300701c0c20090200c0c01c2c15440d010b00034007515403400d82040028001100181c40d003c00b22415107100c6005840218801c40010340909164181e49000c1d005030b9040c84100b00030a0054003146100380c4842100b030b001d40c50101c1c1c001409214030000a1000307000c5581140c0a035000c2982e0300009000c0a00d00005900881c0c80c5900405802d40000e0b61280300b0090780c034081c44601c14080c011104507001c101581c4041e29280741c00e12010f0042c0c0c4d41ca01c0072910801490f41200c0c1c3c100c4102005540369a510301c40d01c80c1c1c64024280b558007030b01940000518001c4085 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 499300575 1250 499299325 499299329
    0x7050604091416050403060506030a0611090a0e0705090d150914060f071704020a080730050a08030702010b04060b090108060d031e17011401090807050a120f0b0c03011d01 75
    0x1303510681868a991110317000342c80003a280700d81500640c0d0881d0041404c500910f0410340401d121240d680304900d01f03100b800180c0d50f120303400b08914030040c010000c0d4050101e640c81c1708216419440c01105043c000f03040d440b45100030380d8040c50700c078000c42001181035003c84222005003d40302a6600c00e44982c0c070a0314110f5900c4001034501e140e040100b50020040f0b81c010f070000d4070700c4a40340e894203000c520300001074102074030558540d400500540d1501c4043e01204103c04100e1480511540d51196102c2c0b00c00301c020048540800000c0c0c169200354801f8000305001041805142d9076018852800e81c010300c0d109002070bd022000904900705902c8004525500d0381c1c90a0416510008002e0015011014042081105000480040c0580f100d090107402d06142c85884c4600190001d403803da05640000e1058220182c01c1200b40c0d034081c5c9050480d90101a03c0385402c88c14038051205110310b1100900701c40e01d20050040241925006d5070607507100084a60b0005102c0c503401c000e0344024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 499301825 1250 499300575 499300577
    0x7031e0203060f060d201909050a030605040503120a0c090510140306210706110a1703130203030c01201e090f090717060414060d0507050604091416 65
    0x43d14282d6201e06014004284051706614001810011a03c19408200b940c0c10400d814800200b0158030307451120080c0758049407141056039400e49460003040d0b80c0f9a251001509035940d0b48002018004140102c3d109031500d05065841c910b011035a520040040c0321020000810a44003c659030400c080e09290f000916240c010407050140001259540000c0c403142d00078400d0780251001d849a40e08000350719507598041d001c414140800108100b910b00340204e2294008241000440c403892807031440c0d141c22a90155695848004440b41e0a01008009400d48000611419050010350003005074103010b46071005155505400c1002c0341c0070f40c1c602d100c2803032864000b600445110100800b440720000d480b2591007251100010240c203c103c0c0e030100454202e003d8a040258040c0ea44c50f813101c0c049504100e40c0c246a440c030750700a43d000b440c0f10f0140c107280380030b2000c2c841704110000041c400104019951a2540178401c09001c8110010380900c1c01100403600c6416044c501001f0440b507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 499303075 1250 499301825 499301839
    0xe0f18040305032401051903200403051c0c0809030a14031b2107020301140115030b06070c030f050c03061008061803160f0c09020405180609070e01030e030307031e020306 75
    0x81030500e408410032045847e0901d03560300804c608009a00020081806980700342503120f0385503052182c14046860101c000501740d0301600b40da50340c0c010030340d4140c10750000010380d01c80300050302007840c2450400e800361483c0403c400300c20743c4040000c01080500c800010244107800f0440400c2d0390b4041d41d9540c03c00d520728020403080b4452403240901304103800100046100c032400c01030701003c5602a0446460010001a01200321303800d0700a001e1031500550315640b404a21b81c840f103d03021240e000041c01c005886c100241071003010080e40408140003400c0e1842428a4801207044c0700c2c483c410601a80290400140d0b4000f5080f42114200c594001651070141d135449420021035440710202c1e5004a131100e10b601207425a40300030090a003650780143d81c2ca00b0300042045410f41040c00800341c0d0100c5041003110748841c090b036900040541495520108403400680107001003111138801480003004101c0e0003a07054200d141c80202404580e500600d5030f030010700a03440211041908040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 499304325 1250 499303075 499303087
    0x3020c10021906060e0406020405101404090c110f0f0f0604080f0a021e01060f0902030402130f0e030d05011e061e110a030e0f03010b010e0f1804030503240105 70
    0x400303036003408041882440c0002c4d40390f0301ca02d142a61840c09480070380700540d000c10309200e0381c14410a504803100b000d0030510303080c2c940034520038001d106502560303204ca500d0301540e8152601500d0341c2d00800c0440401d540420850380c083d250398140d102c50100b49482158002d072960140030500501a60304840e80d40d14106900360086c1c80769100701c10603000c6208094040b150924490904012411080c00101baa12300c0c088184d80d08010b19006060080d204100b4800107a98021074001c92180241007c900c81022820b6000104540a1540301d2400005006440c805007a44018143c81048005d000b4012494891030400005030140001140751120305a03029103011004080103006803400e80c5d6120102d14019003008011103045003c034180300c1440f2100d103401a44010b240c40c05800030007040c02550002004411442c441c0740c000c46003641c030850140c4540034222035102043d18844002d0a0601e4001e10075070049070000b005645c0400450764007000c034100312441c00016514107091070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 499305575 1250 499304325 499304353
    0xb071704080306030f0f072610050c040b0f03040b0901020304030903030c021c0501140606090102071824140414070e01120c02010903020c03030a050703050309031c0903020c1002 78
    0x242c0b003d8201503061040301885402c0000401040d462181e42da030140000701d1400300600304000c0c0040a94540c20002c4404e01d560410016015900e6466a139000c01c10391555001929944543d400c4050401d10005448500c40f44000080d40240c1c0321310500c030540d5540c90011800c0740000c1d58000d00148002c1801c0001c0b0340300e410300b210ba150008042034480400e1100301041003507401402c550036511181c1300c40d20700e030751040801e50280c1e040c0e071951f16107903005000075200c102d10301440c00120004540d910741e22005600498605103403509104c41c1e0501d444107040a04d05a110341d450300010140d40186504190043c04d0940b035413103602c0c1805840d4401c1c16114174106c41c1100b4100214a45070761040c501d03900882d02c4c82d01d403a400010740c4400a0800904104400d500310b806175204120103e00300b5842811150f800d80c1514000d034594a4160b001421032151071201549000160124922004503600c070320001c078842d8086801440f506400e0050710400e034048800907800480501e05a8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 499306825 1250 499305575 499305577
    0x90603030c02090c090d110f0a0b0a21111314091303050c010929010b0d092102030d0e0c0109141311040302040c11030703031d10090b07170408 63
    0x1000c0130a10303550030002d680e0041204010a62401e80b0540c0940d88440d205082100f408500d03e88103031130342004541024803980705032045142003010881ea241c0707150803060000003840c50500b046201449840503500640c5400d0b0404c0032101280340c14260005045480b50034541901d6034090100803042d030346d414000d9034001c56540241d007440020032610007008802e100c0d00d0000d034400c1c484021100043c41c001d0b6161588803100c95003003140e010051148200e5031041c0c0d2442000f0080200750758206103880b00795891f940d03d1048101c2041c0841102041d0003101401c402254010b0420451350428034042e66151802a824046014840140840191846407003066000901038288a5540041c4e210449000c10000170145001003018421854580190003007070a061600d00d07850f048410309907072a403082500003814103546854040c440301d00c044807004d003100d125050b910020009202140540380c8031504540c1c0c4114000000c801c10b0281c1400031a2000400034481c140e44c503a581e400d09 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 499308075 1250 499306825 499306831
    0xb0d03020a0305070c120b010608090f07170c0607080a020c0d0f0303270f02090f040308160c0b010909061103091905030d020301031b12030507030c0c080d0201020a0801090603030c0209 81
    0x140c2003040c804181b0321400046110170358861100381c076056140c40001002070b41d0103040a034882d004000010351ba490001049400e8594010f0b003407441000d0030b11450b14000d100d01c4400c0d0403400210b4000113016141003d44000070a58082d69a4a0201c0c010000034140340c407401008034845815000200388aa84061802e0410030b075004112801c4510402c0c0401007080225900050380e81c8100071410400c0001d45c00c01d010582050301800c0c00d68018040380310082421440080c21508101c40ca4840da201c1e109a9420001510040d41c442c175801e4050150108141ca000b42460340c00e80709210301c0320417244210002030150407114000d003907907680721040300d205407000e103c2400196030301200f0344002d5009500c00d00380300d04224070000c04070300d04050507841503a03586551030201c4040f90b0400c04403050541d1502e0300002d01641c503c1d0100c10b141070f40e0024131440c890b9009680c1c0c05a0158000c20303240c03541c6e440b60b200320b80c0d840c001c900030b90340e0900005000440864420f801814a50301c01d0790 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 499309325 1250 499308075 499308083
    0x60906060a030507200a05070e0c040b1e070308060907210e0304050a0e010e090307030203040603111e04090e030405030a14190308062e18080a050f010b0d03020a030507 74
    0x10745c100003043c0c001101c0401e0307403900010f070404184d040801600b00720501c01004501c9100c4034900e0311581031682800380b1711800182000005100f6003500490303002e070030b01c0d404d01307107805480d0895130030014a0300c0005c42d082c034022000200030030000350003007014440d9602c3c01a842c24043c00704440c007074003401c0840034034000c0f884140400f286540c1da42d071551018000c89001034025624044a51309211b10191006406800400c100000320794044115803d5420303504002c55006540120001c0e90b10403034945030391f01000c80f5032440014000c0001042165281c0005000450a6038844c4d0344901c242c1c85060350560140031a50000b03501d011010030404080010358002c0c0140a500c0e84103210480802c034001400c600821190f8605203400c40c15043c414908038038000802a0f180303e288051840d9039003889000302e03071740c01e000c4d2201c8107490113010983d00741e4100038003510f0045e0b80d03007080d6086104e5035424014004124200007040010080c7c141d8003c01042c1c003e40c805031a95840490161 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 499310575 1250 499309325 499309337
    0xb070210111501030614010506180d02060405030d0206090d02010c02070546060503060105030a0b120316061a01231902030a020609011e180204110a020105060906060a030507 76
    0x10b5100d9419940e0b14020b50117040c001c81c0d0500541e001d8034210030141c001ea0b1040505000c0008071070b869140301d080c4804151230b50001c0c1c6100d40000f03100f03801680d10107a41031089a01130140682d0124885005040c6001229103810451600740d09072a84006c0e5140184c1c450581007229242030f0340340300d0424054612525100c1e030076403d00b40e021030644103030042c814000c0f51030421b132510741c40742c07040100314a20b051070440c00d0080000f042848050a441d468640314101010a5510250324404540c901821641d56a17040e00c81910030400780c010640d0464034004205510031560b2501100d80c050580d030b2091043c0c840850004560f20902e0000c42a0b0b40900603540903000941c40c201d005403640d0015030302d031520300900a180c40350051103040a80d040056030711100d421548107280c480000000800c21401048640300700010720940654400e00b807580891500000704000c001190b00e99009011980da1002030160529060b10740b103410407820001a003074130303209031f0202d40c0001440c6080d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 499311825 1250 499310575 499310593
    0xf09060e1309110a21113c01080412050c0c0406060c11091006050f04120b090105150f010e120a0c080d020105040308190e0a08030a06140604031e0c08010c090b07021011 74
    0x302c8002e99000101d20070b040c06040b204001f441c042d803101d0042c15400d18101c4a58582640c50f80720141c2c003012010300707208000c142c03002c2c0e2146c140441c032500c40e00a04208800c40d984c0030005c00007621004c05071007031183c0c910700c1082400d0281d00203114442a0464415661400800705c906610010f40841094824003011802595040d00072781c80324020300f0350f00344c40e0504407206800c44101818079135100b0b50156146d01161141c03880350207101c3c402d003450406101800c021400548513aa0040300a003d24412402008010b03000a016111040212070000c50a03d90990803514251000b401140d11840000c0030114248410b540c000f00c50f600c086000120803411910305105c3e030380c040b10419000300c204030314a8150311846009000003070480760040109000b142c024400c2d03001c080c140c2c012880f2401d8505210307070040c4000329445040f20440c0c5940700030940c004d15544001c071000400035980041da1041c0d00b41642c206540081965903080c1d0500b005407005d008a039817020b094000e600c46 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 499313075 1250 499311825 499311859
    0xa0f090801050f0a0f09020a0b0307050409020412110102030f0301030b10210308062b03020322241704020102011107030207090c0f09060e1309110a2111 67
    0x40502642d0384003c104a01c0c10030403101d83c240c4045042d10b50149181203041d03030150317581200345030880300c04a2206d545d030340303d00104030344c184596008044a107000260009004d1110942c01403aa070140c2d01e800d01d0260088012a12403003605000701c03403800d0a10062011454070200190440f51303400c034146489540784001050300d0020422400d042880c0d00c50a420306400c0b00507154403070070481d04940c0d6101c00308404004101080c028095030240c0310b0074042054000c00071514051801e820b806e000d0740c0201c0d2020044881c6000d1a00d03030396401c600951080d01da15074405d103041c03190f03100d9840c010360b000040c107a0b8000080c42681190341b900501c50714581420001c0c0b04050007a405000207a06180c804400d8488503582c901c200400100f011000ea603100300c0000c2034031268a040d113400756000001a0b007050328031811004c4103180050003820885082e10301c400f8460f06691280c041507886248000f4146941c11030400102050300e41400110711403046942880c0040c1100034002e2001c2c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 499314325 1250 499313075 499313081
    0x307051309150902130303051b011e1a010e040c0c080a09090e0312070f02010603050303010609060e01020a120c081201080105060109140f271f0f03080a0f090801 71
    0x440703400c0c1c1603a140c11a810008500d914800581054041585004540d00106819002a10020303080050120700b00790006222407210420020000080c80b400c0080c1c2c2c0d803001c1c544400300b990880b240c64815402c40510110711198a1842c05071500514850108c0c280f1000c1d0a141407030300100421021140c00140000b805465400c20304d40d9007426450418800b8400c46a84403040c070307001d600c01e00010001d200c002c80007613030203006440d260404900c005410b074058602500014020b020220010036101d82c000c0f48a021201780d0340d00c0441904171107006a0300c40162402c0509020340c5070109915030707800350361000421807043c14658a0710004040c03114001c1d1082c2c0003071f00181d4450040c01125031344100d02101800c1114207504c2400140030001c2c1c83c1ca107400c5100c5000748000e12501e80c04102e000e40b144070203141d020000710240f030030100d5520a4031401b031124003150310b440d10105554000210f104103481c0d000070f41d945080e981d50020b903003080c0800901c07000c2080080c80401c0c0d49000380 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 499315575 1250 499314325 499314329
    0x10f0e0a020d11040f0807122402070308070801171e0705040f020c010b0613030618080d0c021905031e0f07050703020307270c1107140907030204061403070513 70
    0x255010f40326420844c203201c4d04507244d441080c4130360001a00b403044d808c80800e8410410b9000758a00c002400081407810071403060000a4940ca101054400a1641004010b80704440c182e0320010740d82c0c0c07a2140c40049212541c40340203254803062011800e00d40f00d00c2011a010050001c892401d5076400005058a1898091103002a000300f000720114000b40182c441d101c000301e5106061005403c50b000c40070555200181402d42c441d10515410ad003040a403100007504400160f0390346c003603c55407002030022241004014460549201c4242050400c1d82c0192588400514074000740e00003070f5003e0826114804013841010005801140300310380042030100c0c8608041c1021500d54010541403010f9540003900341c02044040e40381034903501c6c6240c40310380c003810000240070725902c0041740c00d1400d0030502c8a6a216084010130f0701e103489507450182e1402140c1303001d15030740d03001001c0302030b405548511004281c050603a00c50800101016503480186841c0c01070400c0808250714503006500d0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 499316825 1250 499315575 499315601
    0x203070201200f0f100506011d0d06020304030314070207050d030c060b0901081c020c0604030605090c1c02090a0b0a17030708040e0610090303021b120a0b06100206010f0e0a020d 78
    0x3c502d0307131203000c10a2008031314107006554100024603001c0c0c000317442c48a0200000c081140d601c4401d0800c1d83c0d0b80d80041202942001c411500c0740b6043ca800b400a141011800440400001c00504003a00c00203503c0d00f0b4075006040350402c80c078244e9065500e2522007000321221621140350202585518501900030800c450080002c5418594040d607850022070400045401500350103046840f0300781100d0440e0740c0003100060b960b50300480281440c0300070300e0307040e80700c5180400726458400d074500c01100c079802154502d00503180e0b000004201e03030190300e8035a0000100c6108001012041c1c440056491140050302c1c03610610359180c501c503038480c0e0003503040c4000d00014060541003154003034000d60818240491028110349000c0c1d5161107030242401124002d0001c0c10841d260400320250440c00d2000729000820213141a5442c4007046031307050b0041c48203406040c00e1910000341d2504032002a0b914281d01402c20080d079a44000003813070003048079020402104543c0852043c502e0110700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 499318075 1250 499316825 499316833
    0x12030f0b100203280c0f050c0907030f0f050f010e180f06100e09060a050a0209030313030204180b070f0516050a0b060109030317040309120503090901150203070201200f 74
    0x6a002c10422000c8584810b02d86802d800c40009001904030040c0c402c2c00346c02100700c02070b1000300d26144d17203411010041345801c1140e00003804901905508000c0292801020601182c3c00030a681d1003141c40031941d220b40c00c50011b00400600522551440d081981100300c20102c160503030981d49442c2030380495404039805a020049039000c088500000341403260b4a00860307003002c0d46aa5903404024003240101ca030317500082600c80c221641100c00381080a02541d840d100c0c40282ca0068111903c000d034003131400d016000640d000603080c154801503100c1c41c000560b0b00c49690072100d41002c0741071f40e01404000c11550104211180d420407905108100a0640741014545903601c3e80003e407206042c008403600a01c00281c00c010000755034141a80070248513a11410201d1310030940e61b0060b800c0c0d0318001d8410713052040100007030001c04402d843c040540c3e6030320000d1120704403880b42802d005800c1400302ca801980714002c042020300c84c2c0c98030441c1c802c0d403406a9a04000c0705004503d01d80e80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 499319325 1250 499318075 499318087
    0x160b01081209090402040b030c0a06030203040605160f030203040204020906040308030613230405071a0c060615040b07021f020f011515180306020a050307170412030f0b100203 77
    0x84100480c0703403900e404880039820311a0030004a0314070700c40900000d01c52a110342100e0b403d0786040024040b000300083c10403123095a5170101a00a45c003d84083d91500d082000060408605000750a50624196220403030400c40076002c90082d000640101d80c819020404400180d03584400740016500032000160341c0e0074180c0401c030640800d1080405424145200c1c1e428100119006903600100c00240800940e02c2d0f15086041c080c19400141003805148201c04007030401c000170f03050048000c0211051278841e0810800d24841c03019141c03001c881d0800050001a88040c054004144040c0100c8000c20302c42044d08403544130300051000503403004e542c0c40d03e411802d000f814011003011507a0f80d50503003061a103028002a10481800740b12003030500b0304041d03c00e2a0741c0d0008540202007191075412007040104242e01c1600c9480c0041d50700041c4c090101961220743d4043c562009601d492000105402c3c0c0c0941002041803112555640380c2a0326900c54025028648002c4d43c0916a108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 499320575 1250 499319325 499319339
    0xc07091a0109140f0409120206040c170604030e0418060b030c01080907030201030c0507140c010e1815030f15100803030f190605100c020301050a18080f160b01 70
    0xe103558001410001c1d011030030841810900003100d910a02035505a110800d18800300b0080e2500120081c00f5183c0620f940381d0183d03010680c240140c0c45554010851640c980a038150302d02d1109000300d06030018808503001034000c80c0402000c074000742002c80ca10700305d01c02d412034406008506680b565141c011402c2d00e40303000c1c0711f1500700c1e21003402c048a05042042c0440ea0328940d50100906069480241041c594021760950711440d0b030190192101220000540751590342085400303011840880ea800400c0c504128070240901405211301c80f940d8607451207500c0c003984510140e82500540c200303241d45006c240300081d4000740c107104c414038034103007003680c0380c1d00e0b203002d42c0b05001981044c414045011094001c90780c1200d41c000340c62015425428080713000b44401c0e0b018550110300705194820040d004040c142c1a07e008400030001c9582d401040826980d24080481910344503a40000001d83c03a8401f80503848400700c0703220704000c00e1620b01c00002e015064191803c01c40c66004108030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 499321825 1250 499320575 499320611
    0xb0306040b1c03020a1104090f0f05030714100f020c100528060f0f050303030426161202010606020703020d0c08030c0717210d0906020301270c050304030f050c0709 72
    0x31b400181e070304110b1060b554499100d50b0f540c2c4007000b000071110b8009842417280400543d1509900090038800601008051540e55850759008d41401802c20007603441c3e40302e0074403d441c4010500009804d40c03541202c2000c001b0030006084c140c00704a4406c45400c1c20140c0c1607010f1320b00b201070f980000d580d414404070264035042503020a03410107204109010356107011090380d401ca0352182d00c10003600341c05114490400301100641c0255600803c0d00300c0d000e4199400c98074064060018150000c0d03548030300300d0980b4200c0c019100968840402080107080c9048141d1105002d60b10000b1041d40300c1541c94195806050f104409610001091201da410303600c3c90b202c60301414009103040e4140481c0b0007900344102c640041008400704050707004480c10303048110519804581195a90303101c0c1c03066041d0b5100350040007090381e90950505c0381c544a81c0b00341d403000c0c41140c030707420305642c0c840e50126880010300c001001048420720044240c40020003100001c0e10000001141c041c0d2009071150203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 499323075 1250 499321825 499321853
    0xa23040b06070f1722031a0420010210020c010e060c04140411070204060305031b060114090916060e101701170312011404050903040b0306040b1c03020a 67
    0xc145000c004140004500350031044401d81d04c06071004401990380c501802d28041c414010782c85820403180110070014101d03d0b40280c0340b1030b100b101c0d0314034a400c540c03c00404040760000d1042d9000e8000c4142105040b41d81890303010140b04480316450300344030000587e0011410b250082c0e4552170b0781021420284100c652180400307a00c036043c135103000c0c1c2d04010707040720080c1607000701d507642903012452100d4821102d213940c0192050100c16902d103021031384c0354040f481e800d8401c0c210703007500440311501040b2241200e05084c00d03c2d00c0303000c51408000152401920740c084c81e00c20412a003000510700c6810f04010520f580360040401d01000600c10b1030703400d001d0f040c0100800c0c00341592810141c0380c0340e40d05582140c010004410203902040f469441541e48a94500036148000240c46403030801462400b5415a8144140e48454080d1a035a0060380900e03103100e042880050f000d402c1c290301201908900801d5030309103c515422280b0310b901c1131042500140c014003000c00602180d1148801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 499324325 1250 499323075 499323079
    0x90816030f020f10051009140105041d0a15060f06020303070311250507091103011805010503190206040e011d010806070c140f0601121403070b01090b0a23040b 70
    0x440f8609400e01c949034540e258103003800e6540d40d000301d8030b80c0307006149a00c00740541030001c011700c4c14403050f00c2e145001d091050b075100d20b0621550390380ea0881f4001c10b1004210080040560500c107941c1c045d03012106144a0785016070380c420000c1ea8502142280c0024030164016640e079091414000701501c02000c10b50300c00110411000b07842180d01c0414217652103080e601e503041c05490340707002c500b0004c180c0d0007200e81a0428281d200003000c400000c504850900c50054080010340d02020300b95282442240e6044e007040301c20b0001030300c40359001020319100908152425841e625080e07c42d070720a80080818000c02281004083d5540d880d071405800084028601841d2a000083c140001c00400134448260100c1d811030000c0c0c2080400c07080300919054034415078452074041450700e81060165201a041e6031510a40f01c1d01204130741c605500b010840d0318980c201111000640107600d0941c0e00309013541c2c0d002480504002012701c0400c81c109440ba1004c103c07400304800d5070355040c0014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 499325575 1250 499324325 499324333
    0xf0a0f0905010c0c060f031b0e0307080a050616020309060d05040227010b090f0312090306010b040b040303050c0a0c0e0618090307230307120906020d0906030f090816030f02 76
    0xd00032604c030050010031600280340500d0030440038070341100a00700000618505803101889131500d42d80200e030122a107003095040b115110354444049581c1c002d003041c0506103401c5200411400300651164000030756007070040ba89080700721400302d242d80c0d01c034040c03107403c5907991014041189803003404406540e06800820400011102100c0804201846a40c01e000c0000903d460240c03140d002d00c001c0d103031006040e5010701a164031442402c2c1d1105400c10310038040d05c0d002141d00c40901055800790784c1e000c40600d0415045617401e403150703409070303108020342d1080798100800908102142c201034908464a4041420050144500210072600041503040401d040090384107002056401003a00314821a0b80c40c0408400421200100b62000b80903020010b41203042c030a2010b07030f6000071403890b46e0300c59510f96600b404a0b1074540d402d8024000a14040c000c208251081d000300100c5c82000c240000c0c84889a6031700212648142e00d5034404010302c509070030506070850300851046200d40050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 499326825 1250 499325575 499325597
    0x70e0a0b0901060e1207030f0519120c060e060a0911061204110607050601060206060901120206091201020405101107120305030a050702030d0e0a060c09050d170f0a0f090501 76
    0x2800c107101400307200308125041c0070802c0b003503031000d038001700118101e010b8642c06510783c00d10415140c0e281c0c1092350240301b9000040c0c11818254000324096030000f440404a0600320405c40c0c0d000e5280d0020b403121a01c9840140c2c0841040c00080c0c050081c20030300280704045454618480c14044031510300ca00da090085009c07001541c07007150781c401d621101010401c02000d000031454020045e0150561046000210f02c0c17079000030b040c40c09840c4c1182c410080c1ea90380e00301d81c01e003066205002074001c40207102249c03150030014500314803001408009030600340c441c4042800500d4407181b03403002540190309511031920500c40e040c007030640300040d1700c2c46d40c01703076200a0860f200260403080b00b5a038900c0003443c098401e20030380300b000203200c40610865100200c01603481c01981c906441c031340e04d84a10000142c0c000d03095a011140b01400701c055400c7d054550606100d0707a9038031080b40d400108554003800000c00e0003003810031446d80301c0309041070b2840d80003440800070390411410f1124001007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 499328075 1250 499326825 499326829
    0x1503010b0a030f020409060e07030501050f130e070324050108032803060f0609030b061002100b0a050d0503040315060807050d02010e13020a0210140a0b060708070302070e0a0b 77
    0x807038907031071a0740c240828540600002c1d20001c1c07141e0b92102102504d410008113240c60f004001502901a954082c050340e62620200f020301040d2a01a0741e02521a50400c1a40402d98000340a607541c2c01090b10321299407525181040c054120720907a68840042c903280401901b446810b014200d0003000f1420300d402d04140613030b11541048a42c0d0003a05007030510982900c240c0022000c0c0c10114a031081441e0b03540b00141101c5c50034003044400201c641d0006000c4c2c01c1810449045030500c0c2c0c01841103038910851500105008909035400c00020000401c1c3c50b1228102220340f244200c00a5665a145d0308083c202201d10780d1215810500700700301000b00c400b0010f03810050701c0b400c4400c80201c80032840141c50b4003d154407516080015a41e03200340041c42ea60240610602c240c0a5070100c0c03107081c17400c03421100c00000c24010703000d052001c203407044696417140c0b5503401e0140c0860310b0044c0307580310101c0079007248004900581c0910b0702408505c1e030b014441c1e500203039800d00034001c08c3c4601d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 499329325 1250 499328075 499328077
    0xf060418050a0b040f120f030f020a02210d05130b060a0605040302062a070e1b07110d02060c010f110c0a1b050a080a0c0608010f090504061d0c1503010b 67
    0xc0054280f112060201d41403119680318904480c5e40711805207124004180c01802c2c1290700d000c480301003031908a080c09800000e000300c0e4116542640681544440c1d010062078000450003000c0380c401701032000056110b928032815010340d28520200030005a41d180070b201144004020501420100c40100b2900c1d4011064034249c0b9812074450b0307241c002c0071400b10049403c0341c64a00c0801c841183c48100300380003013159010786071101503d06496a40301c50240c10b02110800c03c0e0a003010030080304c03022510440801d50401001000300103030500c41d4000030340503002800016074a0359603400c2d0070216182441303a010000f4020b5005410301d46e4148100761644245100600940c10001c12041a00c43c08a07914020f49001080e1180307180d01c814402d95103486c502c0c01200d01c0d9000050200d1250b014407502c504030f44004d800027081d903040480f41c4c0c3c0a0000034100b110010303207990307140034000c2070143c1060b45824008000c21441c50707040e00304460b21a652095010b070440400042c404810004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 499330575 1250 499329325 499329343
    0x106080c1908032502100806010f0305060f060c03130611211b010b06030c040303030e06040203190510050a0b0108150a17030c0703050f210409091401050f06041805 72
    0x80010084c04404a40d28a07507a1280c0340c1c001e5003c511040c00407281e50b00100c00c1402030324280d0f01e4035405480341d402a41198015145181c1c4426503401d06c504ca460190010400f82e003c58040e00e00f00400030050300041d40180e0081804a04003501003400180d0401c003145481e140041041882a60021a00300512506048035000154035101c550360240c01d4004101d0080c015001607aa0b00d040300245034aa001800b04a00103418111000150480060094016a001030240c4203030380c090108103080c0ea18a9004039210f007d41d0100148110552003168400d001c0003101003411007090000600c4140d0003070801002030b44418522000752aa100004203403500e04503c07041d05100340ca400c41c50341c0220141c0014034407030350300003000b084408102d4012205200341100c40c2c484420b00c00030203040300d591480081d0134090204000320b282c6a08400090385c0135105c1d15040e101c01d0344080d404c1d03481c00c46480307180d20301d10014004a0304142c4140c0e1403040c84449202e51011480d910103480360011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 499331825 1250 499330575 499330597
    0xd020102031b072603061e100807230d0f0c1e17090d090f0b030408132d09021312110607060506100801031505180106080c190803 57
    0x208900c020450300d402e00103000d40700321084c04200400d00801e20b401d90b00481e91180560210404580b0076034181140c0122210300625005003040002c804a51001004203020104010115200c05000e0004214030502403c4400c20355107600300f480d0502510303a014071007656145003c132400111a4091a486114101d40d0f045c410003040491040b1072603010124418656003500e400d0044090740059070402c41092a201c1b941926a40c084000b515202c510030b19070016030410005000a28000040c0340c0110341b001d0600946441300000e941300b00f813000c004580b01c2054081c182c6141e9030780e188000107040000095141c480303041075141021065105400d00c0a01d00e00030042041150445036240410190442d500c2c0c4000d41040c1029280035207810340603140401503030f04450320417190181a80e4214010042c00e4400300244401068000c215032201114240030748601b1400b80614402000740b84010311440d000e500c1006409032140c40072580c41c82d580101044052008015201240c1407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 499333075 1250 499331825 499331827
    0x30627010e0c0a1b020f040f0f0b0306010501020a14150a0c08060a06020307062309060f130206160309030203071e051008060913080a081608041112120a0804050d020102031b 76
    0x481e1000c20300d490116019940c1c040c0c00c000d85023044000e02e0340b250300d540e0525103050200310006d0040c90348070f40007802002e00603003004a4403008501504038145c1420701c00400c03101601101a500329443d076090b02e503400c0c83e580f943c0e030500c481030740b0111003a046201110366100e5549440c0c00a0b583c3c0c496084000d207055110309004c0040d0250100000c0c84030b03a009000225460020000fa85401d001c032142781180306214049080c2501900308074181a0b0302a010074907002032018101d4080013000d40450800c0010790700400180c0301804030340002c203a0340607552320000c0c001c02e9503011004190400ca00519803074840024090b440000303160002e03000d03103c01550b503c4640e403240391405003000c05401d281c000549495280c1d4010b030001d00c24500360301840610170065000712030444064402034016104c001d10703142d03180f50011810320030f004042d08440000380c219070b000361950442c0d1000008124410b0400091100c01d10100f030b0a1509071000f1480c1d40303403810140c685500e00381e81c0c0201e0703420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 499334325 1250 499333075 499333127
    0xc0a0b031306060504050c0a1205100308030901020c0f0f010b01021507080919030e090c0c2d10060503060108070f12080d020d050103151808030627010e0c0a 69
    0x105076120401421380a8400c1c001ca24088072010400d0380002890310000709820305940402002c0d100303450044100d0072196882c50b01d1900e62010384e42001e040100070395403c1041203440b071001c2142c00604004003010740444d2400b001072a00316100700d01c80c64155080101d240c841864020780b40b551080a905210b995502c44200309460849003407002c001c0d4480820150b01410b400420003468402c0c110742a0801d035032109403001140c01040d500c90a0303a80300c1c0d00c1804070141200c07280c58010a46402c043e104807942e1000c1407401307600c40310a008075070b61686c0c180302d6418203101c83d5000d03120343c4000b086460300d4090344800411051145040004450742480200440102100c100117103408080d51140004000d000050200780b004950590009207440c0400b003150182ca0440e419558642001c0c03900c43c0c0f00c000d00e43e400102042d90151800c00d4001d107540804c0d5003a40441e90303405485103a903042c0821144404000782130443d4002d424004641c155901910407002020240040d4017080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 499335575 1250 499334325 499334333
    0x15080a0314070f0210030f0b06070f0b1b0427090b0127021c060602011a1504030605040507031a150d020301110415030b0604060e012607050c0c0a0b0313 67
    0x880024000354014070304a4000c3c10181d241d040107032400c4011f03401308200b034081401c100c80c1d445019001800c42e030389121300c50080b50700200055400403008207c40440364507040518219401900403003480c0c4032411a840c0445c2c680c1c1f110a0840520034020443c500281c0c03240101c0c10014400c195442d480c8018611f03103800b550a4520380000351324425502d0f01d405440094100440e1a01e040741c403458210000baa9501c14044d02d02413400000301d54a00f0b808403c1803000351f500a00c082030311002c2c104000000607090f480f0307140c401e500a4000d8801c4c6415883c0c20741030a4101d44c0100001e20801c070600240150032041903040000445910328540101c2c40400e000d40703100b82d5114100c4ea804180054402c0c08080c41c810092076139a030402c0034003103420810030b050160303000d200300203944000c005002c0e50052030301240d8030b0141c9102646044020003c10fa402004076018400103001095a1224000400c00540580c208039145540e4504155044600b80402080c103141c0c0c01c2d141350703c01e01b88 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 499336825 1250 499335575 499335593
    0xc090512010e030d09060c08011a1305100203070b13020a09021c05090d021608060a052e0e160221070c1d070504060504141c0615080a031407 62
    0x7640b074500350703922800d6041e0000300030a404441942c5250600401c840014800d2854a058406030b42d240141480854103044c00742c0c00a0000c0c1c80007041e42c07003000c5115a00e55503100384000c4150700843d5249524134011440283c040c11416400c6811507000c001030380c0e200596800d840000781300503281ca181304900304d00d104640e100e0718401072502041c041d0041001c41c80d050350485580846905800001c060051280d8902c00d40490b600600c0100e00070440750f4000740d400000c003101104110081c5040007000d042021114101c05808210420444000522056104101e40c4054400125101d40a03449145d400800c04090815403c0d02034405603020945c4c48541d0032803c44c00841c0e485984103180c40b06d032403072880d0191850700d000820441c8504211015500e250b075415051514140d62400a61100a40d55a1005480040e0492401c00c0d07000d600341c0e00c0c0507103c0450180e03401040309210070800e4000a0b4240c200c0207507003000ca900007481203100c50f8184503556840d070721820f0014003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 499338075 1250 499336825 499336841
    0xf1d0604050d1101020606032b20070e0a062409120c050f030115140409060507030b01030b011b080903030f0a0c03020f15040f050c150403060506040c09051201 70
    0x7020000702c018100344a0044054620324000f82c08440c107503214030080660f0340040c25859060003511190300c0c4d0554445000640d021402d074107080c4560030b2000e440a81041c29071040c0b5000303501040003040300d00c142c44034081e00a003058104000b00b0742040381c1d10b906c00c0640800b03403c0c0030201c0c07001181d100e4860400f4078024100b072440784901442c03624000d01d0050a83c482d25208500410071807000c0e01e41031040380c5a0302d040340d06403209079142c00d0040c00795036501c03062158425941c1801101095560003000e200d0304c420341d400520312202d0310003d03040b14071000a150402c8000d203007200c0002008031881d07810a4010030b03030350f880c4c81240c030029182d4840c42c909501551004104007003001c3e000800123051a12a4003940d0346140c985610998032414440050941e100c420082404035010107e540080e41c09141500c1100100b1808114007841e806402d240541c0e0005040007884910b20a80342c200d0380c215004d0080c2c18100c01c000303240c00110b006480c800c00010310041c07a43c840035404904 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 499339325 1250 499338075 499338079
    0xb010e160f0210110c060a050c030402131103181e03180d0609030801050a08030901050405060711030601270e0d030b130614041103060904060b030111030a0501150f1d060405 76
    0x4c44c240d00d00701c4000ba41060480102901c02d400102d4640c0d461801411721a07403500780010308654a540070032074000c10040c00540039950302d81100c0c030081c001100940c85800c400d00b2120109070307803c50080c0b42040c4241150004802a459010307014000300441c3d40c0040d00d042032410151b100c000044c500d03490f8001c024085e034903140a81c820107802c0031146048032000c40350700140035510b41c281c0e5124810f00281078006101000240302d01d00c0c0100107008568044c10b0b0035481001c400001c2440c203802a046010105680d264001c7d141010399105031501812039803c7c4410000c04404d02e40d507008241e200e038189511178205900940b00c0d515119842c0d609890280106030351032001201c00d00e4610b031a1b9010b503003001040c40c08000c4080840340103a8001d400c4000540d15500d6082c001c0c60030b0150294195200d81e400081d4060a901440c0941000c3c500059594034200d030100e440c0240c0307503e480c10b1000c0c100f88649102c0d08100560084c840b201c0c412111141700200186c52403003a034100c55 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 499340575 1250 499339325 499339331
    0x2030915071715150309011505062b060b0d050108010e012a1707050c120901050904152d06020c0d121806030b09070e1309111503040b010e160f0210 65
    0x11200105400508d181c1c0514810622425210350a2008510a1007403181c0c02c0594155102c031004010400311985c616040400528a511000200d02640c0b18258030142c1580390401445401070a110b110110000d60b402008410302059000860640300a10015200f00e000815640940290101c00c0c62210145000745c0e01d1134200f0300502a50000c3c0b000c4100c0307101d124010881105041c0880d0b030b0b0140142c440720700305903c1c3c401f04006800e43c145c101040704502c00d400a01e10056581c0c0408403e2200b05203900800501040020764096034040c000b1075008125600c400d88580c0c81c40e6100ca43c10441070705c2d83c021000010398510301ca00840f4080c0f2030f1801710011380907606502000d075420701240e2034580342d25900ca048413007411160003241e0091403445115503240c2d1070b50100e1003061284038070004082950001030800000c41003e40340700302000041208020100c1a27150240144202d110503a061440900303100c03940481d00f460600c0300000b03888419900801c01e414120402ca8424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 499341825 1250 499340575 499340581
    0x108091e0307021801030b0a0903050409090f020310140604060e0c033304150513020a0306180e0f0318120a0c23040b10030519020309150717151503 65
    0x2000702034001b44015900d048410010403d034000300e000f8a54110380550340c0c1d07400c1c01e080c01c0301c100041c59091411181480031280800043e1003d100001c0d10702d00070a0b0000e11410601304500840400502c960b01c21480d0480034448001d5081001da000881d100600e512956180101410354500e4585200490703401030545233451030020310510040026074042c001c5d41403100300102079040030300800340e20060110402d142c3c0340c002d5020f0a0011200d190100740380d9940c04000d507010f04515001403020340c440000703014032041088032141072001c0c540110724003082481a0301c0d00b10031009101d03120307090b100c000e07072080f54042020002c0c1d1500900140c015965842d004141c0e81c1e0008803c030300c030304211078007000c103442c141c8030b50950384401816500303034020603800440c01002c00030003c2e04128040000041070b65401d1003d9841071940e50001e0050340d42d144450000c003000140407108000314403818085102d0710a1045401c00a0311400c02400010304002441a00016041c0c0002082c08420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 499343075 1250 499341825 499341859
    0x902030a1e0213150302040b0316090b03160503060a081e0c0102070501090513020c0601080d0207050901032301110708130b0301121106070c12020a050108091e030702 73
    0x110340c0104a420020500c0708000c01d003010180e0151058a040c0c19518240401c80c034a4a5004070b690300d240c0349030040c41c103522581d100c2520780051b51581120020190038603055600820060003420803500320a080d4a8a0b0409000025902c2c4c0c51204220010000c911151a146c60000240100f1000d031760b00700d901901413034041a45040410003510039a82c480c981741d400402c50005840040c1e4500c44150b0500341802900a00c400c14141c03401d45c2001908e08042c001c2c402203018066081c00b400445444180081c5031000e02c1e00301611507040d8000400c001406401302c0e001c1c0f81c480a1050414042d9640814010401002c1d181449000091320204000c0c07282d00422260005d0078404083c5600c0300740e8202680030900420400c07100c0f1011050100e009401c1500b0f03030820042c1420300d0308200303a072072940c0c2007116446424416142e4051404501c4d001c4a483c0c05803500b03181074026407603e909540e644036050781c02510f64031004141169140d000b44125000e5503000b0f0032208003030707500c680 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 499344325 1250 499343075 499343081
    0x90d0e01200c1807020709181217150a180609150e0f04050a0212070f0608090c011e05090f0406030f020321070b091c03051014030d0c0201090902030a 66
    0x2003082c07083c54403801c103940b0311000c0c001d00c034011a4a03500800d00341e400c224500000700086018100f07000c1c4844000000203200359400c2c58046010740d01e0310340350070140b494080401e0300034100148042851140205607100c281e04075040b03402152112480d950107044203801040c4580040e400c00d400d0952800071800808481c0080398805402c0b50410ba4804a010350191825a0002c0c1190000f0039928098900010b554030b00089a0041da00c1007aa00d1964440b0110154000350105610100f0084864024001d501c01c07540207003409042840c1c03600000da40080c00c08103150521401184035038031900d581030074140d43d6030080c20805c4003035207034148109548041d142c00c0f8880d204400d071399a10305c6d80f90440da085843c1508812401e0020f25600c6d201e50f0079004003005400e00c00d00c039580c0030480300320409004151198800107103508100c0c0c44101d0ba11207c0c1c1000c149181c3c1407071584400d13140016000d0f048141c078580000c1402c0c42d0300c01210801980d074004046580080240482c99000354 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 499345575 1250 499344325 499344343
    0xd030f03021e0301050f0604030c091d0105070f080f0f0610120e100507021b0d0f05060711010b0a23040207020d05010506010314060303031b090301140f0906090d0e0120 74
    0x1505006c1d82d09503001041040d1003540401051036014610030465139249401c10480c600c4a6404011000d001031591400c54078105c07004070001d800103501001c6e99810116584d046002c04100708007a01d03201003000303400c01026014074000e11071200003102c45807040d41c503004240050300041c4002100030503010ba44078800022108503510b0840840c03030745400010000c1c0040070716040307008480e111000700700c00112020010b480c0215407244501c00100184801482051182c4500148107081c0c0b40003070071608846003007806203180742800e00051003801881880500380d40c02e10700103402c0030000326003e07000720000250000f06190180d000c100042d00414481d48081c1c0c1c0811a0300e0900360084e40c1d0b81c0f0195981ea030141c00c204041254036140180f0446070072010011686020f034140082400c48441ca10001158900c03003090041c049036440003113030031265800061126003000b034132a42e01d4400401100041c05031a42502030542d0096110030480e4240c0d00400200c8912482d4241c0c50714650 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 499346825 1250 499345575 499345579
    0x70f091707080d11070611070f0902070b01140114070c0806010b03071b020d0201050304020414010b1b060403051210030c0303030b030d09030503250506040f0b0906060d030f03021e030105 82
    0x1903404080101d101d061003507909050003000300040c40c078007802501c104100072900300e62800b0700300c4007040920021107001c0040c62ba000d0016940d14050a00481e6405c3c1070304480011040c818102001d0703070f880fa56080c51a100c40802642c1c0703008510304800c0c240d0300d591005065000d280c0000410b001a03a015503ca2990b6890321200031181580d0b05084140c0e00000039400344000600d40059446640030b103501c5440030b00001a0407001101c5002124800d1340708008103600041d003005403025012004445051583c02050607007029034001c5c20a00554100030b1029910100080d072050174600c00c4001160080482c500b80e68903424010098600e10680780d000b0300c60800325900740c074800ea1401c8100c0742c10101031030610403010704180240d200d07140018560a002d61071038002ca01c051001e2401070f440f42510b44401c4e491882c01510360103006082001540005041243c00d48442d00e9000c00c2d03982c540751906008a9070202a8024040c0350214060750030740d4005c541c40c100c8940d0081d8140c44003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 499348075 1250 499346825 499346833
    0x1e1f08010e040312020c010f0603050c031203101217071208060609101202040b1207020d1e03050c0c0a0506071e0e040e1e03040f05040e06070f09170708 67
    0x201c03074003000980800d030b0380100080e5030300303e01c40300e01855a809481e084010f2400891203410301082da40c2030301da50760001c2c2c480350003c24400e4880d2604201c0c100070301007118007444c11031810b0800c111035044c80d071050340d00c2080710860902c03c00511094240849417900e481c80e8079503960b810040c42101c0b8109100c40416402804607040d486c05c80150b61400b8001010150401051300003100d0110020071180c0085070248000710381200d40308050711076055128905001d40c40d240030700a150203a0882c01009012000f60704a9251030608024601d841080c1400308450f11401c505803450311811803101101e000b050000010130201055050003400c00307541c0e00039803880c001c04282c8040c13140b500e010003080c10705003a184142082e8000c4504034034070748103840d400880384030b0701240001d00c2c036860b410030380000074203002c02120310231800090712042d00d00300301c0341c4100e42c00c641e99a407000d4507500600c81c0c4020940f401521a9090102814680c8c6528000b140303c2c5500c25a00e030301c03a002c4d419031406 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 499349325 1250 499348075 499348079
    0x5010512030d0903091802030f0115091401230705010c0509010c02010813052e06030c0504020d0f020d0903200601031e1e02040c0206060109051e1f0801 67
    0x361698602038000e4400300550319110884500c0340050454050440c1840080c0308001a41e158619031503000c054001c07405030b035914081905070034000c0141c012001500769140c0b08659598000807000a031400d22010201499410006903420301003c0300c142074040b0074100071443c88a000c0081c04405214800a003c031014550041e503150040c850ba05000a450045080166201303201da10780140e182540b0a421041c2a241c950819800e035140ba00301c162001107110242c1011201c020044c50707032050400105007035507030f441302c43e0300c05c1c1c45018400c03600424900b000420365840b03c210f8248003401150f03a80d0007c01160042c0800d01c00650105d40410f400c03d0044800c4941081c64011003c0a880703d07030b007190396103041c050111a0030505112403c0d04000041c01d440c031800d504840700034207503440003481c0c8108026165048611402c542042c03003803203100d90700b224604050312800c8444801c0010a0350880058800e4090450343c4034040c001d41804412145d000c1d68400041d44e959641c881c2e07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 499350575 1250 499349325 499349329
    0x6030a060801420e090d020d090f03082503021c080408030f190510210c15210203072309040c17070e0102010f0e100207170a05030109050105 62
    0x582d030315209456040c0d4507410305141c03242060090f801c603d89000404480c80e19501e4068018408458a0086034070030b00c4c01c500e0542d010000190502d132145480384406041c07140c00c0422800c98440105510300100b90030103003940c2c0110103407085401c40004400048a428000e40c0c541c0584940d00b0b0078058121480c03107a5209a03039052140b50021602461601c520901d103c100500070521489007802882d10120700c0d0050145500030b4001590000c0028100365050314401c101e001e41901c0e813010034070f0040002d540e011035082212003588007210181e03020141074414001c04040d1840c20745000030b0810740b044460340034600640c00c41d9a21100240f0050790510701d010105011201148103010400d034614094100c1c2840c071409282000c03241458807143c5440681c2580c448000c0f500c002e10b40025540d092081800c0d00a25500074404020454a000c0d22030404011242000d6000510342c424070a224a20781d9989074028030140c0d030341041c00c8004020780c02c20301401c82d0260030070380001254 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 499351825 1250 499350575 499350611
    0xb040b0c070309031403040b04030c1809030e0d0212030a080a1a03060c07080d05010311030610140d0206130f0603230c160c0b0c0609060c0406051806030a060801 71
    0x1c550603100c84001604640701c81d800380400c101600312510040102140103c65800900015440740080c40215400c100d9050703216001d200f10210b22524002c0c1c044082079004400f00c3c800c41e000d94440e0060720b000c1c0041194008003070000e104c42d1000040d1180c1c00d07940440190f100c0c800040c3c0411114609940100750480081d0312140c1c103510802c04200c0d034070303e0312000b00041880b50b450640340c481e00c41c07001d1060780c8090b441075480342034101100056080601110354030540f200d08140481e41040d100c00f0103660030b0802c003800341080014410031515640102d9a0f0444042e060b04070071607852452600d18031603402000300090421200d400d040301c14120504518102442d002c10507a40e6804c034640b55044101042481c403c1007292001007914010314401901c003e2034100e0f0b1300c444041c0b05515241000e40340c41003590016041141205200003500e0554005107405075441340c803080c545400031901495950f100c80000240310541580d40e1101007280c00303100007400291241401403140f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 499353075 1250 499351825 499351837
    0x19061208121f0b030103060c0309080a0320070c17030403030503070c0f1a1b070206030105011808010c050a09060509030604020f0127050a05091e13050303040b040b0c 73
    0x25003005100d9414100350410000390711507881c81c02c01100030b241516040c20402d90b5844019402400030050080c000280102c8940c95950b050601c101c82543e40c91080603c01e2104010030103560b2100c2070085114206603608446c007003010383c1c0d2242600d04020300710b0102445150028007079012002c11404000c000c0d6821207030162200c45c00d40d0b0310700c2c1098131840f000200484200e0b281000c001e00240203400c82d500100d00310320f0541c010380b0f00801c1075105d034071003a02040c082800a2100a0050b83c48808036030641f0b000b86424003007941c484080c03000c0c0034201c0d001110700e5424a8105042d8170f81c05400340c40308001c240c1e144904a550742d1016559403240812058243d00300c000054054104841c80e000e800c1018501081c055200c841501d000507580c1d0341200515034100001c000e1494070200580c0585001c0307865030014103006c400001840c01d01d510b050840120b4200103003c95841841e00045076401400362030383c0e8a018644507103800790864086500b0030b06140483c46a60301d5500b42c4007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 499354325 1250 499353075 499353083
    0x23030a080405011404121212200904020f0a050a0e1806100513080303040c090e060106080a0902060414180610122c010b01030b0d0803060a030209190612 67
    0x11401c0d00300700044034801a440038184480c40c00300000179081d8407a40c0b4030300002c1d0003090380000e2944444801409884505082c00311241402c00c1c0b0b81c0c0030085c4140c0705150742001c05025695402e800041006801021001200300002180001d141c58004004104030b9081d50340c0d58408150460820140d02c00d05861342114014440008015051040e2801d03240c0031a82001810440c1c18010808030242c01d810040f125000441840308004041aa00b00500034a6002744106003034041d00a50740c0130148640320420581c000403030000d0416a1040f0401a0040c0031259243d4a07080c0000620340b00300782e42d500444a08145862005c00c80c0f014a0103008010180c100320201400b0440e403c08001301d03c144c40c01c0d5035040c113041070000c00b40c0ca96544011840031031b59401c4511051030841c0c03103400d6028103050905036003080d070740d0705c84042c42e45880c0d2004503181c881d101d402c041885000c2e5500000d42014261041c032080014035018980d01c2940c80c002400016250904070304074224290000f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 499355575 1250 499354325 499354327
    0x306120f020f0316140607080307080709030c0e04110d020a180e070e01030b18060412050c0a0b0a0e0102071709031f090308010510020c01030203090703020a23030a08 73
    0x400011034612220039039900062403a4061091000081d08181041e0400000500845010400103035002c00b100040b00046503c1410f1041e40e84071114148801441d440410528000080c038040c041c04044000e150007410ba051040e4807401180780b0410290303015250400340019407601454039503205000f05a0180425010a107080e590203c1c0d01c0301100404141a29100c049101c001c0401c03604005000240301d0401c1135145003084205000080e00c206e42001d01110000303c41f110006c3d1590300260f12030748200300360107611011655402054401600d070700038654040b00340107460407424040c043c02841041420b641c04d0017a0300700c0c0303d5500000c041040c0001c01c0581741103040d000d4104030401500b80c4100c610030303011141001010003020346007a50799031645001e160313000c3c014502504041d1445100d1000c0c1201c0030b5035641c0c031810f4041c101500040080d60304a81404644004c680c0500400000e1352181c0c0c01810940000302c58440b440c542e00d840e041d17a8540010140d280c650044c1c481 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 499356825 1250 499355575 499355609
    0xf010503010207050a0611040503060415180b010605032707031b030b04020904080f0309010c09090c020a12200109060b1813210c0201020d020c031b040905031b0c010306 74
    0x80d06c00341030341032108120b8030400d000c005031585060000e680b241e80b0456030b80d000400c81e40010300407655503500c407042d840c580303ca00b60b00160003107007102d064844600306151250380702c1040010b01c041e0740b844140e000303500c03041d20325650b0f1340000c6070015680300300e448405000003100caa1600818510000d001e8640308800b04025051400040307030420301852500f0710300206c403034052116900517514102e860395211104004103500c046008007410f080c440a021800921100964801c1c1c840c602a00c4c3d00440c0c00c8400c5007500502031340800b0301c034403410748030445240d00c0d00138000e0551036015580141072031280b82c09440c003401c1d0003000066000c44210307140c54400d0030070122a507030070080365402d1003203900b880d0445620b40580c02060741c1e03a480c1c4c15010081c0c40024100000c00c1001420b65101d40c603411002c1d45d003c181000403414240c500b0000d500f0000019001d400c000034041c203140000100744041100340c9603038010503419501202d603042a40c40c01141102c059100f168030000e03501c509 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 499358075 1250 499356825 499356833
    0x4030b0702100c1715030109050d1b12081e01060c02150f2a1203011811030a020901030b060307050c2a010c02040b0a0b0d0f090c05010f0908010903080f010503010207050a 75
    0x145d40090388003040c0c00201003060b01082c02c603004c1e50781c2035645a00040c025180c8a5209000703113003800380b600e500000841290303542c0364a419000490010321050300c00081400e03004040080304420310340c0030000b0f603517950140030703254005d01d03007007a8000c2d6420030014a4102d0701100b195003480300c0c0b0884503d0500c07407030180840c144001c2d1448186001c40c103000c0070041070030049400c0e22101400b80c16901d51414641140b00440c2c0720100c05c1290405480c071b003400c1400780a03240d1000e0b07114005603590385404012001044200c030000d80c84038010082c8981e10f580b060152001e514202c3c2107070700c03000c4403120f800e0010340329840c0c0c1e031a05000e00483c0031103075228012420005101a01c0450042d9400002070507106071a005803004649c0410707001c403165464081c07440700100e201c1080021607280e03291640e29009a024440c1446041604044c0b42c601c82c01140004240c0c41b00200400403180c90018007818098907518031440742c201c0040341e40d1038184202c4079207952245c01132900d601c0641d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 499359325 1250 499358075 499358117
    0x15081209150c0f031309060e060108180106080a0609050105010e0c03062106070e01090f0b070b0405070506030f0901051e0a111615060902040315050c0f04030b0702100c 74
    0x103030802440c041e00c15401e00703d08081000e0100d004409009103034050404104004683c1c0035803040041c06074076428440766907044442d05800c4491102c00d0345410707851010141c05010503502407900b40c07042c1112001441600d50120044500c0b0750b00078442c0d030f42d0342c0820851040003514032114003001000460b4407450100120111810303802c074001245d400c203682c82820050110340c403102150000201c2034980d82e0100034030740500307015a42c0c40c1701581001c09204042c0150304005010b540d04070f0218040c4101042140c00610008108030f54038504088004880142a03c91540e55801c10010032150b151103c0c08280c4030081060701c0c00c55503111507a800c050f041030114081d0982041101c0c11007010102c0605812601403500d258503a800d50341840704850a81d8800c2c0e080300e1041c84148002154120145081e4001140102c1d00b501d5015201c502485420042c0070794842c00030340001000420b103a0300313104101a07025183e06129460600382a80d40380b074101380014805c031030007048802c1126 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 499360575 1250 499359325 499359337
    0x70305121602090106180e100308071104051f0509060609040f0e0d020a03080a05041115040b040e060405090a03081308070203030f031f080d03090809041508120915 72
    0x1803500744203107030341e008242140c00a0b000340c00001e0701d840010040c0340e40104c00e01c004044c020041c00d02454840c0c4c10108a4445010042140320005241c00510012204844022400a10400246c1402d45c1d19200611800c1c618105021802000081a28180030000d20495001d040c191411442c4405c1000030142603e1104000360f41d00c40c41d03000500100720701201d0b2509070b00244801615801d02501405009100d149094104001c01001815080321103801c0c54017903a8030018961086100c245601503500f01d10180b50300840c00140001d61f5400c4a0302480065034108000d07200c4000d1207859159000004d408608040d021814840380c1c240c0e4064240e00514015003810096400a07045078840842d54002800101c10301c1440000c2100070300e0400e680c4c0b001603081c90f180c215002d17258030b80d219040d024942c0e2030009038180545401269030701c50f0010010170508030b944403001520101800b800010b4031504252058015400b4202c80303100030001d10000c000c600c107800900c1c16074400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 499361825 1250 499360575 499360597
    0x19030f0201080603160605091c110d03110a030903150902150c121801031815020901050d090507151103090d080702060409050f06010807122406030609050907030512 72
    0x455803041105da4000d100009040a542ea00f503031080404100081030300b1210040a1500c8850318440c0000c80d801e140030760071007007a079400b840b083c4039003002e55010881100c117007401d0140380d0700350042603407140140d425240300d8284207450a071340d4411242160041c0718000d420000600c0e8101d0641a14009031040420504c11a40480500c0701c040080e900825105040103d800100c800d00c0e44c1c1602510b0320f520003a981c03100356a915916044088411014216039007640001d810802e80d03c1002150072281d41c42e04107100400789490101ea452000e4070400c154981010345003010701e40303d6481c0391a105c09000c000c60601e0159000c018015568107001c03240c80e241000000016182c110250006001040000516140070518508000b800620315410801d1440c20000d404c0d4200c041042d100d0400140003031030100851b410200754403000c2c3c120401200e1010001082030740754200301c068602c902800d1009413154282e66035a184203001c0208203410206c858003021801d00041d1035284030b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 499363075 1250 499361825 499361833
    0x80706020610080c310902040f0b06031f03210306090606050f03060a05121c0203190e0f0a090c1211040506031e0c0712020705030d050d0f020406050919030f0201080603 74
    0x61040005035100554522800d081d403603600d00c1040d4235144c440d6181da03569004c402e2001851420004500b0720000701800440b26124a030b603480c6111007448400607641c03100e07101130b11107803410680c41142411404840081c0c206031021400040340c1c05048221212921010304007005000800b1454200a0080d500030010150000b0f507a9104480d16000e101d207000a003002040c094000b55045071418407420a561040000d407025201181081c40c95501600e41810300c0c0c0a070314001b8138a032a002a1003070748590700440c04101c1c1c130000c1d4420784c0507001c507031541c40030808025040c0d810b441e039003804400100c070148401c1209007442401150302028915003461540d0600c191603002a07001e0300c4484c00341d00b001c0380c00c004100b0103002c20402f811281c0010034159242c540041e91b01c444040b425805c001c408503940d10f81e8a01a04490707504000007509640711611503000030485c0d04400708691140e00c565101d245260701c007900c1d140c10380342c00c028004100c0d16181c0056400840c003920051301881 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 499364325 1250 499363075 499363129
    0x61606110415020f12030105090415091101170903071b0317070213092f0301060e07080c0c060604020714060a0f06080304060815010216080706020610080c 68
    0x3026000a2014000c40701400d00d9074040900c0091800e0004031180390280c2c000c03c0c180044580080a4030b044400440d010710446d5074078600031031041a20083c081c44607007440c000008000040304004281c40007a80d560041d0807642c03000300303112241555201070720b400410540e0042410358880d010780d038800c0e450f0504a1030f07480d9078400414051413840c44011a02281003811441d10844001c001203001e0024002964252902155005002e429200398411304001a080c1c1d02c00c034641000b01ea00040080050341da9491810884540840e80400025a440001420408140f00b502c80d082001d00081840d95141030520000350f0000381c060760820415000d00c04d20140070171009111304051000860200b040e01c001406440080c1c1040c40030341c00034881440b18650101c4d80c0d0b0780c4006564101c09401d615000142d00341200003200c071a60303248071a4045440740000802d07a04540045e400c40741c1554a640b540f100720006030107503110315001041090060321784500c0080880e9901103080242c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 499365575 1250 499364325 499364351
    0x20a020a050a0b0f010e1611010b040f05040c050114071b030209090102120702030c03070b0a060302060304050f19030c020108100b18120c0f0105070501020d05072c061606 75
    0x2c03a142400c60380d2071030381c104006284808580050040c00c0c5140a80e4031400c00c074585842c1d800c1440c8500081010002c111080341500350440f04403554064000c00c2248080800540581405c0310b0a891810a120001800b5440f80078103003118481441040e041c28000c1d500d10a403072030780700828000720388030b540048003584c1d4101c3c0b1305024515081c0011303584c001c5950034031a0340000a16a20940d0014051b002003c0804400c031102eaa90201240c002a601e0019680080006400c003039007200e0040108070070008000b41000280c02c080c0200c0c3c008401e00c4021041005507840c00800040c8801c0310700d0010750140101c3d9030070215209481601644034548885650003814402d030300340582e00d14071001360810030311080b01782c00e80300054503880222002103425038a0082610341000400102003003030080a50545203211000c42d024841e070700b080d0714000c2020a005101080800508821801240140707520306a510f4000e0449410003141146291284e400003074103035003854540441820344 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 499366825 1250 499365575 499365583
    0x7060207060f140f0105010503150604081501061404050a0905180d230f030708060303070803041b1202030d030b03031e220f0302040b041413060506060418020a020a05 73
    0x94100120000e002030b0224a1201c40d003e014200020468004006100700d0361b011080f203030300541c1c8041c030b00d80110440c80130403024843d5900c584421b02400b01c07503003810002203141c0341c1229030541d1900e036400d80000c0f101450b071046105595010180500c00c005500454112646c00b0522051404061070544031046c140103080c2203100015a80f2007981007901507e00c5010380b2034a05500342c50400c16180c180c440e50744405881081840310308000240340d03076402c0048900c5e0b00c4c0d0000c41d40c2d8481c1000e00d00036a040443d14185039a4140ea03c1020030105219019806002d400034002c01c0f0700e00024a06034010070850380c005415000800038260141c22801c841007203d00c201ca4029030700c1060b1050407540002038456850000f824070f070100301400080d50f12009882c0c040310005400054440018005e08152a20310f81c10500c4a0820900300d508068002d00940075420a111668500c420021980308900584420b01080c2501000350703207903a40909908015401225403001181d25010300e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 499368075 1250 499366825 499366841
    0x6031a040212090105071107141207060509090705070506040f0606151d0a051807051312030e010806060d0e030c0f0609010b0306060f040e120408010c080c130302060706020706 77
    0x1c010b40180000c01d20244a00e075401221464582e051812100009844407418413807116500d041d2544180f856070782403100d41c7d821810404413480e4980c0c8060150964220407042c1d403054440400103503546019200b1100c0203607000c000f07480a40d85039965001c40d101c2d410020b0390074aa03aa08040750880044124186008185d1100d080da1480c448003d250380d090072113030364024a2101d0041007a502d40c924a1200451020f10f100d40d25a9601012540ba0040200d0341c00d05d42507001000810301d041e02d58099045000340d0ba0010100d1103580155000c21045da00ca82d002141042208942d0301c1e551301510802022009a13460b250340000c7d5285090004010318000340c00030380911014000910542c1d54110041c1d01030422840c0c50303000100080200b00c1464011038588981241103501444501c0000d0b20b0f90075600e0315162500892802080e0101c41000800e04c042c022400700c85155055445013060451044810b50079a4241701a070303000547d007119565004c1c00f2501c005a5a8059884 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 499369325 1250 499368075 499368097
    0x6090c0302043012030f0204030c030b0f0c0a1409100203040e010f06050f0c0312042609060412150c0c06062408090703080301090c0e0102061006031a0402 68
    0x1032030350700b8031144040d07a14400c03402c000d683c1022460f00030700303601001003075a8442d00588001800402c4c08816006072038180c20480781e551000601004019082002905490042d030880c1842e580d0403041d1194a0401d45075051a81010300203100c0107885010400752810460f01000d0406d1081c60104d04001c480401120140c1c0010a05009540d169a0858014580c0f4280f10006034a00300002c0c1023441000101650810005150031003ca410004c889402c1c0b19258038010524040c140301c4c1d03e20306034903d111800b55021400b21503040c000404d13540480001001d03640303007d02c1c10411402100500d00121102003400200c061408003521800c04548415125a4000b81c42840d00c8001c40e80b10ba00509402d04c07182d02d50419283c2c10852180540440b42002d406540302c01c2d1000e850f01c041607100420001c0004008a2810419000240400d4060700c501e450580400b00590319a0b400f00c80a000e01d01c201c8404005d42d0b40719800c80c4c203840440700d009418490358000460141e07484144004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 499370575 1250 499369325 499369327
    0x9080703050309040506060a080606091f0f02060718050d02010309140105040302160e1f0504021c0606090b0a0807031d011a0108150d050322030c0e0606190306090c0302 74
    0x340f1608041c020303240d0043d41150346902c1d0901c240d40c09840540c2c040d0010380a004045000c1105031240690000140503014040036000c060134001840080f242d00f465005000d9040424401c1d401850030048514850201c1c2c0841030030081072010009141c4000e904240e1549a24804501000702c0c070307a02000950004180b524250501914080000b8071107550510300d940c04119004040500540003603140002e110000d21140300c0080f144100d0704442d074441d20000f28159840c0f502c000303e00d0000c41c007100c144540741d030380c0d1000d45107480c05201d140c2030004100724003070043c0d01c42c0b07074039039030015442c20005500524104004440000e00e080a00260755400744008032210310000e500c01d00d50246440c410a152042d940350145001000090040c0005800d000403c00d00713000361002d1a0b00c0402e11041c982341d442c040b8140d02c815101c02c0c0c2e15400344400229144100d8400148200e0000d01b6561424010354010003010003016004800c140d50b401c0d01269a54041c010044407004070b035409 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 499371825 1250 499370575 499370587
    0x80a0906050420010c0b0105040f0603080d0218040e06041203020c060412230a0c020d0b04030e090f010302030a200a0602031b01051632030403110c03060a0507090807030503 76
    0x86202150f450001d0501041d0004030b000108202d40c8a415104151360228042e1044a04a0081d100c207810007000b090011512402c0d000d120740c09004182901030801c245641da00d010b000c12124801d6242c5031a4020701c1c001004201c0b040c03e0074a000d0f40d1803400501c1d16007841d52081c02c1200907074045802030000080c054441d64080d0f0149070703482082d4042c44518100c080782c26110b206010510b410700080c004440b0030340d42c1d00300007400306580142041c900703403601e49401410324007270f659410721941c00000070600c03074000200514160703a40a401040c03030698a17100c0c2c0a940001b000040c9246645c20b10078400350319020151001401680c00454451500e020810005026143e04e514a6858001000445610203259400443d03c40c2003e8003042c0310103085204d450386048095462090054400e110303800c50000035482580695110700c80700345040a440d4513400992541c51f4150702200100d00c2d204071951150b0b4000070345043c1920455540c0e00c016082015503802a12240c101080c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 499373075 1250 499371825 499371863
    0xe040303050103030f05190e030f1b041d0703030509040902120a0240022512050304110f010509040c050405040c02030a050a110705120105040c0b130303080a09060504 73
    0x111903c2c01d140b60500d1828146501401f843d2040c084020104001462190b20b8403a1414010340040310000c4003529004194410755034100781607074222070f0250340b4180c04076006114030011300802030300480181c1006072031030318100c941d038114900d615803059407420241c005a4900880c000d03440034910181005082d107004104509a0316864900500310808158016036032140d0904055044c119075a002c064940742d602000f402a143c10700b8070011000c04ca103510408915010b080244a07025519004580b940c00706d445004c180c0d001400c0e01d0707121003d0125071404558440100c80c06141075400c0c44045400542500c12648114010400000302400182082d0007881403110700c3d400194941842124024014400c15901c01c0800110a25003d1010000e124000003850001c4c031803001156000d00c46070080400303a8048400403c0d230903001a511001c8001d8500307103140701445038034441ca561410b840c0820010801200130fa82c0d040000000b0318544190b50207180205480304034004007040c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 499374325 1250 499373075 499373087
    0x81f0509070f030e120d0510080105040804170c0a05010c17030106030e070b04050306040f050a0f080d050601020f0c01030911090115020d05131703120a0c02241f0e04030305010303 79
    0x8041903c0e405c4100b64101d020309140455401d043c0c8070304009000d6039080c00b07017120110150407910081d402c120a10081c420900098001c5e250542e00d01c1a13000729002c1225070307803000c0e40141504110841c2c0d0070005e039806091038101460160310040d0140a40440312200307603100360440c00c04291f0392031000b4690002080500041c0014006852070141013100007079480800800c01448601000700701800c1010030b010240b4031030351002c00488a00d80711b1074901003940001203228000c520f403e0001d84590320000310307022645101c2c0c0140010030400c0c40110007034410301d48184c0d405000f1403205c2080751a04050f42e4000d19400754580030b520740c196802814008803600c0001003148c240a0403c2e00781c2154003003000c48496004540040d94a0032210f03056009089030b40f400707880e1950400090720b2590708a8843da0500c0d07130a549022001009440400b0200b002c01c0343e6000d95107000548040b0500103060310305500c21000240c07180ea80c408200c0d12501120110002074880004008140e0045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 499375575 1250 499374325 499374341
    0x9020a030c1b021512040305180d02010f030c05130b0c01050c0a05031302011412090601080d0504030b07480503070b040201050c1005090c0a06081f0509070f03 70
    0x316000e0020311890782d401a5081190101910410092040c101580100001c45401e80c0650548880c14506802c0250003034200071104103441c4c2d140b02c4031154500c0c0c0161507140c4154141c58110401003800f1003100104500324031041401800c1245483c402e114980e07400050080f6540b5660b1040302c40c83c02c078252000a01001e1544400744512070b0196044401d0313035488031210710500f0100d01c8900040300e41000a6004030b540080014610154540300f0b0003403031044448500320f40050341d0342c0e840603540781854000040090030a0205100003400411866040034841c80e0454462546010384604510b8103903030031400d4414600801c910307103681c3c40e0804d07207103681405036400c180d240d0700ca0726181c0c0b0851a004080049040024086a0040c4141c40000820354102d0b8110741c5206000c00082c6000d481d4070745203104980340d0003200c0c42c00c1c0500005640655907004010784460171801d0202d00d407040401e400a21010000c035040d20390140e5207110b18078030b5850340c81d2034149690143c04c9070000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 499376825 1250 499375575 499375577
    0x123c02100e03030a0f03140403080610090515130b0a020d170709050607032708010b0319021905151206010f050a0c0309090509030306010f0309020307050d0807060609020a030c 77
    0x149903030010030382c1d01006a484104503802c18080700100140110010b0488070244060310012109000c14941c0c0700101e940b2070802910007018140c8604000d41c1e8401c1c0d140301c1c5ca54001c0b000e40c80c42109500305405000042d100c078100d010080e03164543c2c5001500001c0c0743d600140c0c003a0240b4000d5030351100720040440d56600d100c00e201c0c20982402014034044e4003c85011300b000003040f80401d4810310b8071441d0100e050b00740422454282d1007051110b10075105401c50307982030503400c0c0010300d00401c07030b4401c030368084248906951550f0709101840710002a01c0c2070040320800e000900b0f842d10907c0c59229075010540301d030b44800b050060401c8150203803101e410071006800340100c07190010202c42001c0c8141c01d1404640c04d803407030b00310b030403031600d800c4510158244401d2200d240701c004082d6000e25003d03254000310480000d021011940c7d0007034080c0d81644103400811031070504401c0244001d02407010305143c0a5651912015100076901084480e540040c207103003003503810301c82c507840c10300360b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 499378075 1250 499376825 499376837
    0x3090f070e060927010e0d02070f050612072d0305070c030f180b0d0c090b0c060a1107080a020f0c1e040f150308120a020301123c0210 59
    0xc240040f0303c014038010901c0c80282d24803a15401c80c6203079821400c05194620009011610000c4034450700c510740000d01001500c10300c44c0210b100e051b1640c5020680c1d0000c2c084500b0500020344108145002405200620104d0400303205043e128501c4070601b8100041c5541e104a03550750020100d4200408c1d9204000c0e200d03006200090b400151003201c4900e40c42c1001c8030480310240e09038844ca60381d00c407400400001481e981d1a00706500000e802d007400d51214607060f0380c0c6410340f44251040180030b0480d82c114000056601c400d075402000040d400c08066401c004044e80c40001d42d0340328207160740c056800b108104142d402d0401c000e04407280103507000001c55200f4119200c0c520140b0b2440c903c150f40751080301081c8800c2d54403590b0000c1904030085200c0d640c80c20090341d0387c2d211540c508851054cd00000701c2c22809402100d040300d8103001c3d00003031b004003500c03210324035080100e540e01450b030102c80e4940240700407110505103030401c403075000b207034a054070401c240010608040d10134056 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 499379325 1250 499378075 499378081
    0x90c030c140f010f0f0c051204030b0906060303040f06050d061205010e21070f1b0b03010f120c0b0904090b010b04050405130308010b070516060c060e0a080412021503090f070e 77
    0x42c3c0000158510f401768201040f8040c0c0610781541004400c0480c842d040704049000030900c11481c18141c000d51010040e80c0e034585418081c10f88078440c1d406200c1c0940182e00003001050300c1100140f0ba41100c0b0440081c4180d12084942c010613000d60040d14203a454100440c4a11424456000e000410300d01c800e0523204404464460350042035805868800080d00c07413418004007840e8148244200c8400318001a00c40580b92210b1b0028090704800c8460060007144264040020612440c0c000f4441c208003403070951040e03481d81c000c845880d00645c580318460002006080d0740f40c00383c030449040075100c0381844180030440d44000c0900200c2a00221a90f01107600a0602070640703040580751550741d496030030014a000741d15070115001d113041c24000911147e00c4995400c41c02e00c64203007484000300120389141d81c0c000c4e1650141c0706040c00c1004108110f206200001071901c0609001c0b005442e03041039914503007003294080c04c59001a210403600c00400d01009d4040c003c621040c8034942 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 499380575 1250 499379325 499379327
    0x1030c02070f1701180f140316120c0501060b04061205060f061e0c1501062f010e032a06010308030402090402010c12120c03020a02060a090c030c140f010f 68
    0x200080c0704406076007441c3d80401e428070b18207401a030191200d1500c190366810003442c003d0022070525078141c030356035040d040070310b42c814000c41280c11051058403c4c5507940c00a80380c5a031b103c46042e120b8400d000e51411b90100064007802170200a1000243d211340b15440c06c24050620041c4aa110340c1480c940410400c06646915864010501c16910301d5110800d00f80d04480522020001c2c020055000c2046903136143c00103501134101c15680140001c99aa514060701c000310040700090174020003100004441004451114203107190800103d90032031600c03809401c41c0d202c1d400c0c4280b8001340310000012100e4a1210300d0f0328030107843c01020b00350303d903844d680a03500001e440240314210560208081d6841070500c0c01c05507800c401141c4e0340e1141148080d0005e0710b000c009159044c209400c4c00d09030707406442942c00b0b61250744c01400301c0d075403000c20200c014160844212011100ca102c080042203418a010001d000f10803400c0c403420a00500f00b0680c030640f2841e680c1001389813603c0040b1a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 499381825 1250 499380575 499380599
    0x60605030c0d060902010302130f050f0108060f01031505120f0c01020a1a10050402030c030402010806040b03121c060b03010f0803030705040e0a0902030105190609051308220609030201030c0207 85
    0x12a00f1240000f0704013424030048000c1e2184009008a0580364440419081451890001180c20845582c10504400c90056030000e0040794007036030000343d4142d641041d5000703030030000028103041c0100b4951500d0340b0006009000088175654694001c40407107501c6a8100041807429400740000c00100c0da403541ca000d031800c80d055103d58065006d40210310394144003091700001d0b040003403042d52a458400c414040a400440b07060340000e12030310106601d42468030403290f110a01801804500f10b040c010f2a900f035100b0303c00300301010221800003112044074032940015107054405140d4079407402203040300610194011b4220343e00200b041c4071045030000120341c00c850145945036420303900e140e805402483d00c01400380d0554204020000140c031446c4000701001c0603014200000c039100e00c01c2000301d8000321079030700200e5900d540000205400c5009002d0055074114144400d00000302405902c510580c0840b000c5106940240700b10340e0140160030f905411232001b4420780d0324000300d072085 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 499383075 1250 499381825 499381849
    0xf070e25051813020c060a0e0607051809010905010302120706080708130606030b331219030c0209160c02040b010504030c03080405091303020d08060f1c060605030c 72
    0x50060000b01c054510044803000007581800034501e0b00314440d0300901101a40c03003c4c074000c8035402010002860001c051041c80882e07042d0740000c082590f00c0d504243c074140d00c00c1c0d08006401c90441055000b981d6000c843d240640b40c1254080b03065491441885140c4c00c902603484500d800c142c4003840302e251310803489980f0022918143c590ba80384c031916904c1800800301d0261406040441c08410321210440d401d0041c40e6080803101aa10340842c0c0205000c1c0c10300c60607140c801954030136031082ca844005a800b080c4500107490110801c1c40c25188050080c020480214807801d200d5025890701c00c1d441c03030703100c0d0760790b9031741000001e0700d050091558030030100080c422540c45200708201c0c0d00c00e000382c0700955807100d07440c00d40c640c0380d007400706450f046841800c1c0316192060010b8085074100d100c01c42642e525400a005040300c40c9000c0d684054020001500102c1007800c0d110141d03140060b000d40030401c800464555149814120103a5442c0d0b00568041d0303100c4800c40416031105440564 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 499384325 1250 499383075 499383077
    0x5010813110a2d0510090306050402040e0d0c061406010f18080111130b040501020a1103030d380d0f06020f031014030a150b120f070e25 60
    0x1201c0c6508000284100005401100c84201c2c0b980c010910704200ca40300d08a014404854984030710751300c5040082c070100c0c02d03c2100000d403410400704001400c9030401a0003d10080c80421010301e07020050b4a02203000b070041c6c0001c1c1059503c0c609000c03603441110003400d03440c0e1b00708240740350440c0041c20017286000304808000c40742480407200404064820041c0a00100038007407a10018401c014907001600d041110a80b116000a03000a640c0d044904440c1d068002d08041161519010070703440c80c5240c3ca5030140801c122581c4011100d20801c0c810494114045180140741000301c40c1480f1420f113419003048000c0002c141550300c4490703001402d82d01403d407020a0b1300628040e0080c1c0030301e002800400101009000c0303040448010002aa42d000551b4629840010f0800d65501d01b103220260100712001c0c11402003842d02e4004041000010384224841e40c080e503d618901510b0090101c0b02e0b802948040c844503101c101e845401420380c14a002c00b50002031907605480302c03030a00440c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 499385575 1250 499384325 499384343
    0xf02090f090405011b0201150905010e160306050301020a080106170411040216060603050303010305210f0d1e020306040c02010504171b0303010f0603050a0c0f0806030316050d0905010813 82
    0x10200f19003500903c00c50500451405501081e5503806406003004084048015140c502c0100d202d1403248100743c102c0d00c90001c004001d40714901e0124070084e5020300601015254180401c41d900c00740002e0403032084681e100700030781d8901039000b40780c082d208585c0070340500c4003001e0002040c072554500100e40d004642c0140d03550018490642440c44805000b8071040c1444000024002d010000d11b040780e0150041e140840c1a40a0994108a810500003907281c82401009030000d0070030f0140804540641000500703030100c04080412811003603003900065000402c21640342098040d0070b4065980c0e000a11860810341d9495551003440a626941c000b03010800303514404204800c0c51503000c2e01c13000d8036540d5840d202e000f81400744502400c1c02007810100468101c130b1480c400d10381058096556014030301060107084440c03100260030542d152005212070700085080c0300601007024441c030000d0104a005500c05094030119174400c906118800d410003084c0140701c03819408041c0e000e4104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 499386825 1250 499385575 499385581
    0x11406011d0307180510080d0507151b11010209090105060d0207020a030501270809211e19020a090504170703050c0714010504091802030a150f02090f09 67
    0x18104030907101c000c941c07500c1624800140c1c41c881c021100c0c0c0c0e14101c80e009006030340c1c45e541e142400340003d1140c070000ba40b14500300d800e014424000381c800240301c1c0c1c900c160310011030702c1d404060355002500e8241d0540b40c01d00b290280364001564007040e4480c00000d5081c01c44013000100000e01c1403103818001e000000b2960422521340c0c1c100c40343ca0354000e1448e002c150700e03428100d0081c030ba401000c0c1d402040d28005404000349502c00504095444010070345015200e0080c881c00030340418201c00f5908049420f22104242808150040d50141500b044040307105070006261689040d4074103000c00d00e46500c4000750311200d48560a0702e2040d40003140da5100c2e40342c040e9260342c0da803a410030310301d81c00318240c01016840f20050070191b0700c02e000c580451391914403601441801d040c0c2c040c04914104001c2010711070641140145c444129011506440c458020900b000041c40f403c94910080c4000404c640b92540305820344160316440440c04c060401010a131400c180c0401e09105207541000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 499388075 1250 499386825 499386857
    0x1606030e0706120b060c03031905190915110a03050c0405061608090d030e0306071e030b0a03021f09080f07090b0f0406090501050a080615010c1401050708011701140601 74
    0x2210500410262101b559544110b44040e12900223440e000380701c003446075041105000c3c5001d000c0c025200c900c144103580144100040080644e404120b501e00b142c0c3c28501032860f690b00c20642050109600307555904040c0304003d0480b0310051403010381d013206000611503600c07101d06403000b0105650901660b8142800d01c49128000c482049a0168080d101c0504069210181002042c0107400700d0f0320b2600c41e4541a140b400201964541d202400080540d0f107910a0304101d50414014107400e14181e02e80e0003198012600748281040c100215200300321507540141000d00a1482c0300150a80e2602d4000300703a00c03240c6c00e11540f082a5250b245500442d07440078092282c20710000d104000403980d48041c0800341a00b48070319032080710020000680000d0104d0760501c924580314030802d0031040e120041d10f091003041c200782c0d4500c0b10202d8100002c2e00900c42c8901809054035581e02643c58440c00c601d84104c46104d003c40360f4109801d0a041030f041410a541040c42401c00244901a24074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 499389325 1250 499388075 499388081
    0x406080a020d03090e0907150c030806010e1908010b0108010e010b040b0a05040b0319060504060b040515160f0620030403030506030120030114060705190204020d0c021606030e070612 80
    0x100c0b41c58650882401300d04000054a0001c0303c2224005d0b08c440c88000c0001d1303461105803580500443d0b034000c000380045d0301c150758207100701800030160f14020741565442400440c1c1c5800200260395030380080c25180d03800502840c01400c0703050307032005950f0610300140c0c514042c51003203004070900812800d905c0740c000d00c10380f40500001d90b030458491510440b000080d000725a0f5813003855140080c049240d0a080c003c560a91340160404e601d01864039040c00741d00c01c1c4203a90410101014020700c4540c00100d48401e080c94002c0a10f62814a120300b8044103d03280e4100682e0540104000602d40c4038101040e60343c002e8250500003016036a01d1f011030301500344401d0b1745940c502c2c081d0304c454000b58100302641c103840d03c07121f07200c0d01c004204080c40b030b03684078209014196031b00a92500780e00b164022001d5000a2000c0c2015040c855211685c0c403d844a0000e10405078000828128955820064090080080d4601400360101c031003100c0c1d4a81005001d1a420091184821160070303010750 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 499390575 1250 499389325 499389329
    0xa0e090d0c020d020d0f06110901140c1603231908091908240408040b0d02130902070b1302060301170a0b0703020a0809120a030207031e1d0406080a020d0309 69
    0x2d0800c00d030b48240b44c603003440411004001107e806240500f0003450b240303940181d074203e01060f120641f4001e41c46180c2798194000e0718400703016200328030044564529400c03401008500c10340000c0f8000781d580091420302c2e40d20906050483d400b841d012600c204ca05000a58182c0c3c10503030b000c0d900c09220012030305040da0319800552421042100041e01140003881600880b080b910f400c0151440110b8a20030301000e81c1c01401c0400207210600c0440100c4000f4000251000310040c40c0400400720800d000065a010300c0c4070340d90102d418018441a80c040d41d03400041483c5120311005241d0000380c0c1c5d4041030255150b180107200083d85420700800510949039042514000f9915220f00010b0295010b540c2d41d80000e042c6001155450784002010f04d840000c18062a0620008681c200c00a4110840c00e800704000d24400048040c040054890540810303917858020968041c0180000c50002c04158010380c0340000c00c000e401c2010803000c8181d07604452703482c8132115a06044412420a03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 499391825 1250 499390575 499390579
    0x1a0f060d0501061d0306010803071407090c020c040b0102010212180309040218030d050f0403170417010e010501050d02063001060804030e0907360b090a0e090d0c020d02 74
    0x3002281036070b0010a0040304013003071016a00c42c0084103041c1902e448003881201c076580c2c400d00c4808001640460300c048410300d008200c8031510b585d00d03140010780e101d081d03035100541c100c0405105181014040c0080b039400c20300003942340a19104c1480316401c0010310540414a4021a451490400b403044413008140200b096465002100745800c802035000180340c0b0034450b038031180742c500c0d000701c00340c5402504e1000b459050a1440c1c82d1441f580c1024201075840c2c01c410040412980201c02d11000703214443d2000090f17a8040310001d42c21200103800ca144a509810514001603484008446040c0c003d2000104955400c610f0280b0b001c0e80030010480c00c20618001058069020510502c0b0704d000740c0e1070322904400c40c03041c811900416600403000521000221885810700a400b10070803810045030480c0145e408021b6004c4503c6401a844182000490941c0b074a840e440c3c40020b4400c841c20110a81028a1800d030359880014812051041002002055541d1010204581a00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 499393075 1250 499391825 499391831
    0xa02010c030201021c390f090308040816140a0b090409020d05060417070f020904110a090c02160608070f03060801050c0306040e07051e03070914191a0f060d 69
    0x81c0d002c07004094404030300215803e01468003030111003064151450300003944503041800406c030a850071103800c1413001002062000c580400000030f402d45000300000c0c00400c1c080c08503008840c0c02c49401c0c107610750060424071403039610002580e4400d10800100e44025056958a50303214010401400b40000061b50000684000300240000412040e101d1881403000c0e09049144050b2020b183c00303140790140900c2070341c155480050501c1c143e03480d017007801020414004007411001840c0000f40d07820101000340c881109180e41a0100b06009840c13408030450400035042000041c0880b00c005c202c82c007048440790a694a56020340e021101030a18240240003d03c1d00032031031809640300360b0710316018600e015042014007201007030f41e401f9a24010b0040b030000070540c80c1140000780c0112400e03458003a24100040c444001d114000c0c0d508401800b11110345001035905800800303099060b00c43c1420040158901425030410365505102140c42e41d0074004600041025405540030001c40b4501d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 499394325 1250 499393075 499393117
    0xa0c15050702010b0307060507030c0f0201020a152007020d060216140106050a0902070b0109110c01060312230a0503042f090105040b060706050a0e1501060810080a02010c03020102 79
    0x541074101041d407810a504440c02c103603507840200c2301845001000380015034049620400105e42590410b003050051048071004140368440c0e428503c12894841103882da0354051140c2e0210811655402c2c088002c021414660345402081072820f0755140200100d0340020350076040850104902562600701d130090843c0c4984c0211a80200024083c0074801c4c1541000010800d10500841e00030903444803600310581d00c0c090080e400751110901c5001d1040c4284641030019900340716040040d4060a0700544814400c0405005252800c43c0360a00d0140b000d24401e41b640380700100c55000384140f80c42503680e80c86081c85903140480ca00c9904007400840361001941c0b4038001e14081c81c160440d05803601d40d9940080000b110009001503410010600c01a000300d05158000e07540880b41181c007040910380240e1440c1041300e440c200e480407800300310050100c5617100d110f8a9001401d10803841200e410000300942d19031107504001e040101801005081500c00e4040e103201d004014101d0240203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 499395575 1250 499394325 499394327
    0xa08030d051e04030c0f02221401050108100e09070e04080d06170705061e04080d0206090c0904081303050f010f110313200d120305060109030201050a0c150507 70
    0xb9500740008451151107025145202440c5500666151310341301440c1c01642d44009001c5d499034000d80c0c1c40724070110b4901c4071a00060300044180d4020780d0006171645c4c60156040b0200e41030b0003a504000c08601004400c0301c00c00c507650700b900d412030205400360381da030048545480c02541103103004101003804c2c4000c0102c1d0b80082c1c003d4604c00581401020344a0788884103100751010b4590380c0340c0c003103403081085040003c02408070b04100c000a02e142240b060202001e0350250b4400303038545c1c0c0880b8032150231550610216800c5040b9002030807400e516031000500340500a84013520170203002550412100d0301d168400025603110b000e0341c5020050024180c003c00a41c000146401e003403140040c450400d0303004580c4240300c4440c10092426003603c03007144d2005800c1400fa09500c100000910565901c506210102d11404644c15842400c500c000c0940b0b00c0503100c80d052010809007440141c0c1c001c0d0039114284800d00d002c0380fa0418500700b00700000c00380070301c000043d450241841201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 499396825 1250 499395575 499395581
    0x10216170c0114010e0601020f070603020c0703050106060e150304080301051e040e07061b050712020a1211011d01080c090f0d0c0312110303072d090503060709030b04060b0a08030d 79
    0x980c803201e055540da1ba642d800690f01d0307904880703c130704807508118001d10425000b039024064007800642120450b80d01ca68446085130142d070400d0021403100e80c540501c0e444d0440240700210312000d149429405d00350f4505140b0301041c010303288582c03551030b4000074501c49041d81c441c1c00d1034001d009104446061850750b4889203240103440000740b100c00b40503c0c0b01031740884851080d5000b002828007034606610460200940d06080781e1101a00e100081d894150110055030030b401a0a07606541c0103c00c005002014401c5003407908050410400c0410707a0000306156018964100d0b10303035500b6091000420000c01d401d601075000720380450541c240103070b9030100c0013503d10881e40b1940780c15a00350295049202c010288016a00030000100494400c444034101f220481040c0718103284402003010154100640e480001582e040080046180410165400181d9414000a09400e50300d4013040c24000030405042c0d507848441140d0720f074880c0c001c01c1c3d0050041d0780a581d15000c0303102000010b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 499398075 1250 499396825 499396829
    0x605040b0f07020f0a06051012030f0905012618030a020705040b1906050f0f0f0c010f020f040302060304020d0507170f39060309031308010216170c011401 68
    0x191100c0040082d0002c0d0002560180c181200070080030002000d607224005008005e10f03075030300580b0070540080d60003440d00d2004030721807081c0c0b07070702d0200620030070b00404a4000354495410030000900c40205410f4004045210380312400d1580004e0b626840c40301075158002c1d10380344091200003400c00c84194040303001d42c1035031400c072030612954103182c041100e800010f4610780c1d6000c2c1d6516080014070700800007000710580b000041c3e814608070064402c1103403c01d5014007200c4100081c4006413010a2090b001190041d02046080080510038038603140a14000240180c600001007019540e815035840c020030303440741c01c88000545032074900798144800c804004143c49a21380104c1054004140c1402000628440001c404110078008035019123061000074100107003c04001c068544200541c410b4805900856644020a242245000c0d00e9400180143d105020b103030f000c07121000800c03a0032078000e0700b43c0c14402c00104201c8603500c11400c07800855840d0040c0f01c42041058404241 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 499399325 1250 499398075 499398091
    0xa0f06030c09053a020603180c0603040b0103031b12030c0201110c0106061209240221090f0606130c05042c06061c020a0309050a06140702030f07030305130605040b 72
    0x14802d00004600c11300140c0300c0e03400a5020205100140400e0034680d40daa08090070b903000c864214070041c002c00c030340c1c0e0310035101903400661010042c01415008009000e840001140032142c02445d130b1241d0514000301700b00d0b0008c0588864041004c20310075080315140d0b03200c1e58082c9a40d41c5501390118000c1186204203808100e640c0030702004583c030b03032160b91809600809441914545040c01003100c048100d44500d800b80c1c288005144d14045006424003018840d090100130f0500310b950901e0521074010540c0d20383d0140003001580d0302e40711009100c2c001c1100020610003030206059900c1e0045400102c08115000401c40700b40f01502003608141041100800464482405200303030b5100d00c070002c2c0c007107070411120804540b0890f4003c2c11460140e140008401060341c1d00c3e40e0410803601006d80c1c40703648a08201075164100c948564114101c0e00040d881c2c03201c81401842c1c076000e020340c0a8241075540000440c1084400d441c50314a65208200f00114601031414600404047e117080c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 499400575 1250 499399325 499399399
    0x90a02040f0506030d0c080904050604110705011d070609031101031b02060103120e09060906030f032206030902010f181203020f0d0503130221030a050307020c0a0f06030c0905 77
    0x4a851401441d8803800c8031f401429885c40c0441500034003002e040040d0506400c60ba541500810041140f000341806612400021a2100010407010703100710b11480301c0c603801c0e00014802c0021507040381944044940c00450516100103040041e0006d24011040b100410340c0c3c030401d07078081c1d0303400321b00071b03040c1da01c50701407800d0103c2003d004a5200c01401d5000e03422103159004030b900c03031034407446030b0380c1c0044001c003140e081d2040c480341d10b800c640080d10810f0000310303000a800c1091002c803a07800d001d0a064034007000b155490b600000c0c0321450354a0304005010401442c268804a03036403580c00500300d40c1c0880c8801c0869854029620144182c01c0341082c0604003400000e548070320201d9016840c2e40c00300c500140d100b0340070462100341d1058805800386440644240444042c00986000b9a640d1079084d12890001d070068107140c41d60b03141c1c0344507074003c10b814021403250480d01b01c25220035180009840002e45401d9851b01c00c01d0700030f543c0c0302120881c40045d0321151454014002e10040c01c00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 499401825 1250 499400575 499400593
    0x521060d021915050a0e01080a09080f07030305061207050d060605090114010f08010510050903030c010f05040c09050601050313060b0a2414090f030a14100e0d0e0405090a02040f050603 81
    0x201d5050240c0b159020018146c08580c3c2031039032240d81015000a80441e00040d641410f507038060007988800014003070b00c140420b0300d005140d0035200d01035000b40140c80300300d181041000c03160b0300c0d09210700038281305040308080f290600c0401d0f4020720242c20043d102c6092075071071f0a10050040c40c0001d040b40068000c62041800d01d204400250403a1009403030b00e540c640380e604050f034807a044a24199003610040c442d0452a0707009014109200c00100780003d15803e1a081220500850750009401e1a081c50b05000c41d40c0d0340181100c0d800803286159240844940c505140500324224210750301840207840400c038400b59a80721311888418070180e00c401100040d055a0b0070701d011180d648441424400c1c00c00604001d20156403400c001003d40304c4c1300140b55200003d0240c20b20100c401c44d0310100710f442044001380704030403011803450020b0403804003c00d80108800c000401c42e901840c2c0328030105070303500700c10018148125801042070060010600c0a00f00070003045072002d2003032145421f4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 499403075 1250 499401825 499401827
    0x30727140d0506190f2c0607121a1e01031808030a110913020703080c072112110309070b030f0403110a0c12030e010521060d021915 58
    0x29041c40c258010080e0981c0d59039013042209804542016000e100d0716400c10350401c1da8a40305015250681300f1190303013038406119a080d20481146400c1d030a5a112900740300042d50401d01180c10030141c61004a034190114403000c50b044903046605420402a601c070040241c01450440c009110aa80c10005035440d114281460890a5000b4140c031004102242c0400850307045043c5801d400c20030649003d03030000110340390f0080c18001030403096000c0341d54006c05510040b00c0780c100f0b01111440742060015241d00d00d1500b22160b440c41168180b046802c0107070300401075248404408242000300550f80500650f0b55441140c0d820081c0c042c0c00710219041e507083c015a07001d400c4c5000d03c0407042e602e941d03041d50200020071800c10075101d0100c0040c0043d03c483d0300340c00a00fa0f803a504105404451402400c06600c05103564140034043c005841e020b00700d0706c0640724444482003503c0c4251a2280071a0126078400c3d4040d4116000780d0002042e00790f000d00810485400300700030009042d807204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 499404325 1250 499403075 499403089
    0x1106040b070311010204030b1602010c1403180f0d110601050a06080609100e071d040606120906090812090d033803010603151a03070b03072714 63
    0x10300204008140a03640100303226440b426003001d8020700051800745c072a00e030603034100c10880350402032001c240c902c9014661b083c0501c0412221609061070702c04c8812a800c2d0560200901c50099140350440f0202c50b0b06003000140303030000000013900e500241409000341101244c0312814554401d2400006280c101410380c24201c402a44c0d4400141d101d403410407030b0020000d000000106140400422201c2c1e01600150066641d80c9890509000440710102e80d480510400d6100e46d160003010440d098000c10012040003d002000403102d1316032415900400b15954040e060000100d0012165030180fa40c00d40182035000464907000c000310070440507a080013850404803440400000e2906244180c007000c8000d409031101006142072010038210b07481540290b40818040c01c1542c0c102d5014400d1105aa0720007a4200040e0391f518086a503400c483d10680001500c000002a0094880d1b1486806680c403100c40404001c0301440b40307035005086004143c0a00d01c0d018a036252490400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 499405575 1250 499404325 499404329
    0xa0315050d060e030708040603141807050402030a1e09020307080a150203070318031d0d0b01210206040308030f0606091011010e0d02011d0708071a04050d03030504110604 75
    0x91084120300003030799860300a0f003007008803100544014001c0e0000603051502800103000c6a9400082c21030142c002446006009000b0702e11145401da103101e540300d030100c0e072001910070a0324003681da519915110002841018025103814034400700c602d0307429900c0c0e08005061030007202110300c8552500d008075242d24110340300406070881d8608100c0440c0c0b040c0c001d541e0120960500098210560f400d015884801d804114009940400c18003000d4421070b06012410f41c080d21079079880d901984e41d0b10b054107010300070490840461920900340c2c417616031045604075406040e503030b00e40380d5178600186680c00c10343c5e40c09040c1050750b0000c1d07130314241841640e01045004103d6009020080350581e4480b40003c60010b25540340c8486180540c001c124900c4022055800040d4941400150480c4001c04620303904161708107403420010182c0026080040d00c1c403807080001c20300180c0c42a5841d0780301e158003a03a00150204035001c24541c00d40c0c413042c811401079044018055148003041060701c614 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 499406825 1250 499405575 499405579
    0x10609050f130c0308041404060605030105060a030e010608150103060605040266010b060415020307061d06070306030c121a180d0203270105130801020a031505 70
    0x11000150b08040301d6004071104a024001e0240090384076103401d1807a80c015002480c030840c0d4580030a010303060610803d8010309951800354195410900062801d2003490217034070401d0349584080009080a500000051451601721510301b54441c58148010000748025907500e440d20a00282c2030405000b00c6074034000c00c03200e2441007455640d8076000e9031352441042540286109030400e076121000800e020a051a01c0e1038154103042e00129025991a10a62007683e41404d1001a250721514140d400755007a2200c500380e0000711a100b2440c60003410006441d4606115000c0c007041d450b0a6505444103a803000c0d51656540c86805400340c0d040c03407100500344c03c1c15801c00c0040c242e255113440740325841948500c07050340c100d940600302c82c441560300c4500360400342c4160840000401c94482407500078000740d400c1c54031100244091a180040d01403401d9003411402e002d03030b8402c034112007038030400f181e40140300c0d501d50180900030b40104184501183c40c01e902d0741c039a80000f5209001f10741c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 499408075 1250 499406825 499406851
    0x30906030c0f030e150901020405030d1b02040216080307080f090d0804060b01090801090b1609030f020f0114070b2703190203160302011415010c1103100c05090301060905 75
    0x2030002c600500c1c001d0698500c5004c1c041c80c04045c00d000c1070016001d00545030001d61540d04020406013490b00300d0480300306000d0100011404c1c402c0350010305004a40444005844540b1401c001445100502004013005000030410001079048440c0c0da0281c03400b250f0089441d91000142a6200d6004914001060135180000d002403081e4011405200b41803409500c400c3d41c2d00c00160039204651400c80f502c45612003004040300340781c04698a41030355403400300241c900c0c50320f45502c815511107002c2d0090010303c1c40440130740d005400f4840307a00c604000c455a21105801c1c614050801562801980d046521050305403481d800700d501038142c01031015514007101890401180c602c5a0b0b980c40940c0001d0000321309069403014136086007802500049002c0c82a0340b0441032000005148202101440200c149541d138070400305812203501070300c1c8807104900f000003c5e1401c40c03846603030b8080d80c1c20084000c40321b0380d1010107001003003070a60080c4071590302e401c0c07500308bc0c1b001221003184441c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 499409325 1250 499408075 499408097
    0x40c02120d14060915040b010e130603060b0306131707080d050402150c0705010c2604080d0c0309180608010e01090615060e01210501060507031805010806041a100c030906030c 77
    0x2030141d112aa02550504011021270140d001045850244c0c1020102c060355840e0200203002e101c2c001d030000306500701d0203060030b45032405051000c44a040d50140c04001c02e000c0b0404a404035030112052180c0081c030003922201510f003885c2c003a0104a0b02240103494004440318102803000a4416201100e40684202e41c01c017001103410b101d80c50802da6040385140861220b2107540031045c00c003c10500e04056070b40e0b080502c0c1c40d140514507002d86c2c0821010a02c910046a0f000c2d1503981500d40917a00c5621a268940048010b00303010341107000294600040318155105c1548200240362090205002c44903155040c542d09080e54810b144c00300700300902d501100e6124581e400703040703071881c000300f0f142281d014040340c1114426005040840d0001500c03100b0b054012401450380d248010f03000300060300780310008003400030191450303000307645500400c060840d811016209904020308442821074807800d0042440d07803201c0c0b0070b40100711290804504540f02c1e00414a0781150341c0c988020650b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 499410575 1250 499409325 499409329
    0x81006091b051b070509040605040b0115090918122c150703140324060c1b060d0906060303200c01390318050f040c02120d14060915 58
    0x256101c81c50101d000f013140129199440b181c01ca4099400740d000000d4603d024034080b9070300c08043e0000403603015807a1070541410742c003000751002d0318420007000c40c00490344d8062402a1020040051415203001649130b40300b0b5005042d00a030144429211545030552010442e1b44002c0c2542c56800044c28441060320301180c0e4020814548607103042c0b00e2040d42021104c5050b0070a80340301c81002e19982103000302c0900c0301a00d2118500441d03080745014404203402c2d03a10004580c0e160756000c2d511030082d200b5a151400e60700c00c150b011206011400841c6003400c01490580000c401203844804c6014415035004508802000e0400091000b9901d05005541c8142858199252000c0905900f04001c00001300e103030103103c0103100407011009625010300003519921583c1070a0441d04820401907503030220741100080243c400007050495403c04030305090111001007014000014803024039020b6901891600500100e40850307a11800c04219030f03100309950140c100d200d07142d0310601d24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 499411825 1250 499410575 499410607
    0x31c1206030804030b1b070b07140a120509031b06180a0c060c15091110020d021e0f06100807050d0209070e180a090510050f010b0310081006091b05 65
    0x80083e644031061106d540c4200c0031242e101c0202200c0d050000414854010780188003105018070081c15a800c1c219410740041402031303803d03001b1f0000b0780c84401042d100c5d14103004445403c051245601510340d5010758056031040181e843d105c0002030800e03204c105110215009070b02c9030f400300d42e910049140c850101c1d8010390001094035440a581e144d1244034540b4172a10041d41d200b42815003809500c03008004941c0d4000513000c0c295048481c9812040c0e5001c2043c01000c5015482805107061100c0120300c1c042046041c00c1c210700c200c50034003943d5130740201d07500200e606a804644019440343c0500c813524904240094110b0a400041128603001d1030820b062004007070103c10300d0394645440200e4403030058448006503a944c507503501c02e1040510050f02011680441403046042c812000100d9040501c02c06142250220200344061001340300307000101109400c903038101102420400c002c1c0503501c01c0348c2100789043c00000f241c208442d0001e070031140340d899050a20072600508030f50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 499413075 1250 499411825 499411831
    0x815060318070504020a081518070c0501090501020a02010b21100c0e090703050a1113061115010e0a05090d02120a030b03070f0302030c01170c090d02031c1206030804030b 75
    0xe002d04800803910b03489070710190940d0409540c42d030082c0e003031107140032240c0341601d1803060084030b801d40c5d1920402c0c41c60344c078103800c50031502c0e03c040b00b2980c50400e54010440740740c0c001c005500000b80b400702a541500700a92002080b1042c40c0314500c030256000101d004442058083d41010107079030140482070740050154404c0742002c0400881e10300000300e000303408440c210086a81c42003440120010362003030f40d0310b0440081350710f0315081101c1070044c28a4070300e00c6008208405420340f4008000240403c90074660f540002c01d816507101e10741904810781c1100c4201449252100003280d20900140c8200710401039005800b41c0c005982a070a103503401010350500b455110100c0324140d890410101c4024050341d01d500604900390310400d400c01108074020303030410a00b41d4100d03410a00c10045917400c04c0c0700307110150391010b880000c02e140d03c40061011358103010783d8a001c00c0710305040100f101504180d80c0c541d4040041020f40c04119142070202825a0720280414000644540b00003a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 499414325 1250 499413075 499413121
    0x180103090309083a0e13110301120209070e09040b18030a090f060806010512270312390c070803040314070b0d0902040b031c08150603 59
    0x1c0554489103e203207401c040c480d800d400150448000c8800035000315908850702d5140742c4607580c1d84183c42c002881140300d041d010340305500030307056000c28519950102c040fa01c14044116202c0d0b94030900c0d0000440d40042c03c0e4000e1660390006104140704080141c0082401044140517498580311060ba00350007c040140892100e1000be100c0c1000304003401c0c0c024843e40c0c4062000b818109800b20360000381e03225034144007042c001d0000c9a170b04042030b40d110441c091040c003000c1d86c5a018100c0c1d0810303504c09400c540d01e4000e0900f030300040040014001c803c1c500d041810709031a106084c15040312001c0d601c00d500d0038a1035020742011190200c0d00740c046010000c00d8140001041c030a4241100c2d0b0b23100b103c15510008040082100c810010400c108807807010b0b04405207000b0703465100344a10900007042954a540060841d642da911207000030701c3c00750844101c10b08040460004804000b50320380401c2a01c1300040c201d50030184220540e0002a02d46411500d070801c500880b0a500003100e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 499415575 1250 499414325 499414337
    0x1f090209010c0203160f081605010c08090604030602043807020d170c10020a140d24080709090807080a11060403090f080a020307170a0c080c04060b1801030903 70
    0x480580d604214505c07000404028030b06005152100c82504185217034050007444c2c10090702007880e03c03036201800080340c601b800c000c010075400c1c1c44c0003072072031107484185030340510b0119000c014001700b540500140c5515000c020001135480003441c1d0030354124031500214446801855240b610000c010705032003403001e8040c210050041d80e60007410b41c984c03202180210004660b0b02828a010080300070400c00f59001189020b0041d01c000f0100000071910440c032071000201229030001da980b207200035582c1c4160441d03400c9100d03118568040c0c0684200312032489400804a007070900c5202c1c0300e0140d54001c042602e406840c0c0d50380c0386e403034001400c2c54040c400303203c80800d2000011b020091060b4402e41d5500705084c200100c1034241c00460f04144c1c44c640c40ba10001006031000101401650780c8000b030410110300c3c0e120403a14200c4520001040745400c7c1800203096200094102240c58080341c040c005907440f41c0e07981c5128055030b90943c030041602084030030994040c0d07004c1c5a00500900d408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 499416825 1250 499415575 499415597
    0x2706101403010e04060b1c02190b0c010b0310110313081201080a0b07090503060a1109030a150608030a0c120909020708130b090105120613091a1f09020901 68
    0x12540394200343d03c54041c607203201c000c110410025103e803035884242118000d80801e0f030f43d05080429182540300a002d11000085481d1442c000344050004047c003004865807010102d1303401d8060600544da01e4084d2150701e0500c2d6030800f03140200760480242010349415035841510000048111100079a501c01c0d0801c549080013290100c0140a440340c07000800d43c59006140080c401140241984104454800c00b0320031980c0110300c0640004c4001000308440c44000c55160407031140e00b0000758035100d6800c0237070402000c2100d80241d014500d60400419580c2d00030a41c40b4811040000005901e0400300c4000450740240301800c3d20084c40c1c0040d4042d1100001ca080740d0003c1f80954460300c01003808104881da801842c005400e104511a08050100001a040d070190141610402000000150b0f0545500301d2a031a000c2c5440001d1103d0180c1d03003031030942d17044941480c0e800003c04000080580303615620122401ca440c2e41400700040c544482c440080d00104a1541006914000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 499418075 1250 499416825 499416857
    0xa0305040f0606031a060607020d0206090f03060106110f0c010c0f1a01091b030b0f13110d05090f070b0a030504050123011701090b0f0402190902030105270610 70
    0x241d00c004e1407050090001226004c5940b90301c10400900c032522915041102400580314901e0524001fa41695a0303030b00c50300140001510f200c068a0804d41502c1090b00001d0220380c070400740e06110070750a090b207008100d510b141684400c4406100c40c0891083c4158200040c017190700c80e030000340100c91003140c0e640b0050401e0050315082c1e00c2140195144c041040541c20100c43c81d41800e5680e0070104034031000c1e10089180b402c0c0c0d0a40251180e00c2c00d00d1200c1402200c0e81211001700020720f40d581d0340b110100d50100041c04150341000039407103443c0702500c290b81c00043c880150751401c2601ca050103074101044000c0d100007003003100c05540301e0303040c0f0132a10083d0400913550004007510103034039070424005400c4030365020000e43c40b031f0f0b0608030710070041074425008a82010b502c00710803030f2070b6a40e8008218402007441c89500110303d1a540002d0321381e10790303004e03505840c0d088903280c8265032110030640f0f01001c010502d80d0403414007000f00b452840e1510319490760f45a1402e03c1088420090f070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 499419325 1250 499418075 499418081
    0x30f0f03060f0108040507030b091207050303100e040f02210102070c06020f15010510110a0302073b1b180405010504090c09020d0239120a0305040f06 66
    0x450102148003000340a05441c0c1220000880c460a2a1001c15442d1a45a06988140a100181005140ca07002c5400d1000038480311a000c41110102559401d081c50b0050342ca42c003c0302c0d4480310304440580132030750048004039580500d4120850700700a603000d40070880b440b190080c0c401a85001700c0f44101840c1003c0c000751a0007405410480303c0c442c9801000b0381414860202e001c0c0c90f400c001301013400e1404a104003415240181d40407200d486500f40140c81400341200c900c0c00c03501c03a00c0007680801d0390005082041d1211154980b000300c0c04010401c4020010740c1851072044442c0c221166182c107800c05d0b056020040910020945a403030311204100c0d03000d1000c0a80003000306c0700300b2819080500815006140c00e4500704070080c0c2c10780b10141c0c4118503000d11006550002808042c100d15601a90001d285110440304840c0074221a100740c44201c1c1c141c502289240740604d454588040b07948010007000103c80c2e8039140700140110b00401c0001c108680c02ca20003020203004c074004d44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 499420575 1250 499419325 499419337
    0x6111201030f0b0c03060307031b030602030c07120806101b1202030c01060f05210106180b1e0102061305030403120e01121104031e0f12030f0207110909030f 69
    0x982801964981014090701da001800044c0b51003040041c40141d0b200010007030200c035080490f6520610980d9401c202c120310315400030300740381d0000c42032000c92186100100342042c400c92103142c0d4400c0300c2c80d0503505544200c40d0694007108511a00400318000d0640b050482291b800045510340e1a03565091603001a601c00d00c01640003190f02d0350036003402d20070b0b07501800d803800c80c0f61131407490000042e1190080340e04141c540441c0700a00440f00009402c204054082620030708140036582500d00000d1840d1801544150220b0819051184481c03d031360800b1881079014000715911200c0f02c2c1c80c0003214183c1100d0501c000c01000020910415403610311032200d9886010240c4801c0005022031684040e0141c0c2500d0300e4001c94034907550038100c500300e81d800105900304103d60704088440c9200140040e03c0401803201060400c8000c03061548100482d803400c01400c2d01c55000c2038124060080c0007443d24184203140200352800d5090325911032040011240740c98044030204110350061 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 499421825 1250 499420575 499420583
    0x807061104230d17120702030a022e110c07080318041802060c15040503030a24060e0d05010e0a020a14130b040213030302060106090501080405061902041203050711040207050a0611120103 82
    0x101e400310316681e050140400345031021440c0b40c0c212440411001c1c40a40c81c3c0e00c8a02007980e03170920300b0100d848503000d40d2040300c07485059503a11944c0d07520380c0784c4940c0600144800302150ba40207111d41d03d024840e1010800c035440c001408a5820750074494564441e2141c184507200d2541c8a8234400d100e107a4803845544944040c5880c1d05094841e0815103030103813000c91000c5410840411001c0d00d4070b079038600711a03940c5000c9000040700e8000ca10324216203003000c0e200b942009a42000c440c8009103044100b03100350307180f60340c03c0e503600070174182e410008094583c002403420116849071819000802c20f2a0010801440d0122602080340990f61981c400c5025030032150041144030340250145d80103100a090880c4945081d54407140c90355801415031000390001d00e00b241c01e20010354107032406044082d28600713103000300b810040c150f50002d100445114903403803480c0e6a141071a00a403902e1035440801466101c0f10b80e600c2c60081c21400505101b010710506c00c5000c00c03101e4002d400e0085000f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 499423075 1250 499421825 499421827
    0x5040c050403051009083f1506031306050406020d14071b03080403110c0a0803092e0815030d05030613270807061104230d1712070203 59
    0x2e18038100f803c0c83c100e84550f015080c50f01c441c0102044c02d65007190001581a10180d51000280920700d0140c500c082403000303000f96429480c803880307165011850243c0d50202d03503d10f204806c142006000d1004455100310490520702210001c1c10640086404c43e120310405400d16804030781000480310080b40c02c0301208854070500180c0343d003210a10302810309002c142590410507840140402101500050401565034410744105c541842180505440140700f646405c1da42d0080307a42c0e9400140360144200410700d5840c04520740070505429090b150b003007204044008100550300044010441302102c1001e141500c0960307003d000715848460700e0384900b601c0b810030005106011950362441c808941c50303c450700c000300c542862410f859800148651644941c5850304011901545200070006130030301c400c1c410510f8004001c2c006030354000c0300742108110700b11000d8084c14044000d03a9001004041c510700451000303a000c428120400416501d0041001a2080c10204c102c0301d480060304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 499424325 1250 499423075 499423079
    0x302010f0c05120705030c0313030314090c0a170615130f050403031103040506190212180607020a081c0b1216080106051302130509070c0515090a0f050705040c0504 72
    0x50b16111340c1000e458035249040d0b241091031901c4c0c500c8090305243c8e0700940800010101b5120342c016003181049142240308600344103642d181e840728007514940c82011481d0002c503900c400d0920b8800c2c405540d900400b216100c0f20b0516414100340410903030007003958001c05000e00b000380070700031641c84481c0e0001030920b800e01300141250104079100c41561403c00a0101140000580740c1d0886403101040b402aa102c0000c0f034003d00c24000c40608000c2c0c00403c000460841020001400040350141c503219503442004030707100c00d44180b005003400d00c02e0040b800840c41c3c8114209090a5101001503640040c00002d54000403005034030040780d0040b28261001d08415250000901008000307111581c14080050f11151050300c18000c0c803940420725402e0321000c0400c000080501400c41d0509041c500c02c0203008a010b0001030701d881c420700c0a1000340006000701c1621504c0c500e805084040c8083daa440a018400207080d1030620a1000c0882d0a0755540305884c3d0280154407040c0c0d440d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 499425575 1250 499424325 499424347
    0xe0a0f0b07030c0c03120c05041a09030f0604020307030308090a080f03090c0a05010e01030915060608010614040e0112020a0b03190e030307020c1507080d0903111c0c0302010f0c05 79
    0x3d034064410001c0101800c8020002a00010050602d00d00b441d8082011140400222042d00542e48200348480c03c00c607001c0011410701c8004c0c44a1481901130302c84c02800380005d59a1140181d400a4050340107603010030100c3d12510b030003500868594155240b424150f11441e03082d400070304103d00d4007a400028021101070070800400341000a8942072446071803d00041c0c594505004090f05241e00c499041003040040014100428440401041880c1c0c41e548000e15402e001d01604020a0900d51310030781c0c20050405a804440820341c81e500e4607070801c0501d039421444010708a800078107801c3c004c5191100ca201542c490303801d440d070080c1607902c000306000640c1c5401d690721501e500300300706204035107a011441c000c4500080e80c110429120f800c4c0b0540c01807040c290054140440401c0202e00c5481e6a0007041031180640d44000c0c0841c1c103c2141d40d00c03004030744440155078000c100b0408c90a4003410000f40041c0c002d000005107007242d55100b4040e00d40b60082e0500007000024489008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 499426825 1250 499425575 499425581
    0x30e031605010e19091e110a021516052b0507021905070510020f0109030c060621020f060403050114060307060518010c080702030d09030b07021f0e0a0f0b0703 70
    0x2c00c508132403542c035100100b002d04460250a0040000903911086164440e904442039440c03c148a502d08102400c054000c000080e04410b043c60014021403031480018000f2080050146441003a81d0b000058051000e886952182100042002c1c120300b94044101b122000e9148580841401161620f403104000b410562001403440d8040038910b03061000c80c10006510040d501e09450b8411400b1804800b61b10704421104c27030712a01e41c2010101030806a00030b54a07240382d0300c0b0f941c2c03d00119480e034100c0c4004070780070340311216900c0c500718502c0c000d46001a41e115844402034165454903444e6210b40d801e4581d19140d6602a003000b00c14002c01703086c1000002c00030425032170890b081260f024286058001260785007410411f40074059400c2c8941c1404039045075900604541c250200c2c004068500101c511007074818200050000e20380c1d50002c6104800c910030380d00040c40369007201c03200b0700040c040300c0300b11900ea00c1004040310003e0703110803841c40c04c103005840504251424440c000c081d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 499428075 1250 499426825 499426847
    0x9090c180c090611031204110904140c06190c06110f0711010c050a12021e060a0f06120303050c0f0703180812040e1812070204050903030c070f030e03160501 69
    0x10070584c1450041440400b10a80c3c445850006059402c2d86840c00e203d0340c65126405415440300800003400204420082e65400d2200b0140903180d43c80d4000c020400980148103524401c80201800c69840c60310034007008201500c0380c803000880340d0301000140b0898100e1001218070240002d000400e0003501c0120340d10390542480c056003c60300b50f9440d107445074200d010041c010f100468002055a000f8096401c00454041002c034164100101065a9183c1034440140c418905515103420203410b0041030182c401b2210225000b1009640490084c4401002500b5050007413200a110385104030042c07910314000da9075081025400c01104a103d00d00b40d004501d160b001d144080c032026000c0050b101203c01400f480c1c80b01d55224500c13a04403151947c28071074a401805081d0646400500144c89094000c0d01c2c20404c07990344040c01652880140d5010404600034402c060000303001464a9510a100e4a800ca0308442c800b80440e00d48172032096a505046007000e800e00941d640b040680320 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 499429325 1250 499428075 499428077
    0x6020c090c03060a0509091203160e0a03110111100c030204051c050a0308040f0b18010606090f05061b0d080117010b0d1101020c09040f05010510030c09090c180c0906 73
    0x31840c101400054010740f25071082600400040c40000c120f1f260034031034043c0300040c00c07103010380c0c9180501218272101c0c81100f07054042880201c051505041c110314044c140c81d230008400c01500c40c001c0056505c0007207858010054803410708060713200c0c0c0a074010500206469180580c685013824100708040c214207810410039105010b0f800e0209000007062004240c1504180d0380944032030408072050b01c5807800103030a01c1d00e814244074400c05158804001c504110008001d8161038850480c0d0b880040d21a000c2180e84600c0140301e14a8076000800d6200d201115006803040c03050402c41c01c0915903048000800e00e0200100001140054103182000c04900204a0015100e0004000c80b2503024060880345510801001c941d008004a94022200900191091420f460054010000000111102e50816021400c07030301180c4802401e6946c40781624944604201e000401170107040000d03940c0f48cd40900014980990581d0b03001e1f002615200031841d03411145010b0407000003640694 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 499430575 1250 499429325 499429327
    0x27010801061107260604150f020901081b040f09090507060306050105180a05030106260c130e2a04140106230705120a030e030301060c060e1606020c090c 67
    0x228a10004120002914003505402441080c1c00c02204e0307805100340100c094600c9104140401d0000e404024032041444031400d11100c5a2000021b0584c001d45e0300ca24081003100010420b10300c1000507600c0d04554001e246820309955154840780b48403558003140b295595060303050309001d42446140090b011074102400b000e40740c0000200700d481092626280e8554a201d91005981c03108920b2004090050017808004d44034560a188881c1d034080803540d1003611b00410031400c4010648031030300e004c01806007401007c03800c080000780801c40407900d198010070060071320100005002035041d1405a4820700103c42250511084624030709224881002480040041076032080f800625800d0403806d00715400703640b41740000c0302c0c00390100040c03803801841558050840c4a8002e03000d031010554062105a0304881c03003544910080c05880001490714102601140c2c1c5e50f040201009082c0c2c0032282c000c48801d0348103103200120b070080c0c0b0040c0c0011000c0400d0317183c940758250300418031500392 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 499431825 1250 499430575 499430597
    0xf040312050f160324061701031109070302090d030503090f1506040c0c0515160c080f160b07050408070503030301150c05031606091e0b06010806062701080106 70
    0x1c0190302c1d001001c81142c81246014a00c01d42d209401c5090149554826082903400c440d01015604500740200760028442845a840180514094904882d040000950b46e0000c041c00d000082034020300d41001e054007080810b40d00d45480300543e00c594000d9580350380720700780a1006810400290b000801f00d0b8048481d1141601103603c1582d0032060481d000100000e039003800380c40c10002d00c2e01c0034045004071407080d003c110268003850b10451608685080c2e081c0c1e01c2d1420b5841d50342c2c0c45c0c13024150382070a00c04401d007003111800030250f400d20317620158505020b41d610f43e17500100444240380000e01c049000c100940e0704024450103040124055800c6606003404c8003520368007071100004110864442e007080c8136007071086608113502e03403888107a940d200b81040005000d0310700b03080350360820382880c40240f13900ba464412105948004410f0003070302c80380c1c011950183c000c0c00e100c0d80100100200c03035182c0746802410040900340600020054151000502407401c16030282042c1b00c825075071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 499433075 1250 499431825 499431841
    0x703030f0201290a0f0f17150c0706060306020c1501091107060f0225032309090601021c080103120806030d050c07091a030d14090d15050f04031205 65
    0x707100c00c0c2c0401084200c92652480001804d1041980c000380800004400204464119a001c00203640300b00000051030115109000e0341c0310300001031105c080b0861004980311010401c010071103e8054040410f04c3c5840380c443c0001c0340e116002216040d8890940e110a070b000f01c1105a005100b50402001221444c0404500a100c2d20750003d00c02a544c9050400c00791543e816101001c400034515007a600b1203c001190a90010005602040c541001d01030f25100c0d18148440750394800b5001402c110220050000750074001e0107540c19402031840414561002c200c4a4000035880d941c3c1d40c04a52640c1400d81c00d002120300c240f01081146401c100c03045d10001030110648103e482c00c41d984e801c00215050600d152030f00f04840c440d040c103c80d100078207041d0400c4031001c0f80450030350310451001c15003074440500f14a050118044240205140c3e0324108100c90704503409030b10340b21a8502d10a4200e422180708495510004500c1010b12041c1540b054006011010b4401c082286040c2110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 499434325 1250 499433075 499433111
    0x50a0e01150504020c0a0b0106050a090e06130207050a120c170c0a0228090f0c02060105010f1202090d0f0309120f020405041a0c0c0c0301090812040318080703030f0201 74
    0xa801d00442e00042c45c40d038840070400036103030401c1d0490641800f558403900300a2160303024502c0c20000803021100400e00781c5a1019050083c407000f032090501140800300760010b500596400e840c103014145003a00424018100c603900c6030503e0351450744400107490524020840031824507142ca034188001145003500051060f24550121004821244000c00310403072072000050f00850366440c400700150a0100d608094036081170b00505101402d4003a004a95803182413081c140000c003d11042c21826004140f9014401075154001d407030889014007291442040741002c8600c4829600707104189503000f00e1300805400d11500c0f0032403800c42902c8001c140401c0d40b0010344126511130118041140086040c00c0100058061980915045200307561381d412407101032020380221409410340e451b040c0304d20f00140750301158030707420000248410031600300300510031410300c000318211440089281001c5c000400041005200e541d05601d8010300868400c810001035a06040e004807121141071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 499435575 1250 499434325 499434329
    0x220816031112070b0d05060108010501231e070c092d15030f0b1b040302060f0c030c0a05010c1209053406030e1204030b130222050a0e0115 61
    0x9600e42c442c0001850101d040c0003c0b940011203030400000e0701c03008610280c00a6100302030903240d440050303980f00010342d29151664806490307a82ca52007001c1c89501001d02900007601e01c8903c08813540702c60595207030543d104850555a00702c40140030032111005000c0d00c00202d81040c00f4003610340e220000c420480091104503e00745460b00d000301c6601a0880100009542141c80491407860350b05001d1241c40d0103580c0301d51590ba880202948051645017240c04030f950140131146861850320013002079402000c0700c044a40001c019040c2e80c00c800f080401c009900480000032000d4200701e0103001c1462100c0c03042055410007030f150010640200c5c1010f14100486104c580c803603031000880884210f00075101010313540c42c00010a440c0d03410380c0903648420f248800c44541c0122a03952246500031403000410148c1010000f4408131078050100131004d1024214000e20180c0c000301050390300407510709903a265943e1081007900c8009020314100e4503287c6008010107035242d441c43c418003001c0c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 499436825 1250 499435575 499435579
    0xf0403030f21090c05040204230f0a081005090705010f030207020a030c0b04062c010f050f0a050a021645021e090a031401022208160311 60
    0x30102501401d005611104100121042d641007000b044085040200850070054034400302c00180410981002e100700c405499443e5a29440c0868811200a0010710501ea444e044a07030708a04210310384544032640c0c043d0440da8003a050b12450449140b088a600401c0e203602d0b6401040c0070816a6001142562883d00914000d607440c4142d00125202098a50004006010b59000020103054110141c000d40300d440d51405080c2e01d00400c0f20303803145480344031110150f10b811202080c030360142c0c1c0d131030060048904165081403c000c01c46011078100319003950110714009140140c055051041400442c000701030010010308010004500d9080c11084294041c070084807190a1400e00c03041d04840c00e00085011051030032030000c00003a40103c40101c0c0c440c1c600881e4070510103998000e95504e10b1003d0800c0401d0b038507503102c5154000615100b045295401c102d006d0f28000030b101c0740c0120005281c3c0452070585489021454a81480341c3c58400318040201400082d2580854441013501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 499438075 1250 499436825 499436837
    0x90a0504031b05010e070602150609090f030309150c120118151e05010c1e060902060a0e0307080304032109080f010506090609010311101e02060a060801020f040303 72
    0x80d51405a544800001c102002030002504141c10060150010425045480c082c4c50055944a80c140e0703a811081d00101950311525000030003908100140c164040d0030501110030313010030001024215841501c48090743c0d000441026014142001600d81189545031128640f2420b5041c4200440d8180100b000c201e20b0302c0b54a81002c00f035600084200c0040c40000c00c2c081cad540e2031060115091a18101c0d0301c000ca019030004140d0300400b101c0821f81e40241b28240754800392208041298503c20b0100d13595680ca061000150300d801006e4a10710040341c40d0740c02805103100030140b8143c590741c0a440e4684c0200010f00008003410301c2e41c1c226001d54601e8480100039000141c03040b216580100400388035080c035003400c007401508039500030300d07094600508544a007005e110702c011003400090303c0b80101e5410020581800e20400506c25401e142c01e03000c009001601100200c400190b05005074060800d110301225507210b01070003480c10170002c501e0b0030141c4481042a02a80c032019050040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 499439325 1250 499438075 499438081
    0x4051809150402121002030a0606050c1905071710050a450b01090b0f0609010f0e0405010b0c101839060e1014090301090b070507050d020705090a05 65
    0x1101c442c01c2201800c11000e80b02140b0481700140025041200c001c0500c070308010700018828018412100f012040034050412100b50341c051140300b001c2424111130b14841e04e20005000740c0c0200b0000081394500303010301403150b0041c0c0e448040e264050b285801c0d151401d004004100b048070010b031105142068070428070341888400034000500d41c5c9040540403013001c0c01504114280403410b05076107030340303901700800d50180301402400f1000f40201904003000304041030543d80241c41c007810305644ea10340343c90381580b1080454103480081e40000707007114000c2204400100280007214008a211000f00070100710070410b0101030000481c00740043d0451540c060f030318454004001c4d001c8a070565070454240b01d24172002507409641c418440003580f22005901c1516040350444010011a0f035010300c4103081c2c44441507260b11120078254150743c2c80a40100080c5842d840d1031103486035071220740e117032070a07828000e040c00189814102150170061081c072156403002c00302900300c10503003c005001e507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 499440575 1250 499439325 499439329
    0x40b09062d0409060e06090a0305030414010905070b1e031e071701060804030e01050a1706040b130203040b1f0603020306010314040506010f06020c03060a0e030405100504051809150402 81
    0x200d455081e9000303800d011200c024041540c00c0501c464504500301e4029540700081251114401d03800280001c0c410004078000c100c4d4402c620901c1c014000002400c203c940d9207041c90018581d204500248000c540344401180d010101612021184126499031811001038115041d2000801001070443c4001c1103259109a81150f040c404440b424102540c5480d000f502e5003a00f01e4044001a107074002c1d000c1c281d403041c42512a04c41d43c9841e002c10001d11900e0101201500500c0345800a664410351411940d9035980c1f15030001c0070324401a502e06017400e007800c100900403c0920445800041d4070340310400348024108a4015181c010f032a174503241d0040f4064500e41e26043e600c50244410300c0240240810b40e07034101c83c3e417081328090b410b9a41d01b082c3d840c0c1e02d8030b21000394550455400194003501c02c0c0c0003080d0030262038099928003501ca900040f0b5000f03803074040300d000841c041801d010f81d007080a85014030201c4000388649924103c0406665100c89102003070001606502040c115 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 499441825 1250 499440575 499440649
    0xe01020d0e1e09090102041a070803040210021f060e01050d0c030b0403050f030702010b01030e1c05031015110d0c08070839100608070e100f09020405040b0906 70
    0xb658018141c18441c01c045203c10b010350000d0182c102c540303109050b6920300c10380d04411240d1030f40d4403640450655640703808009105103001c031180300b503000b20301d000c904103043c0074160f8140140c0200002089810840001c6030064140c0190b4002c6002c02e0703003000400c069020401c00c0326032111049800356201d207800c035042e00480b1900c2900c0c503400306c00d0040310f903019049051190000e03a010070030b0312503a02c2c280b80e8640d0b09059900a000d0b0001011120314403410041d58013901c4080050056030381c5113074141880512203000c0c0001280080450106c080c180a1100e400d0342d103140c10000d20310386454a45880c0301d420030041445000044401145034449055000d05a9044c0e0460f405036800c9601600c4002822120156010f103104050b0f035440c15101e444140c4d0181d100620425043c0090040c24074405000203140d07071042240050144c4a0b0403441024001403100540c48614200500050343c0500e243c1c64803401d07082c2c08120058036015030751110621207014039010b03c94078507400100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 499443075 1250 499441825 499441879
    0x609031b0510030501030605060405040b01060e060c0f010b210309010813020405070e011b080d0510030f05030702011e08060105180405040f110303070807080d1d010501060e01020d0e 80
    0x4070b0245044a0464155004904070b030300601c0c4c148190354418040000310340027110010101c1c0c44a000500105100d400300440450010b0034480c501511003241c41e140c181e0400200340540c0d1600101c05460601040705e010700c6070342d01c1102031580041c0c07090315101c0c040d01c50024108041040026082003001881801031034021f40208018200300c02c0080c4480c400c880b00070702042c080020382079280b0200a4040d06d0681007110b107030500c003191402001070007010f0315060b1000c0c10000701001113400c00f2800d5041d40c1c031890045964a00510002d45038034038001c094194044001c1010301d40c26081a545e5500050918086075643c40624a8039941512680543e070843d107070204100400a04101d03c0354524003c604045440001c0b00030160b8a1140d20300062490905211450002c1e054002a011180704440b0124113a142403c01170843c44007408100d60581d1140010807140d9041f900c041c181041c21b102800790400b49503805814000e011214134092031918100581c030b82c18027909090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 499444325 1250 499443075 499443079
    0x316170703030c110a0b0f0705070506010b03010311092205010e160302150f0f071e030c060e07060903170d0c02031309090b01050910090518070f0609031b05 69
    0x80c9400e51410010000e018500020001c2140303006241c2c08204000b0f404010603034018090829540c40e00c2a14001d200050504010310106200c0381300010000e2088078040c1030803000c0d5030307282e41c9907041242850388080e43c0d01c0e00030348005041c07000c01c170040d804c0c04c6640d0041344941da15610300d52a00900404442c0120710340d90140c400344816480000b030344182140d000b2a0844802181e42071a0071051184048111040104002e80b0340820002e0014001841c01201006085150014200e14140460500710001303890800e03c0800c00c112881103d8410299500900416040900103000a2002e00025001080c18894200c003029804215403100703250043c140303c51080b0754806035032604040340ca54401d000703c2d200412012003074032405c02401e40007603600c00c0700d910308020300ca410300d000b0b07020740b10354000803a02007600300490040c0e07806004815816224154900201410034025801084100300190030800c1550780c0050513005883d04104070300d100703440c400d04c4403403044a1540030076 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 499445575 1250 499444325 499444327
    0x30108070302130204141c0503160614040b07120b1816020c150c010207170d0b09010e070807020703120206100503010524040603020a03060b10020d02031617 69
    0x21501400215200d0100da2003078908881c110b5444807003c09030f00590143c0c3c5511074903083c4604840c1380c6a0041840021f20f0102840c0c110881c1d1500c1e402c55100f2000444d00d00f261116000400c20903100742058135000c02c0c50f402c80c03800c2680d604c0d1030034a0085c09100c200031a24000c0300362503401e5401002d504100406284c000300341d01d0b01c0ca6441040485d4001c0c1041150710080701b03100d0011910502200c0c009001c0d004100b02c60038124070310f8025150741040343d9801e006a20010301400e05010910188050b001e4031132501c520f0700d0040e2145480c45c18003686058004014107011004007941003c0c00703052101c2d590340c509900301e190080b241e0020b05220700341110005425004540e482c001c81c2c0c40f40c0d003000500c2d00ca00901d42610000e440082c80744020701d6000050f0f2185500d00444000020804074180e90b5070f070000b80740c0107843e420543e03150780d070f0f038a50450700d16243c0166244858280007400001140e0032021751039002d40143d001d015101d8001c68410041c20042050301410400496 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 499446825 1250 499445575 499445579
    0x100c090b03090a0b160806061605010513120c020303030406180f0b0a1b170702010f0623040c14030c0405040903030b310f060302030a051c03110a1b080301 68
    0x6599203020f0702e04140e800c1e080403004200a03101c0018901c0390340c2802d0311840410340707998061207407a5211341d514000c003254000300031002610a000c1c581c0641d1840b01440c07021491802c02c3c8400600a030901014002c1c50342075000144c8021050741c2c1e010740c101d9000120030075114507000007001364000040c4202d800c00340d4903040101c9200c50034054400c880c4100030300090450400c0c2d485005140100c04a01000361000b6400d6802030395a0740103002d8400400c11103030b8010540180d903002d4100360f66004402c8a0b0f0210041182c030f45440c0458119014411030558070340c003900740e0f1510503104074020000000070710b854905100f201c0007072001030010402841c013410300500614004142c64400d0020b01e0b444240c02e90a001c1a2002c40201104544a0040116000c0003030640031042005c0a4803070328000096034080c8000c4201ca0300460103040d84040e8240c80d1008041030717060711424546081071030340d640ca4038002620306000b11030802d000b0200450b1407840d10204c241d00000e003009400000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 499448075 1250 499446825 499446841
    0x3080a0503070e0301020f070b04050f0105090a0302120307080402011116061110050105010e0f030703082a01061a0a020a0b04060b100203030f0411060d0603060b01080c0c100c090b03 80
    0xd5204500c1030f030f40ca480c00d119103820103090744640290b4520350082803108d01f0200303110034040c03904a8800e40482e801000403000c040e00b92201103c3e11a00342d04031035146010f00d034043c410201110980c0902a2a40c81c1c40c8101034040c0780040c2c4064100324104034080d03440e00041002c1000000c40c450004040355031100d000302854002d44e151002c5008a87c122401004140501d074182c0300161070304071308103210b07006004405d45a404400c2d4103104803a070000100d0b40c07400c000e004400c0b54004244041c80c0c80e403c141080604504145002c2c1c1c5000010045100700c80c887c000800f095480d61556981d40c081c0481c9080b055440103005210303500b042c4810040a640b1500051600703981031000f010b40154240d8880c0022600b2610000f40000020300184014240d41c1070004010301c442e00388807040c002d581c1160303550380084801640d135247c091314540e003050100358042d006017246850141c000c50b032582c9405c2400e00100744261202a40010580690450000b410a00e00320640702d1504c0d142c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 499449325 1250 499448075 499448077
    0x40b0c0a020a081305041d06040b13021302030411031203060103020a090b0a02070801050c120115020316140c0607050a120e0d110f060309060c03061c060e060603031c020c010603080a05 81
    0x803030280300703515000700007c4090983c00d43c00040c021900c06050995110340303400c00310703140007010444030002003006000141d440705076860495004840041c1c80e0301e060711f40701a206c00c4910020740b190740034000007101c145444003100d91100d0286005a12910360a4060b00d80808c42d0300310288101001c82c5409425600042503030407600350704000d00c40c544032014292803610813014864518400000184001c1c1d0340c00091400071915441103906e844501c1c01d803c0d60300d9502d550210707041400c0114200900c0004c106444410300c1c1194082d20700451955a00d80c0c9428070707000101810103c0c00100f22044c007074411688004006006504848141d180520800310118246407051a6140c44525141008003d0720b00c555160707401019183c5a0038407800c3d45d50002004c085c1e008803810414072036243c5824401031039910400c0d0110707a400c0e00111183c00c1840040800d80a584240005180180c10015040c0f60001002005a84071500d51a0a015041c00c0d04003504048000580301c8031541d103d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 499450575 1250 499449325 499449329
    0x40603030f020709020f1e0706060b04030524060405150a081f06030309060804050313030602030f0906060a2904080d020d030b01020637061706040b0c0a020a0813 71
    0x82e09584280340c42e40c400ca812401208013000030624140005008884101c84050f0483c20041c0c8450404887e42d03103c00a946a0f41c001801564000c2410003c0080c10001314000500105510748901c998964484980b80d00074080c41c480c80d00d4802150505107061104590140090030b240c10f8992100d03000760b41d0f080103c085007081c0941d1501040559002d201d52419a5072555483c00040c3c42c020046170700200c00f400681d203034013003000040011901c1149500081d4410000540c40b884d1212448a401500034918040c030f411440c1009040c1d503c8419100507105200c0640c005800003e41072240388188840001c409040040c000c01d4160700003034500801c130019400c8540a2444c070700d040b0103803001109020701603800400071410054100b02600380050029400300d40701c6050a06090440d00114404034255989603070a200c0c18810081501110340140c0c010021410aaa15115014001080c001000101140c0d0101c0284284814062030360046800b90f01d98500b4941c91411003107038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 499451825 1250 499450575 499450577
    0xf03120e130513122a05060c03180105040c050913150f180501020309010b1903150b0d0f020103050c040e160513030318050a03080306010c14010c02060a1a0a090b040b040603030f 78
    0x800e0555900b020442d440010709a8440042c0203d0344230840c005400d42c1025002c2c5440741c1110310443c203501824860a0301c980c1c0112803030300405240c1001d00180e640060410b045058080c0044001315540c10341e0710207122025240029140c01c45040c0d10010030010741e48400003071040030308505001c01500a180a90079060003040340c2c00340e0504100c40101e680340f00100d074249061003007010440c108a00f40003010010004207044e88110300058464801c0c03030040fa188030065a000f810355a140c403410b84e200241000d22031400d420822510514000241094070340418010140c080c148030300213903000c1c40e8080ca0040c80458807483d002d0518040b980d100448480c05010020f000e02d00f410006048a4000b0121465900e48400450f01d401e058181914071121030550340030551424461200344d104071b0f50113040305041401d0080c042d03d0350700204144000d540000321200f90744055400080726840d510005170840b00e1004600036280344407030b1542c800d180c14400021301d0b800941e0a9014281 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 499453075 1250 499451825 499451867
    0x5031203091b100309030e061215090123060d06120b160e041503140708010509070605030609150301050c07030f0207080d0507030201090c0f03120e13051312 69
    0xa0802240660352480b01450b84542060f980700d003c3c41c000d5110a000d94000e19296000016120100348154440c101e14000c00f0142007c2141010f04c444404110b110b007141d5043c0d041d403401e03681e103405c0e644a45004000407a0403035908115a2071104890345000490300500245543d942c11910803818458140d8010605c14000b0381c0e0071790a040c16140d861415240d2889080c0301006000003086118589003001801290100128010740c03d000c26441c40310004150303c504001ea007034250b07030000c1d12003070299000ca40240000b41c0c0140070344c8d41c49581913640c0f004540d10f20036038152140a0010341d0742c240d441d200c28810729000310f000a00c8454084e4640c01c54140024604a030355400c00c0c811640c0d50303001449100d10f90340c800d00042050701d00900c00882c1c114025182e012000718a6403243ca900400c4400400401c040c144d183c4204401e14108082811042004100540c14254440706040d58400000e100d000c5102d840d8081c040d0000c804248103643c408014141d54641c0c008000c10481c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 499454325 1250 499453075 499453093
    0x210f160e19061101023a0e01020901030c09120b28020301060921031407051015061815050f070b01090f06030c0e04260310060801080a0f020a0503120309 67
    0xc014001c40314081085406c03449a03200d00e40e411000303c852041512407400c4415510361900200d4024000b111903036030300040c7d036203150354001350855004130000f600740010104200000190401c00004071500640d4200e280d584a60f10300e007070900106907096101150504100340b0b08815406503040c1c0765280c8270107000c1d5071900441c0c00705031410401281c40022000b102000640b0543d00503a400242c040c81c24140300407652503906080d05203d82190445d524405040a181014a000000c2401e418034036843c3c840c0542c501080800c500031069245030b9689140d0380203219001b260000035080c044151607034814a018408c0341800e100301d854407400d0010a6002001c544255000c0f01d900c006c1e04051145810044603c1d500010000c4c9c901088440520007010820341c40da8903041510b0f4400e590340e1800c1f0740d045018003595001001000310050040c0f003010800200540482d4200741000d00c07140c2c1b40c2c800951001c00d15000306415004041181403545006405180201180b6095030807010f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 499455575 1250 499454325 499454357
    0x6063206090607060c0e06070b0a05161209020d0b040b0f09030c3406020a2109030206070516060e030123040f06060515210f160e1906 59
    0x8000c401c0301d50b034085810031041c000124142d10207201c841d140d090a80d00b03008000300190080c0c01c14002500c40c044440b041000d02607951144961011282441003c814003c40000f05007000041055080503079138080c25081d96510360030121f0296009000109502d46841d040300f1070780c015504030b006040c80001040760700601106503003116508400a28501c03043c1d240242c048001084485581c0f00004880850000c40c0003001700036121940007080d455516250142d45181d2080041205401ca0300c403802d00c1da50b003c2c510b0700807641c04403800c0c1e0301c90540c1d082c013509100c40d5000d01d2114084519000898a4019000160b605000c038001c001d80c04010281f003200b1142810520101c2540600040000b0300010348050154020b80b0006502503d51022820082111000004564011442d0b0f86080c6035889071092401c0000d410140d6420300081c0b0b81a07055000d007605407141c0118541d0b0802c1840b4122509040300020585110b910308408940319501d05130203203000080c200c01c0c1c06d407611 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 499456825 1250 499455575 499455577
    0xf09030302210f0c2a01050105030d08010b0d0e01020c0706020d020c0102060f07080907030c08060f13021f051e040306060b0a050412020f030d11100b031906063206 72
    0x4a90308460b036070182e030b2990400c1100b50300c4000070b031044036201a103454a40038074517072890207948414000101541080105483e0030f072440702c92000c000704c00005111242605043c1c1d403480d1301064011a640b440813001030f02a000b4911003001a21a4441c00141507500140c08919500c1c99000d4400d215411001245c49500444003001c42d08003440225800f940f0440020b58000c2451064035040b07501c07551203412182890f4494915a0f103d0380c14490744021802c807254010702c9081b42c414140b2255404110b044100c0515642e08a6421a0790101180034400312103040d081c5004c3c81c0c00450090b00d451203180c2043c0025180586415000b007454001c41e4101c809054040d01d92034100ba18040018100328120f8004a800016804a10b109a241000b44c44140300068071040200b1080040140c6010380c030021030145c0c6402c0c13010155207900c011444240010078403105032800f038a5410242c020b0440c1d5840300e01c4a0705404040c03600c800b2041c0011910400e200384a004144a8000300141d07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 499458075 1250 499456825 499456831
    0x516050d0c030b1e010807050f0a030302060a050c0405150c0105070908063405030624040501050f0405180a0f1a0d110303031f1a1b010f0903030221 65
    0x310303100c0c501c010300c0426111184541c0c01400001c0300700b1003020038004414260000e80c800c5005074041c41c4103200a10f040b0138011100b030810f6904000592642c0c4000303580301006064009401e5031900801e030800114070440d0058034015010840d141003103240c51005900c0104656850351924003c075401501c2810443c0403914883c008044030746403601c4100341d140d0605041410401c00540c42031240002006035040c00c21280c442d03076124540343c2c05000502d1065000b12540380d50344802034402d0396000c016070301039810a00c1c0164403240401c0303040c841841150080d580c81500c03c60340240380344000004500c1070b10340010510000d0070301140c94040d03c07850025000e44440c0114000e040d820840344040c0c0c1980105990b542841d4940042800c42c0d000f620444420501c841c292500c003040d901c080c2d0014001801c80d12402c1e80701804149480c01944800c0344010241400f00210035800d410450710780441c1c4808201040c4c00c6c0c54068001c1d88000d0f035015a600200b048104440c8090008501c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 499459325 1250 499458075 499458083
    0x305010906152007150f02070b190903080408060613050c04151e050910051314130c18150c03120915020a0e0607080901030f090204090516050d 63
    0x44003181210944490100120b41d94114900d416001d4540c1c03400c02698008003640c111011034032407803a17001000f101c0302d4640d035030035940302074070400400810038100c481c9184101080d14012080040484040300300ea032000d0801e80300800d012803600320101d01395001d12001c4034020317062040c0e0101101950421200e0911801003408104035098032807500444039411490b1020505050b07106080d070f203a881c00003c03000070740042a800310354100309014016043c0e00341025070801d0070411030304520600e58000c04441118000e40003400c0e884849500e080300740c0d801800d02c00d042c0b858100800c1150800f550900700e5031019800100100c0040c070b015024000c42e40d40d04425195034400340c0d81103903940d200b03042455841041d01c0c0400c880d41c290300c0311060750200143c2e0710304954500814501814010300d103d0f03982081442c2c006207081041700c404900a0a000c02c0e1003040500e0304008100b19140139400509258a281c2040004580c12000d115411142c64881752290140018840302001c020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 499460431 1106 499459325 499459349
    0x9070809010b03162112021011070302030a03090804050319061d100905070b0726180607020604031a0109050108191412190305010906 59
    0x40744060110f00401c400703240100300301250b421a2103120179560a07602c00c4828840d4400240a140d03421820480c0401c01950000c2d440701d409256107803859107481c1c1c81000d4404540c1c01c0d0341c00e003034156009504244504d0400d0340103180180050360141000d010001c0c05a07000c01806c030307215240468a020310401c0e4980001950010386018031036140204005c4041c4c1400200c0384483d14254201242c4504142416820512150042c400352040020b0140038080360780150340301d0b11441034401c0c0d1000c028030b1840d03905009849032510810161865481d040c0f50420181c00218002800f03540b50907038075603510b68800c469547c80480101107070010000c0c84c045110b0507004000600242c00281c89040b1406010000001e0081107072070031000103540c3d88420020a42608025060280e0302c421900c0c00400c03003090100c00000003400c04002051015a9000da90221456a4110303 = true := by decide +kernel

theorem cover : BRFrame.Cov 499280575 499460431 := by
  have h0 := BRFrame.cov_init 499280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 499280575 ≤ n) (h2 : n < 499460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
