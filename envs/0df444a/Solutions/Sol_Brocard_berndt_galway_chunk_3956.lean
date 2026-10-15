-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3956
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:09:55.2044+00:00
-- url     : https://prove2.me/submissions/f2aec7a0-f223-45d9-9727-4c0a0d9e2abf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 711330935 ≤ n < 711510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 711332185 1250 711330935 711330941
    0x6041d0103021906020d050f09030706120b04020c1009240615050c0d1202040909080d0617030301060513031a0601020f030a0206010b0a0201140408070203070b04060e0f031f 76
    0x3640708591010f000c60340d19003201011590f0b4820000568061b0051510789070160025200c030056a8a0b002d061031400000203141980c81d07441039022540c44104a020640c0c28060801c5800c0180c40662600d4440d00480755240ea03d440c10403543da0383c80c02c0b490108015003c559103007100c607071507201000c0400a03490000300200c1c0b00303811b941980c1100c41140c140c050f40030b50f401c1c258440003400105c0b4200c2c41c2031f070b080b09540840c00718a035800c00c000704100780540300d00c60440d4080c240e4540c071062a81c01807012150640c001c400a810880340400d0807600000480741551803514021b6116040121482c00c02052078100502c00c2345520850360780c0341c1c1075413900c42c4600000d038201c031120b101035414552203204902c88100181c2040740140820801003004004141c5240700009201000c2060b0104504041e101210544400507000d801e40c0340c00c00c8090041c100402c0014074007813070000041d1083e151800c903180901d000d20500120b81d03405200001307100310040440001c04009030404c10003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 711333435 1250 711332185 711332189
    0xa14090706021b010c0209071202130918050d031533050310050111070312110c0907050d0b120f100e06010602060105090411040614040f2906041d01 65
    0x180700301d103001400c80f4040301c180000b140041c2c450303114001007502804540f140c0108044140045000c10b00c50100e11840184901c0c2200781040502c10300b8084000c01381d4625889100000c0680d11291b0302103000030402e83e000510f07905000410342455078200b100b00686a004901c1c60f034401e4103a051400c24250710303800040d080c41c140490000d01c40d10070b0b941404160341202103183c0c802d80c2803040d540610011203000d190401110007255072039481c1d02524007000700308070004a04512101d100302d010000301140c05c204450810052611010080c0240541c0f0486440e05442e8001d058060b04c2ea03112510b0012003510546e042c501362020703810f40e544110b407007528010707141280001c82c0b5200800ea66050310080d0340a014664680810064805005030095860100d400801f44581d41c640c072400e4000c1134404080c85648110000300070440366890715503840a400c1a84401c008034866460400740305a440c403900f850340440001c00c4d0f940c011034104000f514042c113441d010021a81441c0e40c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 711334685 1250 711333435 711333437
    0x15010b13050d030908190507060e0102100c020d0801080d0e0108221113060302090105060a110114072d0f020313120203210726160b01090b01050d050a14090706 70
    0x240290b080c0702c81c030201a28001e010f0156023000c07005115481c441e620142c02d90320140304a913240c010710603140703044404041d4210702690010031030004c00342c0c03c0518140140026070107840f20f602d891101620365443e8035113460400140380002058040c025180c000720086400c03444880b0b10b50f0f427600364109022041c0251041d50781002d43c20001c00c0900840003500d5010b406401142d10300010310580da00105c281005024601000000d900000d105401600380a1a0f104a1500b032001c805880300038040d0100c0401600a10b008200520031047e03501c0300f200070b01d0300c000100c803d0b40d022401d50040d4594520400345590000501c159008000c8102034022410390309142140c0d1200110546080140c0030501020b110310408907680d820700c0c481c80c070404e07100540103a0007164a881103601c05c60101a50002a50502c81070085441109001d444840300410180302d80c04006040c43c014809502103c50b00c60000a040c49115000380050888919030249941040205c0585601060003610 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 711335935 1250 711334685 711334693
    0x507300c08120406050f09220c120209010f140c01020c0102030108010f0203070c060f1e02030403030608010e03090909070e01030f1b0608040b1806070f080915010b13050d030908 78
    0x200681d0107a02110102c8002c0d03202d07546480309402c15070086d500a50141a4014200c03070145c603501d26011010401aa0f02640c0020a0400d084d4040c00452403081c41a20982c0b041c000c0c40301c941d0300310000e80c440036018280b40518500840074002d01d4842c00080030100c0d400400c400754210015000795050f11032842c002e10580e003012041d04e040f400112088000944400c006101152450384100c04240100701e01240490410955000440403043c903000110760000030030003810703854440d0308041c2000b50700a1007016801809190380c0d019910038540308081c00b5003c41d00880c0c0030000c0c400140080b4225014075030b903d0400c0b4190481c06001a40c005107280025000c0310001d288100c02c0c4c41854270b8020041e103641d180c1206405c030040000c0040740000510070300d510342c00c125043c400c1c41c0390354400b0000529924002c1c003080c0c018000c0e1302140d00c222494800c40001c1c0ca0520b05460f0040340d01078482808144080b84003580c0e511441d00554418403074020300d40e0040703a0b21b054640ba00125 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 711337185 1250 711335935 711335953
    0x1e0602160c080d021c0c0c270c0504171e06161704060e0109060614030d0503010302030a1407030f080d0b030f1c090b0d02070201110303040507300c08 66
    0x25030340303c401065a800058100742c9402c10284800c080011102c1c08074a40140002071980d144071012425801c1260344900e21858034a5a0442d1a034083c5801c03009035083c4500d9903c142e010b4031034011781c05500000c0005000350b4941d4102000034948d0040042d50240303100006160803500c451091354441c0d0860b43e01c191802c941400303441c03205100c041032036500e106d80da1917803940c0d8020f01c000c1600100e507549802040000c0343c0e40b401103c3c0a8440408103000414984040504e01298034180e2018014280010000f5a602059004007503030861a8841c014480b0b400c840d0802480ea00b00402d0b003c1c0105901c1c0500a900c00036008900e12482c040007400010b904040d92443c0200e05075045a104104605e6148210b44100c61030718072500f0080c804580329504a901e981050071110000c0d50302158110540d0f900425240e202040c01d409189141095100c03103882d07016070b005811921020440345034800c1e103c4106042110b07940a1091050007962a151441003800c0c41040c840f40b2074080c074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 711338435 1250 711337185 711337199
    0x320010203070302070302090a0933110f1809010b0a09060e090604090501150923010303141602130f0608071518030f1a0c0906071e0602160c 62
    0x2140d8101d0b4240d0005d0030b810345154200031030444c0080401110030348440003100090207050040640300045c1c0d0751842c07642004000310340d40e64840e082c12002c081c2802c2d080a070140c3c5036030844000e20403003000140e84494680d070701c000b460b04400c1041e03040003240000007904100500541400e0003955a80030382e03950303200401c4400003800008154080d5503d4003107504d03482c0a03801020001d06c0780b0001710b0781c5101d028500480c0011a80002c03602915141d1144051700110510409842c500744d514071a0350464078010a44841c0610300401003c1c000789600c400f110f6404040368131a80282000c50f500099080b4a01800002c0b0002030000c0c10424042100940400ca10041e180300c1c505c40c802415059004494400812040118101003d080031021800343c140307034500d190140480080b01e040b0806513000c80c01d0002c0c0844042c5005116403ca02d03602d02045404c4180c001c6d081d504039410300000c4003941c040704d840c01012107100095001c400704c41e950120302a0360146000c01003042d56662 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 711339685 1250 711338435 711338437
    0x20f030f0118091104151e03151404030c06090602040f031202010b01080703090311070b120703060b0a080c1c051006050909040f050a080c01020d06150807031d03040320010203 77
    0x40003c0800da000c01102c0550308103541b202118208498084200c180d070380075000b60800c2c4688094041004118050040c4040382d01040d894010314001007010b015024002e08920002a2008080102c00c1c81080d040c0b01c02038001030360715038008204665603640d40300803945042d5240302c2210181c1c10584c1010385c02d07006101e19845e4120685031024503913920801200144245d500032400e00c643d102500172a084c04200c0c080140103030008065546801c2d82160030707003100c0101030f8010941004c20501a90034904181d911080041c00c04142c1d82e125078401001c1805413205820729500c0c40c1c81c12a0100302280c10941c09821a0944c0050f4140c480d81c08580078030841c4c10040d04112a1700101f00050b101500c1020003074064000e45070714028540d0742034203135030209294250700d84d00230408200120180c810000288150035008071180320b03030140a00011070003484841419541c4015403619103c3d041d06020200d402c8003940c0d940c41d200d107007010070403c00c040c030740b84000403081e4417406c2540008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 711340935 1250 711339685 711339701
    0xa0c120311010c09060302030a111b0601121203021b0f1605010c0201080105100c1a0603010b06030915060105090406030305040e07030203130b090c0414040203300d020f030f0118 78
    0x144d288004282400f400350003940c030107803403900c0c2070f60303100309064500c407589000e4801d6220545011510445000c9298507204040c0c000e40d8461104140c16000103d01881110324844903007805030301c0384090440e400e280003d4891070505c40c010705090a91480300818140e41100008101c0d20105403900d004655454400c2c5000307010072400d030011300103031410b500c141c1c081c01c0d4541361003100800c80307581d89008401c510000b0300c1658240700c24080a0310b001c0c0601007030018140c80c0c02e4210315005900603540c018081e86502400e04007004107038941d11803c00c54180000103031090000a40c0e9243c002c0c403d070700a00c20306200610100101d100c5502c2402120701811000242820f40345039621340301d080d504013801103006031040a4441e099601c0700c0c041c80c85540d01500c400c030540e01e07150051500f444821a1350601c000c940700020000c0070104034800c00383d504d242c40e66640312002d01d88000000d1152075160004030300044108004e08a1141825058902036224000049611032903101603586031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 711342185 1250 711340935 711340937
    0x10b0901021002031b070212160305010612020d060203060118060c230c090c0409180b06121e100207050708161202040c0e130c1119030c02030a0c120311010c 69
    0x107100e04405d00480720050600d13240001c0041c080140070201d002e18203140103aa001040c2c25046007002401404c0c800d4500074407501405e20015082c036800075170040c0d91440001d003000d502201107440c60744251b00541010954110310f00c40c4035140d0401400c90305142c101203031048030514000e4400344c14140704118072840c04e0000c000011b002001c02091800041c400d0701da0307400038040060490b445000f0b040b00c401c000d54840303000742c04c1400d0030342c1c10340f20084c03010f800b4006404903105030711000a1030007104410300c95001c48d41240c10207940e08000c0c039481c5003204240007041e0201400780204240040382e001c0f40882e410301c00285a507100005091041403134800700e020704079000d420309800282c4094020301d4030366034424291000418075148064a603100942d502c81c1c1841c41368003c4028660001040020310154642c40020540c0300510000203080040500d01c10045443c1080607441e010b038083d0310079840a40f22040d00c480e0405c0d10350150001445500001c1c804e40040c4502d240c182d00f5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 711343435 1250 711342185 711342211
    0x30411090f100f050a0e041403071506060320180405040b060a1217030a0204090f052e05150909010909050709060b16020303090d05010203180f0715020106030b010b090102100203 78
    0x1425190200c031000080040d220403230070b010a030020136420f0000380f0400780b0548040c401c040002c80407004540c0640c00070800e0501d419121100d0a0b0000c03610403030328004d0304045a0b140c90040000f10045d18401070141c00c103080400740f104208128420b6442031000b42c2c0e6481d00b032640e46503668800d00d0010805000307200d0301c5c0c164101c542030306d50055510070043d04000d454569158200001c0300d003602803030001c1c00d1b40c500901030400407110f904040c2c040c844410000b001703111508403034502640c0c412148295648114020350080d0202614000c4e04018441c03080c56958001d1030020f002040800c450b035000d08040401e481d100d9104240545401649150034030108980c1088800ca0b8070805076071610050000c0d182030350310800109d036001e1040b070015849080000d2141c4415001c02d01d8000d030b5400c0301c0e0b44642d56010024054048a40c0140214011004010280e00400498002a00c40c0c49020000720f911803c0100030b045002003a0308aa8a203505210580b0072070105840f000c0403085 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 711344685 1250 711343435 711343439
    0xb030a0c031106030f150a120b1618180b0415060224040b13171210080a0308070903050706050919060206010501050927240d08030411090f100f050a 65
    0x40c0f81e400c8403800303442c06403901015940703640c948a80640c03206011511802ea0100700041803061282c40c2d00c2b04e81c0c460902c41000da00020f401d07a0422500e000e0700c00300b091452500c40301100240c0101c101c040002e042005407103070040c1d002c5418001400390101606c50581c00031006500d8000035502c034100d40089400540725a1707204101c2e0310700901004c040280348001000400ca0f1a1803070b00340741c1c20038a0826a20b00c091041030041440007403841101002d6039404110a03003010481e140c0c119070500d407082056a420106480c000b40c80e410103410351040c0440400c1070754021000b00302c808412034003a00360702240352610070880b45038096600180c001d04010091075008101810048400401291a00c050320b50341407a02160b8a820100c02c28008045c80740324050070b0090000c8240001c3c03a03c8000c01c600021402440c82d036a4010300d600000000a070501000d502645041000101b5480ca41c1c10304520b0030f1807000e000d4621040d9007400400c0000c0c0515000354240442d00003410110f9114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 711345935 1250 711344685 711344701
    0x1008010b1801050910020c1215042307060306051507021f0c0b040b060108090a120804030306080f100b0303090a120203031e0a02070f0e16030b030a0c031106030f 71
    0x300c00c0c0000e1034180842030281c3e28940c0c1d545d1246444030312140d4000d082c000400b40800564145101041c0e5142c1c2061114031110032a021a20303031b000f41c204004070f58019114520120381008103451150700d000340f100210f01c080e456000b510898004488410b4140584e0b440c3d41160711a13104001c1d403020071243c00002240221a00740410b03034140c24044c241c6c0c40740e52140314151008507400c481d81142181001803c0d038211300000d4100b454103004020315210b641c2c50710880d19a08850308144113003040020101840382d0000c42c06008954142d944061240c0100b60790b031880010810800c904006030100c40d07042c0001600d04214008003510352003460800d407508184210726040e6090f010402c001c04001ca0760f4660205440b40d00c1010395581c51043c5402801c1800755003000300d001d0241e000c2045081e00c1304490755000100d13034104000c5800380e550160b0080c034175110243d4050080c850540107016106590600300c074001d403e0410b10783c90358070400071540310803100c682c20400341c4000b01d00d0030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 711347185 1250 711345935 711345967
    0xf0118030c231e3105070206060612061c03030e070501030e101a0d050a14010204030209061c0b01081014092104050a0b0a0e0102012c1e07051008010b 66
    0x2050051301c810040d202036141e60780152082032481410028541e6200c840c03501d28450036600840500c054826402c0560001c8c020313100d4007400b45440c10f0001301007441e540c0d405602000c0042e101c5000c102200d034514025028101044807403045010707000002a80e540240035400082204402038404e1030300306198440201700d5200790b84004d001220040c1444c1d00d910171614402401580101505142032030a080ba842c4040c22403030080c1d005100800060b01c0d66110190441c0003101c2c3c07141c0b60004282d5070780221824440140140c010350303000141d80c000205120641e079007100000c1c000c0e203259120f866201e09064452a803681e00103020f40c55502c900c43d035644a6403582c250001c1c60159104000307581460140c00001442c071700020114030b92904200b600003d60b00c280020b00150840301c00018040c869004105000d0f007003c0040280480103000a002003500b10590403a500c46140e03007665109414001e09014440d4008036034040d42c041c0c41c0c1c1a040700c10030b000c02ca242c02d058121682c02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 711348435 1250 711347185 711347239
    0x12030b0315011e1e050306012909030f101a0411180a0312080114030c0a091e05090307120809030d020d0605031015091103060f0118030c23 61
    0x44101031000201d0070b60f000750341d1103044c445070b18030344407595003040200740c10520103922404500d810058011409054401d03588000700140710700940f10701401e0301190a0241c20007070315940d80610b0180ba50b40420a6011108101310550000b00d40341904c01070004035801c0000c842d20041013407101c80040c50b0400034282013114042c241d900c1065517507456a51440d0003e05401c00b061450303005000c81c2089001c401c2240c1c600710002c014407119100450244103541c0a0a80c0d925100d203159902d151042c01004102c01a04908118601e40351501580f81e03002118200e070344484448240d6134007445418000d01030901c0d140654500000d00c90018000d6002d200c240d0380c495103e01d8006602e43c0d05028510300000e070000f01044101c85108000340701c035030719085085100c0c9000e41d44883c0410300803d40b6440141501d07550390480c000720050301c0340b40241c4404446103107a58000300400c04503900101c121503051560011540e04403201c000d01c0502e0484068200312000e40080c440050301300001c01c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 711349685 1250 711348435 711348479
    0x340c150e03030309030408120f071b05100201060513020405030d0507170a08071416110301060b0307050a02150c0910110f0a110603070903170f030412030b031501 71
    0xc0028a000040790441d04100d504040301d0300041b8040004440900c080031b02c1d4501180701c0c9141400c209001c0407540280325000e040502d060911603100a4400420030240c44000c048201d8000c0029009000e4045d502034280600085200c20291085030300940b4251803009019044192801608988a0704901026580f1031070b0300e51280b40f98500d480c01062500e031541d0710500309142c5417070013820344860220074114201c02049a050070603003a003100c40640f64020044240c00c421003000030301400864002c2080480004180a50190403900500704202c5e82e8003950360551810340e0002e06c0d02c404484400147c003040010300714504c0c0000b0107160b0b40c040707401c007a4950101004560300c1c0207141c1442600c030303500000741182803201d00d48036600c181e041207418501c1d501d090b040003441c040ac140300080c01007030302c0c020040488a41d8001d0360380e544044684140c8901d02030410740c00b02202d0040c2140800e00c5c02142c098a8200480d654698458040607005a40d192050034004d01500d101401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 711350935 1250 711349685 711349697
    0x15040e010e3405060c1c0e010807080906241c14070f03120309140606120303011514121014030604051203180f1b1e0f060906340c15 58
    0x2c0c2801c1c00c8106c1180d04900690b200f40790004488000741141002600c220288000e1101b0056440310014032107074001c224002c1c0010358842803090488141c42400141c5d8000c20340408200010f49040d164240c0c14090320440c1143ca03440c02860340c03034a10a020382842c00d00da00c003081c008252400803c00d0705e000c01d40740014141c09191282c0c641c03802c050004058540040081c043d030b5103070039601c0e04403411120002c0c601d503525000c0031100311000081a8000e0212070030903060706070754a00a5609013940c4080303900311446c0c007080355682e540d024020800d40b5103040880c43c08070304001410070701c2140c1c442e0041081c10103508201c0181d0308001d0401c455400030034000310140f401440300030401010302c0010300e1100f6916000300000d0340c0740e1510238050466446070301c400c80340b029564070382c28000b60340c1006200340c004042140c9125108585800281c0080d462100b481500004408105242c3c140103c0036142413400303030001190030015000700c42c00c0100f80a240c10342c04401d4010f1285003000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 711352185 1250 711350935 711350953
    0xc170705010f0b01081006080f070c1e1a01060e010e241c0924020f0309150a060f0512070918050f120315040e010e3405060c 55
    0x400e082d240c1d481e07601c801c0c42c1e4580380d03095015604103034500e820403100d44000c801d260518800501301c480c0200501d2400c42d402000c40c1c4400e01418101c150b403900000c80c0918000388000c2e080280c410781e102203c2600c9012840e500e41e00e1951a414181c408542e40e03e18031000a800442e2890780c0228001c0d4007900d102c01003002200d280c05104805c40342c85804988803400548401c000450100c00078507001d00344101880001c03044000884001000715200c8440600c0c1c0400314024007640f01c0d803031811200002803011803140050b64210220941e10b21074110f039982c19a01043c0e4045108000b4000310220041c400303840c000050000e00d104030000c0740c0c84a60b80f860458259000c001c2802d1122400043d88814000148000304102d01720a000b8a100e00c02c2024040c90f512004010400800600300c0c805150340e5140c005c0c0c21041a07000c000e02c00c15410880e440c0e00c03841c049841d07403030100501201001800000740c4030301400184c5810710400700d00d46002d001503503000456114080c0505211 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 711353435 1250 711352185 711352193
    0x5130e10090312020c030406260708090f070509070f1103130305070e0714070f050f06010f06030e070e0705130f030605060103092102071d1501050a0c1707 68
    0x514850a00d2402001c9070900302820701405125004803040b2060740108003009814000004540c212003003031800402d2007100400b030032aa40107066a180000c1e1204050002d01a407054600d4054210318064072101880d8801035980d580481c855680c004010308002200301e40210000c44aa1425090403039081da411340c2000d08680c40a81d141241034440f020034001c2c040f0400080001d00004c40c581503013400c0014000e030034150034144c04900e5160010701c48040100000340d120085500c1001c0b511001c000700c900c203444007002d000313012100c4071141e0000303809403007409609030f50200d42024101481c14955800541c00c0001e0040c0140401080f02000c0346d0b14040108005010084c00b10f0040380c11441d25038143c03040540005d0405040112103404143d0301000008003080c070207030385400140e100109034100021a4400c1e0509403450480718a141d00c403601c02841100c004d8204051058800010356090041c44103200000341c0c0690a400000d02c120140e804000444034482d06000c80c0d591 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 711354685 1250 711353435 711353443
    0x706020309011b0504290c010219030c02010c0806060c070e07030b010e010302120604090204060b0c0c030d021c12110f092b02012007080a1103011505130e 68
    0x2850790810ba64030194102c0250321526094410320a501c0c0c445e113032074680b00c0ca003008620b000140300300710701c4040102640c444000084070801d00100000350b499601e0400c0756803280d1108030503800401d00f00501c0d500124410320407420f910b940b81c0ca40d07007620f444481c280700b4150054051052141b1a0300004118180840c404509c1408690740201d40c030b080c524001040c081e030101c20030b4140350040c0108286030b0b6184010541c810340c26680003c00061071300000780030f4038059010b891003150000301404100004203500a19a0043c2c0c07c0301d22000c080d0204980e80c540016105016510342681d0402040c414281030700055491080490012500b10380ca00107030307001040d00301c810400003602502c603003402502410381204501e90b0000344207224000c07604100c0c0c441c50081c100b02c2190900490540281c5111026802c484110f484071515403081d40d40d140e02d4404240d800c2d040c00003c00c451883c05000c3d02004d0300840f2a106d48040c5040c0c03d11441b1580403080000d0541c4545030441c800130108 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 711355935 1250 711354685 711354691
    0x504140a08040306060b0901120902011809021b0307030c020108070c3810090b130f0c200d0c0f14031305030c0a0b1b070801060617040c0501120207060203 68
    0x182030755580b5071551801d4001c6552a90001004001c00d026036205a03801100003940440ca00c030021489010500c012a4000c80407289103074100360030032010801b50341c20b034050054410320356003400c1d640c4107a021140c2d4a008441c8000c00003040c80d900b0600551154001d02d03080348180c149410a00345076903450840c180c022000700030004a5100204240b8018410380c2c000e04003218050b25142011508011403e085000380b0381f0050300c504141125451380d031520711008004850412469a5a010440150010700d00c4200080c2021500d04120480060300101018101000340a4444000c1c400d884d0b01c0e801c0352099503000207030341d100c2e800308210005004110726201c01030350340c2d601d144801030480d03019600403034001d5000022441c0350381c80f030840450035910340d202c0180e110303900110071078102c07803a07180303c44a280200303007000440325015007111054844a03180d203083e1b0009050030f4818440300316170242506182d62010001940590a0040d0011841c00c0152901881c1e07240c84003a80d0045d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 711357185 1250 711355935 711355943
    0x70501060306050a0b01180b0a111f0c0f0c06051015020a06050714031b1e0d051e040f03140711030c0102011401061b0b01030807150209130504140a 65
    0x80c10411040c2113071481640e540240900708049034400e0350049000040080c0500003070310000140d2561a54002d00301c9403120185181200d0071031442100e066121008e01000c90260b60400140f424424004d962940507210726a4981110b03403920348581001c0c08000d001600413040700040845c00c6608580c002451001c560005c0c07041c0c42c03461a0802c04c854000f0480340c1000754a02016400c1010070040300c0d0004003102c100b054030f401c5202c800d021440740460119001c0303440704500e40e820144034058603038620369000420a5581e800c0c0a9142c03881c0480c4000b6007111404000750020702010506003c45000c0d2030b194075079204d01e03403100355179034444c1c2070a035400c0c604030350a08601d250410900d4480e070404e01c028851200c0030b1810500f44241030007804144a41d02c041d9000050120f0000f00e07e1070b40001d124a4156502d04044d511170703100c8001035410b03240c0306070f06200c0c41c40280210f075490303840580311841100c140806c00004200140c411036259071000c0301d6846445040200065072405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 711358435 1250 711357185 711357191
    0xb1003200706051006080c0714070509010303080a050f01031101030c0306091d060a0e06040210121109010206060103090c12031b060501080f0c300115060e0607150e03070501060306 79
    0x1c4c1290310551041343d0001040160740030030002259912026500300c6035001840004108140d140d25080c1640d0703030810b5421000300000081810340c844403840c021342101e00108503d898aa0458180c19424080038180700310f90316a2034204d5110340d01c894000d901c1803070009082c5444e07050305d5040c1c0c2c0c0107068214404000a042c100701c0c0d40d041c0011900104140010046403110150094403800b000300041e214104604240d80c4c100c0c02021035010035030444500b040303c01440014408076400c2003052a005118603000681c80e94042d2240d119056001426012951700c0e01e044100c2507071035101c04038108800700000140b0442e1140c0180750091013000c01041c598140303000303503140040100d5086c605910191001e121900d0302c0700142141c5000d0039540e40c84100302c1c501100701c001c0e218204c900b0343d860180c0d06003405c03080d080b2403819103c40e40d581d005040e0080b010045140513200e03000e07000880000791035240ca0400e1340041e0b5008480d00c1070b0390070715480351104c03400c40d00c0350f50007a2845a1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 711359685 1250 711358435 711358441
    0x60f0302120420030a0c09110412060c080f04050a1103031b01060303081b0a08060f030a0515010602010c0509191802071106030106020d08090309040c05120106030b100320070605 78
    0xc041c900c030b000160380c113400070701400c1c0a0351581d5140618512800c00540d982d42c004840c814004400c4802610000c014885503850300d1814500405c000003241d00020407d03400315003180114144140181c3e040030080a071080c80ba01c40f1a56003a4649a46a1507c0108444081c4041003540308000d01e04d07003000010030515506025115420003043d0038070002d010741e4010760001d990700030b8804401e030915003000969120300101c0c1c2d800c441ca285807903041c03180c4a08002005000216816240d80d684006e18281c0d0382e038070099080c1c481d4400000c020900c24003804000d8241501c1d83c0e0f06054050041402095071401601c10744103100740d000101070b0b00015410180f2980c19a4009101c4042c0c500d2442e540c0b40000003501e480c108c841071000c00640d080443e4000740100151904d42070014000c01c018442c2d81000307000da600804030b602540d100781c000000c60034000e2040800d410710103021591011103902c0120002c00885aa40b1009c00c00e44240d4000c4d445c0e000302070a0300c18411000010b080c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 711360935 1250 711359685 711359723
    0x30103060c02030301060c0b0603010914010903140a0504120804170d030e070e010312091505120a0216021003090c2c0c0a0e030f03070534060f03021204 67
    0x10040c1c4010820741d8000c00040040603800035282c0c4803250052000034660310389c4800240507004211000d0451540b05075824017003001075028940282c4642c44500310b602281010030701d01d00071542183c01080b420700c01041a1103c407501468800d00c00c6545a182030340380c414011404100c0c07041c0d1903184d84454044a44a6014425480c0f40c001c400e0041403100c1c40c00b130200200d0b0380305001c0200144595103512121704e002e0070000c0090880104414540b440400c001480340c3c2105000304200e03005d0402061030070101f8821035030300316000345d0a00d9000060340c080c0f01282001400c15010566178000034000718000100d4000603200d4048041e46050f10703440c00e0950741e0698030b2030f00801e200b40f50a1000d14030303085c01140c2c120000d0741095148524100e0001e82080907190b07020b80580070000b03842c030401078041004544c12001072030400c03000071203039401b1503110202c10141e80740280c80c0300144585070150b509445001041d00d0090307d4100010312243c42c021095408407003656022030860206 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 711362185 1250 711360935 711360941
    0x203060108030408211902031c0b03030304030804031202121501171902090d1b0e1005010806120f0604021002011a270718061707080a0e07060503010306 67
    0x1408940300540c2458100f254a54540d4840a5212000b03e17040500c400050b00400940340c0c0ca0084c05c1500c401c1401010019449030302a02c1003007030364820305115001110b070030700c99800c0c1008094015401c3d503a46560940b02030f1000f40041c0c00f848101d0a50000d903482900040c4044100e1018007402e80c03d04200140400c00c1c950100b50501003590340304800301007501d04055015040348440d124003000000d4040080c8599005c00350045120100e41c0c061243c01c00907580c0303107801d5995411000d507a400214141132401e4580142414958804022039032003444820341012000b0b00c2c40c0303820001c004e1105c0c604800a10410030580108041000b0f5260500c00c02025080d140001d12890000c8100f50000703e030188441761188030203040b03001159089481c0002401c03c13070025101a8182198042d0910340402c1c14946580801040409c00a1041c00f2400001c41030001e814071039124040151901180248070a081d941c1d182c1a41040844c00c118120050260b61a2a42c0d03d5045050110903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 711363435 1250 711362185 711362189
    0x3015030d030506090f04080c0111040806100602250f03030e0405090313050d0f060c1d04090c030b0a0e190309090501080303040f05030d0516030b011d04090507051503010302030601 79
    0x501d0315040030000940c0b61a0780099001c40045990304d130590311803070311445500071001c2003001c941c60202030040d5007424000078801c1c0c4141c84210f03038241c0d86003414031501400d9400f4001c01600010002c100043c0c03a00e04250343d42400f1099250100d440e03914480c80d07203045900039000100541404941400c091144940050103103010394942190702501120131038291250500408200d0820307018060131317101d2040d5041d4862020300c4805901d20f002069070107520700001c004410524620102cac80e00d4800d41401a41c070001200d60f107407454507070341106c8600400a601454031964030000a10081c8020809103282c10b0580c24106040d040c000c144000c1c58120300d003814a810010320000a0010503a60b00985c1301c01000e4507800d141c90018218016015621425800c0c101400316803100240e009030505420340c6c040050b0300802d0b0045070044c040101414400c50342a850210900300340d006028800e0140080380c00155881000c65000706403401d010360304c0d00c0040014000c5140030b10003580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 711364685 1250 711363435 711363437
    0x71e05040617010302030c100309050304060f09080d1e050d0608031309050f1609030606120b0a021201170309030303131e0b400308090f033015030d 65
    0x1d020f40c150380c0400d0b50381140941d102d00c54501c40403040c001034400c0c0c02480340c4a5210302039a031210b5031880302404200d000c2c0c15500201d080900007044255001442001011051f5500c2e00c48030811800c0d2425503665240c071034100141081040c44098081c005d840041081800440d656101c501203810030001c0c6070000c0c070746a03040c00b00303010110f02c0d0070126a800c449000940b1051440c1d900d81660824195817005004078100300e00086e82681c1964074524039401001d98015076a81c0c420003134128442c00c9141c5012914000043c041201c0901c07101c0f00703035000c44048030728204403400041c1c23442c1c1003190045d002884158050080080c0c1061102c90000c4004502062403903507501c03115024001010101e458140f818007842c02c18440310504071142d258500519140001c11140341040b2004100341c1c04034030440c0120314245030000f202840c1c0e00800c0051800c1211601d01f80010340841c030002041040c0186820340581d440c04011401040c1604812410b40064001c0c14140901180200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 711365935 1250 711364685 711364727
    0x21b0907121e0f0e0a08031519050916211d06061305090d030b0d06060303030b030c010e0a06030515030d020d0305090a1e0609061107030e030303070c0803071e050406 73
    0x4991310390002255103200b60301c102c1c8940c40b551218400380700300c00240c1140e940564981d8008581401820750300c1301b601c100780c401002d1981e54440c2c0031f50316007101c90550001500300030796501000600040310303c1010b0300c880100d4909a80285181c41c079111100b06081600f208044c41a5440e2103000c036092800340344004e004920309a1034980d120700030f4030004070900d5250400c04056a49511100707032642d6120501300203144d207a08000f8010602e141c042c900070300c5a0b40814400d50b00501112101110040000386124103040b0210060800500700348a9140245426121a64203000148502e54541d000300030741e00882000030f050701d0018000745515001a15440080340143e00e5500154409801e01c2c82190658a4007074001c1044100140c0034502c0c00102c0c542e280303100340041401c01e029995038050141003404043e1244803c0d580f40d00440c0340f0b4401e01b0001003600014680c86005402e108180300c5820b819103102170301c01481200083c1c40018148641ca82201300312487c444606500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 711367185 1250 711365935 711365951
    0x402011d210f210f040806010e0a0f05040818030102040f06210204080705010c1a041103011a130902030a08030403030917030402010e1c15150501021b0907121e0f 71
    0x200342e400f000c089125400c1c100000708200c15000c11021107000317184500442d8050769461902d00d4200200b075541c0d902c1641031103807445498106014143c0a141c0040b401d615040248401040051802c42c003203415540030b020001742e500c0082c0c0b4040c000c01d201c2d12089c1161984030794a101c1d026181203204051441030009100c54000021500140c1d0401c1c00c107040f41e8090f60400e40c03801c1fa19032040b101c01082140c100420030003000300e0710b13046c0f1400f50024003944843d030040314040e0550b001c4050f0000440900d8940d01603054124101c0140045c0680741482c1403074031416444d9004440640100761200c0800080100007841c484c404107080382d0413802c600b01540002c02082d5802401803107a4508000c01c0e452080c1d1505955081e54458030316582c03116426007203405000c0b62000e00a011055400c00241940041401c4140b00141c100c80c10f140c441003070400c21030a0001e0041e00400c24894810205540300b131007902c485016480c803103021602c1c901022001d5035400d05400803901c4c1003a402c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 711368435 1250 711367185 711367213
    0xf1507050c0114120411041d0706020c0105040302030c04150e0f0403020c0901051008040c050604091409010c0c06022b0e07061b030806131e0c080402090402011d210f 73
    0x7605401c154040d003424a0f04d0400f40c0010040d121011100c0106510342380c440750725190008403082200e00d19001c0e55007400003840195401e02644c0710180d00358001c0c0c1100b00052402d41c0c01024010782000f0060112500d41c82035150404080f80c4000582c4c110906000c20315804016090402d03001701c421510b10340c106408500e0440448420b04140402c5101180401c2540003081e800381501410780c58070b4542e107000e014060042200a0450310340c10070301040c151a030601074044012a07984452058000a1741c0381c40c020340c044910303120f0080e00c107003800b481c540e0b145014001c41202c010001c80c814609414440c2849001e17404501401030324071900b600201a1941c4d070382a542c060810600b40d5960a021642006da120440070060313142980c0d58411000900301038404c0c0e00001000c01c070240c1c0a03030080e1350700f890540700654442d24000c0000c00540c070a41000302e108000248840c00d5403481030205100303d100c003221015518042c00408141842040343e00c40340100d0307000426203071031603a41d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 711369685 1250 711368435 711368467
    0x6070305161e23091306060e010516150f0c231b030d05070906091215150b040510030513020405071707020c010912050c0f1507050c0114 60
    0x650000c01401140e2615840da005690f1090107245010841440800b00d643c2e05103c1d50007100030a115910403070800b00702080714418401030380d14a8403110b01d0200c40a0040d5050f412200c0e040c0c0580c0c1210060ba4001900b180c42c0030142d214219010907007000b2901a401621100358030001002082802d580b043ea2520f124110403900c1c0d208150390300c1024804a03e1031612514071041a844000740e041450b010310380c4480d100704943d0341c3d01e030809500c4950480e4940c00507c9004d03d00941002450085003072807880d0b100040b09460006002c402e00c82d41080000d0b100d40c0b04002d01580403030100445e040404a803d400c10107403800f0401c034a014243d58080007402003001c3e0040740d07654001000ca48c00f890008066080d124881c80c0e0a26000302c000355a40440c2c0030b242e0000380c10310800540e10000752000301d42030f40d0140181c070500c45100d0502200041aa02269015404084007803030415000018801d035405540603010307180d502d00014028120700c0d442071101110804c50411a529504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 711370935 1250 711369685 711369707
    0xc1803060506040e0105041103070e070906080c04081f0f11030a050606070b040609030906050304021f0338220f0207060e0d02060108070b1206210607030516 69
    0x100c0002000c0d22501d02090003407101c00356555040d8600024082804510358005c5010341d811000c840e403190f21129403c942e15130a80ba641c1c00314880304001d0200314003400e003040d40401c0403c02c0704d00302595020344524140c1c4840744020f0014150714075000d1107a4900800c1d42500307031758806100801e02540c0303004141c4002031164490076998004a08140d981a040340d080d1500700c000c070700756030420b0b0400c0030040480f1030301100072541c80c00300094070710300072801c0d684100d8008100400c0c4186a40c90000c040310080260420190760703482414900c00d1105000c030102070600346116644205402060300c01682c07c000c40d01c203d0080500009038089140c0100400c00701c0c09001c17600c001090f081c0740c040d0180c1d0b100100340c14104401c05040078070001d4110314502544d804c8540c282da0340d005103601c40d0818061010a030a08001d854802c13074010b80034540062015010ac2e00010902203d05001e403c102c0f9a2503c03500010140a509507240c0250b64000000900019102d481b0354400780c00105e0302 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 711372185 1250 711370935 711370943
    0x30703080d0603020303031e0603071a070311030c0a0515150d0c05090c0d0c0305043305040501021b01020c1903030b2e17150a180f0c1803 61
    0x1d04400c0d80a00c1e50802001903902800b12a202d04007070440151011810107014492a03402c03002843c0c1d0b140018002040f103020f600c2c1c040041100001440301540804807c1d024002103607414001c40e0420001009d03907000c01030140c405a4110b150080c2400d0000103807442280b4120144440041901c4141641e10300c01c50304100d642d0b00a140030444840f066024541c002031443c200048100d00c41c0c01442d12481000c4100042d00c014901642250750039a03024060900c41020784124000012001444110040c0180c800c80f40664419081c0c0d00102c50484441c0d401044a2070017a09003c40403059214160003542040e1250065550f2180c500780000309141c4030701c82003401c1c14002c0c1d10024400c44007070704519480c126002c000f908141e0300b42c2c15044418052072074180041c400e0400d0309282e01d045e88000000e071182c11140302c503c444080125404558a10000707140201c90442408980740100302003044030315070039060111808405d075038052110b214403000302060b245940e00d00352948 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 711373435 1250 711372185 711372187
    0x10b04060f150207090e1f02280c17040303030c090605180f100815011d090603010e031810170a050c040b0406080a05010f03020a151e17010603020903070308 69
    0x440b500491418005078400c2500e140740116074811510040341030482200e05510320340b1005c29242a0108a02c54298800e241d02c0400070385c001ca4a508000030703143c6100a1900112540345610384042401c0c0141c0d040c0440c0600003402c10816815001d00d4101c00c9050400310109454120081c0151080c070401e00700102c00c0360940002c5644184c06034140040244c144030b41c0503c83d803405010f0103006d80310318400f450740350601c090961142c401e0040c100112910000112141c50501c4405407000d49140d616548410006140b00070410250040401e640b1081103a18806824030100d4442c2a130f944080005012450b420400c00d515a0b0340c1200029400041030341d50340314003a4043c001c079009589041c40c005000a0310640c0208054020200023030301700020390b43c806040c0341088075884000d4000d0101001000000c8400406584081d01c3c3e00301204050304048012040340c081074810300100c1c00030b4003d00d0b0000001f56031903000d4171840c1001c526208503c00080da4400f0300f03110061440358 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 711374685 1250 711373435 711373469
    0x905040b0604111c1e0e0105061504030201030908090d0f0c0504110a1d0307060f0815090705031803031017210c011e0204060f0804030804020108090115080c03010b04060f 75
    0x1145500201d41d000c2d0005807608031070380030742d5101702402c422209a0300c10b40c20440840d90b035280c82c2104800c03008100c0007071854649940d0054014080215044c0c54000c8103108000040e1a5803080d914483e00c41d0342203801c091440e00c0c00c0241c02002e42c103d00d000d1351400341491485403105040300e18100007400e00020840d01c0e05d010b480000710419020381c05008011000450341d4100440e65100c000c1a100c002e0b80c0d076118400d5512010a15a04591040058000c200618082d500942d00548140070701415a9001100c0d945150300a4403510750f0103038902c404005811500c0e03003903c07a5485080141428180001d00d0741c01002c4d078000005c640040c0090a00030f40d1009502c000c1011185580000c08050000b90740c000a4025100311408516651749890070584500c0d1018402d0740c1c16104d0824544a60f0011031340003200415040140d9a10b420200000380e003507402c0303802021048010611400444241401d40f01d9407554107001e41c0c04d01c2d07403e0000f495007001c1d5006441d201d15000c0c0c1011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 711375935 1250 711374685 711374737
    0xc02150c031b0102041d0f010b0a02190b1506090d020603070e030714030d14030c1606090b042108060910050d080306091b1b010f02040905040b060411 66
    0x8840e8032103410344010001d216102c4080190054000c9889844182040810b1b141c1c0b059144c1c9011115090006d49460051000c80840005070130342040c6841200c5400140d00034103070f910103403032105540600314039040000075806072100129000055070014200f10418002c02d01d616440743e8028822480400019542480b520b17000002d807200608465509a1b908500c890142284010500030700844021004050052039486005240ca0382228595600c0480e44403998005130b1840b5034100341f480103032000c21007600410190500881c112841d80c01d0a00d42020400305081d036402440440041005607130307421102c01984800d003a60007404580e075250f006001d0101d2234210316400440620000240042800514815802030b1140c0403540c2301c0d0b03009004801c0b207900e981c07a107400040101d0244184068040000c5001e408000704120f001c40c41400c09036049500500e442c65030b504204001c0c0311942c403800390446002c0d40c1c02c101c0401c06017403410b0303544101c26140c0310b9441c80d040241040f07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 711377185 1250 711375935 711375937
    0x1202090402070605012d03030807050702150d0c090807030b060a0e09070e061c110a17030a1d0102030306060313120503090c0916030905070504060308070507060c02150c03 75
    0x12005004540e541c126280c041c00801082c05100103883c030030052424a11858440480e0100e5591085080d60b403840ea000c4845040050961080101c240035407401a156000c0c141030f1420040320640d03c3d00000c0b4400c0080710550245801000344003071040040d803101107030140540750000350032040d03a501d00020480031800e5078814046140503000301318074142c021a200381038400246081055445810130400460502601c5100c4500b8001c840e4002130100003d610102902a0416a4940d03407045c0c0c0a40e4407442a01c590b81e0741c0c000254140010307500101160b48280414134507280c041c98100002d5481c040142814012580000418940c601c3c42001000c540e5020802020880d02180c006109030010b850f40d071800d100344001c015480ca4035880f618801c200d04c5902103e000d10100080b00907201301c003000e40b41405240404201c40c2c03514003036800914080cac22010703994261807038101d261103d00d80c031080820080341c8407500140e403001c2900080b45101000c81c0d469503070001c40e140c11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 711378435 1250 711377185 711377197
    0x90a02011e1107060207060f0509060a110a050a0c1404020403050c04020c030403060e0a06141608221a010b03130305090f090a0902040c090308091e060705060a05070509101202 77
    0x2c070b12400400103500c6034001399003400e490140e0b44140711403810510544060166010840e0311030018000c0c00351051240c0750703402070b81580c402202c00d6002075465260401c03203096815100f40745e02100c140041200400d0301c424a14080e40d08500d054035603201e50751a542c18841031482385400240c10080154204192005560082c6040001201003010556104e0400794122030351402c1903480f40c88030405075a01031098454180304850407040f164112002e0200501d070442101e11000e0b5050201d0340544080e482c107104036103027190717080055001400c0c400c05038400d6403003400400070042d2041140011607116a85801e00030380303c1142e01c0004032081c0840442c2078001040c3c800f00040340000b034000c1a0f007540280c40c1080100302c107003001c445980761400050721440d410400c4440e51700308240c40801c000c8098211704402c1c0300ca4000501035600c01101515203500410a0041404652040b0f6030001c800b410403d1034031400070f0220724000040c040c0c2d81c050000982e54544e10300784540407140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 711379685 1250 711378435 711378467
    0xa03270803043003050703140d0207080408010e0604050d05030703091505060109060f0e061b0106030305030403351905160e030a0803060d1a10030308090a02011e 71
    0xc0c8070b40e1202819426148091102030f402c15924a01c041c03180481c0002d082120b4060356100c1c0303804590344090720040d00b403441c64040280200280300d46858944003a10955101d04807003aaa07924024505082d14071954040315a038008500748400240b000408c641c078000f00e410440c0c0c507503a88003001e4000b014030141c0600b103408004281118a4240c0c5d000c28414402600c800c1d004a0300c1e488101d410030a0b112200011844040100c3c4091501e071020701074200458111490f4803084c81c50031400d5580740e60080380401c2002c81070108040d0050b801409001420300070032109001090921429009002103201441076903010a5807113241200c014580c61014a092200e81410410003903414002c44010300040c4030f03100c200040c3c0c40e002c90f07442c1e0040c0d0050501c500710740b074070804c010000e000b04800301c2d076045000080c0c546107942c685849100700c03078000e410700d0035603e1340c00d02030503028006040c1d5505401060200300140e8100030001c03814204210414800c00c4d4445091303a481c101c041c0a04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 711380935 1250 711379685 711379687
    0x1d0a02090c0f18190f050103020c0c100f140f0403020d03030f1407090614190c05010906061d070c060f06030b010902130807080d03020310030807050a11030a03270803 73
    0x2010780800c0200480c4102c5059913001000004130a00040c182094000c00113420070201c002c00540d880383d006001040540030940784403c8600d00011852010610610080380d01c3d01c2e801140c041e00103c0704100f15440e9601c09141c540f41c0701c0f1a1382c07507220303c0c00021b100710314034861002410f22940c041f03804460122020841594440d14140c4621400c440076030000d601144085140340c0304503980081c406210380340c42d0420b141c030f051701c08446101042c000c0412466440d0040420b1090203244c154500a04c0c0000b140d5041190350142c5003040f68064111220f078a0a100426600c501d00c4000c00b50460707070002da50b6103504440310241c100755201401c0140302070f0000c26010040d43c010181215104919990681d844000741c0c1c894000d803080a106030071064014035200d0182d0002d541c46024156508685512941c2c0c4044e6600107403025146940102500d80030409650001c1c06422400c4000317200c080e4081c1e600030f11280c0032040d840188140306100740142c09240350f0041c0039100c010192 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 711382185 1250 711380935 711380947
    0x3070605040219051c080717210702031b1903020c03070905090303131e03020a0b010f0b0f090d080a02150f0c04060e030705221d0a02090c0f 62
    0x805003800369010b900c564044005000c001094065003012070300d02612200512006481d50400c0380a6220150741440742008000005148282114124511040e41c00d80340c461240c80c00209a0203204d079404440c0d001d03010300809940000544402c0c01188001c04827514a401001c0d0400d020649602d54468002500340704246e004103003e403100800340c040f20240e69031a1000025908207a5445074181c02c1080451002c0030354240c0b0740c1540340500c1c4401d40310644851298a4024040b000744d0058200346072050420603141171490042100760a082c2e03c032400c040840100d0700c20702e1000b440e541c03000242d4a4503070710b903164105101d58010b401982c40e41c2450b1000781d01c0e0700042d5150351240d9003146c00101640482030141d40107120b410300327543c1440e0820005403200000d4260745a80743c407404130001034030f603034a1b1103089845040820025003907429400101c140c4560010100d240001c000a500a4240004002081c3e6030105e800c41e24035162202920210f226407074000c2445d0100040e2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 711383435 1250 711382185 711382193
    0x15010e0601091e17151906030c0f081b090a0b0a0509070e180403080613090203070902220506220306020c16061d12030f041d06100c02130209030307 65
    0x10f1a00719109020300071500d07a01e0032007032a11a043c0e289001d224001d100040360304001c140e110000800081000011800d85980740e84150116030350108127800301014090250110610440381c106007500c800c010110818400240c00c0c200081040c4402c65954000e840c440d65070300c14020050070090001642d6041082e801465025091012805000050410400c4001a4000034401c2da00356507500e480362615010009402d001543c141d40780c0da00c840c00b01000d0398040c4140802410709140060341c8001c0070104052140b03d003a41014210b4411800f00301c1350b2240401c4403560382c42031945a081d00b2460010300c081c0c220681016200c6032012400c144482400200031260030348550b1a0280f490b41c0380c4040300c104032916103614011040c0290380c9001e05010007603003404c860303007400d40c2d081c46680b28000f00650000d5120102451140c3c80303070108600405d010580000050324565425031107a407000d807103190610002401003246240720710045003030713605482088a0040030f89903030f140c060034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 711384685 1250 711383435 711383489
    0xc1b02191d060102070f081f020423030714010c170f0705010f05220f05190803041211120c070f08030a140c122208071715010e060109 59
    0x1a840c3c09413051000218082c0400c00403c1d04540da80c0c0010a00c800c46901d8010b441c5a002c03142c6490f50f902840003040240c403182665174407102c00d90529001c503070440105864032210358080581c1c40140c0d44c1c1a082c59034040140f040701504001042100c40180c000d4002511480000d40600130000c12138004100c0190480040c50090302e1042c000ca03100c2c8280769400c00240f5419030241000310040034002401d007042c5100c0d1500801c2a03e50030b51014081006000b601101280c0d400c40020820003000504000e180e801841d51815007d0b000010b08001c1c0da0324407100309508404000700f2069010041040040f01810b03c0e603504088081d0340c0c5045540d290000f00001001c50700300c41441401324606002e65040d00030010041070881d00039001224140d0009031340d60541c0d400d49505014008416540314000e0200c00e0040109514140c40c810601298181c0409030380c1010300c8102c89030f041c2440d05415140456101d410503115800141c4440040d6401118114115104e0902e0300d0550a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 711385935 1250 711384685 711384691
    0x60a031104051c05010c020712030e011403100f08010903210605150417010510051201060b03090a0215070b0103060c0509091f060203131e0f03050a03030c1b02191d 72
    0x1300007803001082140f004c1e0307140d910500450302125150040304001c28800e00d1150311401c810b0400c5651001000a00c19040d881100d03c0c400c080308200b01001a0752040652000406803e0000c0003a00c009641c0180189002d09190569440826605511042542c090030051000034980383c0c2d40c000925151400c0e070468400c055000018207054202d118041c010359104030444031803a0001230a000c2000f00e03010300302c002001d26660300d140c0480c0301c1d0f1182005500800c03020006202410a84c41000a0300c0200714200396140c0b014400400002c1c003001e40725054947c041c2010400009000c000c0b41c281c09445401940b051005041c0300b0103100524a41c07044441210b2803255480c2c031228141d80c0c030f100c4c8400e14100d4594500c400c1019a203200d0b1705802045010305004280c3d075581c0d4046036411010381041d01c103078000d408102c04042d0544038041560700981405807007515541040d819008040340044c5c010010781c2800700e8000303590322440b00640400c40000c030b401c41c4c003401107a0480c1411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 711387185 1250 711385935 711385943
    0xc1a0f0a050a090b010b0309030408100207050c030d05030c07080c010c0306050907211505030a0c050a1a030403120e07030609140102250f0803090c01030b0f060a031104051c 76
    0x11074085603103011280645a071241d08960380401c180d18010303a0000700d900080c000119800b0601c40844ea82c6001e002a02c14221582000768030360226040890408250240031482940503840e6052070341e411000f6650711083c0e40d02c031141c5510b01400c2141940c4250516201c81f9440d00c0004c1214503007550040d81550019100c02e00665034440c1c040c2c90700401c1c032503e44a0883c1c04c001ca161003034000c0d0024201581b086483c06102c0b0340d02d41c08030385019203206003110b0407500710509010f5814a41030440091624071014805611a07000e248054403026101801f042100100c0f0313010ba543d141c1080d1031a4003000200d940666072030a16038010030f9842d0003180c2e100c0003071600e000104014026988010050305501203030003080e6407203060401d0040411544110089042c2021a1803440654030071020400546aa1003901000408a88000312020701c5120030881002d0b1907200c0005660000225003400140c00080051107401d500a82d8000341d40801c040540c003101c400b00046941d4000e03c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 711388435 1250 711387185 711387191
    0x209041103180106060305090c0415050a060f08090c0a0311031f150e0907120515010603050703150b03280e0c03060703020a350a0507020f06090d0c1a0f0a 68
    0xe883c0100c6c143c80d8281c0311120180d210404125071454540d010041407401e25018001c1e455407000880c10f5001d460b03012401148840410000d400d030803c022540c070842030800343c42019a10030020740540c1c5e0902000d030070a0031a19050a003918200031503220414044070303109100e540d0f2014000a02000c80008920010003600025040850310700c940c051703964074002e0110036003007a00d084101c0c02103c0d0151502c1c0b00700c0d4503940103c10701d44005806000c466a000c5402e260041c5c0180a45070907980803403401c6803080c810481d00b5403640c1030700e0304800b0401c0b01010a004007012541805c8480101550a1349007881d402080100045c000c10301d450141c0541c1c0c1656a0b01400f40c08902454031000701180c0d00280758005002010103400c40b074014810100344420b206400704841000c1280d40c003181a94500500203d1601003104e07000b0107191000805c500d18104400741c0e21165518a4007040c031900000842c00c01030b000101c3d039148c036007a0900180c0c5240c03107651021144405e032203045c0c820b85 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 711389685 1250 711388435 711388439
    0x20d0b0103020301030b18030f0703021c0e010c06020c070f1409100e0106050a050705010c080906061504210b09072c0619090c0207091104180209041103180106 70
    0x4042e00940e03048a800a41009007030355402c07070108100001201c0030071540000c0044444456082000d4a4614000da0042028044413003032010038200310310161040c4003110026082c3c5a030300c40b03041208254041009602c8419000e10740d4034141032074001c0d82110303403550340c0814010b21002c1007005426080310300d594244c413412249030350042319014a1511211200042c420140a10300400346020a45400ca00d811102e4607501d00311060100c051000400768002e2003004501000025001241207070b03d210b0b0800000c501c00b0b030503c214850002c1c6503010844c43d1040b10041c034110018540c01c665402058a002403043c3d17214000b03030084102184007039401e410300300d880f507980d140742c0414003042050740d860740402c00000d24480740d29602d9001c0284030110340b10a5500031100d100303900c2c1d00104107150400d0314030007d840400301804100c40050108001c0d88000b0011030110205000005a40c3d00310716010030090400070950400301e020000c00d101180074081d0705010340e040e800340200022a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 711390935 1250 711389685 711389687
    0x12240310050412180e040f0803010b0c0d051305210d05271318051002091e010905060a110330010e01060e04140112030f172e030501020d0b01 62
    0xd140e04080c00700d503407440c113010b03c039049001900e544c002d03000d85007040780c0000550300c018959109070003c41070700c0c8020400d05e680c50800c0140e040424001d0030107030704100004c070309440d031084a0f1103624442d00b030054002d00d0344942e1121905040c1c440384299919892400000f40503980400103001c0c2004c1050f040d0030010342044520141510300501107001d01c03850b00c40d21005007240101c7c6030403080c50000000001002001420107880b020707080581c076003625404104420310124141ea40c070500d115000206a1ba00c04050000d8500849030703141c4034681c3c82400c40300b001d9101188042440b00241c0c1109060740c4e41007a0303046410300d200c20071a084101d58942480c1d103080c0700b04402d8070500b00062010368007031141500c1a11000e00009405c810201402011040a034001d910171003028100a05043d03015880c0c4403507507001e00700088000151041d66900610043c0004081c8281000c0c100780d02c80701265005e034400c1c0304001c500c440d60312400d0160003584039200c13000c40b141c0380443c0160f0079 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 711392185 1250 711390935 711390947
    0x7020c0a030831050a090932030a09051c121101020906030f0109050906040f030f030902030a03200d0c021e0a032612240310050412 58
    0x11006000300080901e15950081d039508914021400c000c07502c8a8508800c51905a164040c6504094095400e241c8030600029280344c4c1c01a107402401e220303002001c035030000900ca00e00e0443c89880000d00740100e00d00c000b4014a241c02a900b40000030380c5a0703220341e203c10404261841214000381010412800303448150070013000810084c0c181d050b260105000c0c009589000038040005454204240d0004409620464844030b0010101005109801007849a568000e04a000811482c10240c0b80c5900004070420000d0801c0503842c845070303040b44641c0003103000760341c094100c5907240080e14025190240c4a04079a10354100b82a00ea03800504c009801004440283c0702c8041d224141d03024414244140306243d910f00f410008052042d8442c500c5603070055018050040200c0509404100c030003a110600146c54a800d200070b082c0600c84ca41e80d0b540000c5262000b00f4406d00190858202280300203c45034180114000300302d8101c06500aa44218842c00e050100180480c1c800e03030704 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 711393435 1250 711392185 711392203
    0x60a090f0e1014010e15090307080f0f010e03030f1e010b190f1d03031e0711030c10030f0603050105090a061506020d0c060e030313053a0509060714060702 68
    0x1041382d10170100e82d0405001d83c56514080340405803400d14258003082c9848160341c087c620030f80c0081c0044000d12030501440140b030f4000c100900c0b211642204190f43e038007001d07101c0d000048146000c2070310b140311140e5150035a00d07078a4901d100796940d5440508140c01400611413507121007101061040c0c804d500f00380c9000c0480d100c4050110480401c000c41e02e60810050b5058407081015080002a4040207000c2c0c224500d000e0b0740e10112403503d010034000981225000703501c00c002d0701c4615030390b802c0144003822552030f0015218902c100d00a019128962001d0065440c003814044100d5001c965000c400340280c00500607188680886808a1740a01c0380d400160060100007805078410300e0840f80050003200e02080003200e070035a86086d5401942c806010725103881c44ca4040250905c02c801a903014842e81e06250301d103245030009041d9100450746e08444460202000b418000c0b02502c040b418054240c2e81c50345514901040308143c80e24019203035202d000d000a000a10009000352 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 711394685 1250 711393435 711393437
    0x306060825031802040509010b010f050309030912010b09010303050301050f06131e0e0c0715050f01051201020d05010b070c05092e0513050f010b0f0405060a090f0e101401 75
    0x29038003103200840c010300f00c50000d01412400503d0b1480540d60368040c0b42c1c041c03902d03200005004007103e0700140000300d00b0840d920500c501402045641348000c400d44103504015900700b01400d604000003401428019611075014401380004030034568032401660594905807000421001c034141080800d010302d105101420400c01c00900151000b0020411001c06008200c4049a110b50043e65002800c841021500c1400700d030386003e0200c80b00c800c543c01c0304401801c01803410715020984015505000d200c5c0034240c625600c1401d40800d504455441c0740c040c3c3c0420040d612203a12620584c4003540c242d51039008101c010070f5514100705d0b02405450b08e0404010001e01c49044c144a603424000341c0c205503100400300041d0780e1903541119010007110300000400307141240c510310421310181c00402d0b0500d006d0098010010f2040100d80a40300b0803a621615074000344021206030000b50040050042c007660005071140480c00211300401500f0146002d45132100c0400d10071000000e80701d8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 711395935 1250 711394685 711394741
    0xf1206150f040902160c270e0d0c03051b060a0e03090a03110f0a0e0402030d030605010c030302030c1312052406090a090209071808030a05030403080c1903060608 71
    0x500c2549600419481702090100021100d0f04c0d00e9021203141e0325404040115000c40310606410a038040215484000302c03420040a030303117960a80d60302c501000fa02001e0084011004062500490a88107a68060041010881400240151610401e40d8600030990030100240c203440004019287d0562001d8604441e5a00d141ca0b846603030071940b01d0030382c5c01c8107600301c2d0600035480d11090700d00604550329051007642040e1051611700343c0c15207405410075181601c1880030383e030b00400500d541c0b07425140168580c2c5502090740c401e84103100c43e00ca00668912000992140c90b04500c0400314000c2c0c080d107181c0c16542c25000c142d031718814024000b03007a4402c00180d90740b400105442d000740e00200d00040c0000790340c0c081180d044041e54101c012400f01702e408444058448102406840600b01840c20601070070b80c00740c11070202401c003e00b0300c000c040004d000c400709081540c109410038407990043d4003605402400a12403805a103000840441c005854003070a1012906c074011400c1180d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 711397185 1250 711395935 711395939
    0x110118060f110f251223070b0d0b06041508160f0909020d09050a0b1504200702030a0803010f06140306010e060a05070606090e0705010206090715050f1206150f04 71
    0xc2c8400c00030707000c820f450741c200d81c21005ca021038000c0c0000ca0600d20540041507608182c83e40000f40506000380503101d0b03880b044040c01042c03403d6094982007040c2010200c4e0036601c4000107612030046400c01c140d008080c2d0300da03c10f4030f50b1100010b80209450003070681800304100702290022081440107020070005041080b00091035401001c1180e00210001455049540d071241400e0030f0f01400d96402e4201814062407514039108922010303c00c6408024003485412040302a105840c13208520a0000c00c040d82036450034010b240a669003c1c01d12030fa40c0d82c42d0101c0b00d40646460090400050441c0400a6400c00c5541100c1c000c0405840707130710442909004000d040d900600d10b80003008418481d620008a0368010341c03016050408000c039a0180d00100f840c42c1c00c00c140d00160440d840b01d070a11880180c0812188242d03030b54a40514940c80c00000d090300c480c0304140d0215081540080c00c0800c1503c0400c2c0340340242d40c1110070707450164500b194204980100c041c0568150f0b020401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 711398435 1250 711397185 711397213
    0x131e0f0f0303110a02010c11070303090e1005130507020d080105030a0f15181202070506251505060a060206011a03150a0b0d0b010318110118060f110f 66
    0x16640c0158400d10340403402c034860b41048441600032010035009030791280c00c2014034030307005125001050100f200800d5510f1a54030010042e030b03e18440c1c031001c65106400f1031401074040e0f4201c0040c09000c0c001d8103400c0f4240603503200601c8111400e8005004040e00c520842e44a810b81c0d0341255802401068907c42c2521244000c6058840848288510010600300240a8011412204019403426460365128148503510515006030101150409a000e0119541e070307006450100d2308141d00c1c07464481d400300d6403512404030f050000d0600000c03003d01c000e10750880c1c1c2009101e075000352104600c0075039034403003a0b0740c503c006c0c0103d05000344510840340910100c8070141d548441d007180c40d003003443c0d444c20105552f1240d9400032200b010000a01e50b11102032800703981040c03402880c04200504540403014528610b89500816042d005402040d00780e00c02d4a40d079185a60381840706506681d1110040e000980c143c0707029010440101424503032610201d42d010301c0703041c8880075000c4818200c0b8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 711399685 1250 711398435 711398453
    0xc0d17150d03200607050a02010e1c1214040c0312080f0c130506031021022115010902130b03060f0d052401060e060c0705090a090605131e0f 62
    0x502d50f000030004903081041a9042101da0b004424944407036030b9810705220000d096440c001148001603100b000c0c50703055201040c1600e01a0a0300c1d2038109040320404101d02d001e4500105410b00316030406060005001c10f912120341100d00c41c412082410100c1001520000f4085400702c800d2021400001c0c585620140240350200c1c02602d210030140d124400129260070544c1c40941c1f40e01c000340107004084101003016595040e0280035141c0d07082607030014030707200902d00301980010800e03100b030103054000b0451454003005040d4407218541c1c55207003000081d00200704030345241c0c01c003076800684d0341400300c12280924405019448986904414464040301240046503035115450003070008400498010030541c0303254030308020b01d5240000c02800c1c03030035208001e445850100071600b5503c20004815084440544200c00555110700002c801041901006031003541048200801c1d010100718554680e44140000364614140981d0703c50109903180004018880000c0c0136008545040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 711400935 1250 711399685 711399707
    0xf1809010603051509070e1b0d0b0306041104051518061c03020307050c0a0b0d0510090603110a060302040e13081c0c090e10090e030c0d17150d03 64
    0x1000204045580f03a403114649204030a030641100104018084029400e00c5070000405680e26540d0072403c1c880640500c0910f9081c040150400000e29032142d642290081c2040c2d80300102170351950b1030a42400200b107501120654891450000081e040120000311011204805451200c20305000c03409640b40d00800341010b5884622200741d0f1070005070141c2400c0c003041c885c2d03000c0c68a944036403400d1868511407840d210b2217995504d00c14000007418038180c89999403500301c086500d403a246e04540c14900550000184a4140300001c42070050045070440340840544800c283c00340e488608030101d009a004000101c015500420030080d034405503181c4041c064503421346062040f4034605d2040c4411201c2c880300c2621101410700d01c94000510500030054417030710080707501e001d400701d1501400034010501182c0d0b940c0202d9400703060030030958080c01c01c0304003281e0b210056040050501501013140130742c20018500000c01d2044003410700340780d07400090034424134a0000d40d13099401603820 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 711402185 1250 711400935 711400951
    0xf09021803030403081201050603061507020a031b1d0412080907051f020c1f1d0405040606180e0d030c11070314100e060705070f0803010b13050f18 65
    0x91503840c41d075800d00c002c200035807250a49036501e4006000d80703640030380305a10181c0703d4132040c0100700780394a40f10307800d0140b4108061a65524881c41c07000901d4420950400341600c20580d01e01401504030814400a4401c0601190b0239803603c3d282c810007005003120000c100c01e80c61040c2084c450300840d441500502070106984400f900c50b008210008482d0000b06440c00c0642e0100f14100c2d014858080400010740d8085841810210840c00c500d01c0c42ca0405c080010b54086d0300c2d800014407528400021004109001a080508040014090502030211020b0010580702d01d100070b10f1042c46030b504000805895052102c1f01d05500400c2840240f03014008801200c40d140c400c01e10880000e50710503003045005045005a04d841d002880c128581001e10785042c030b0011a00c00101664045e00c81e18080e90388550929000145400307c03100181000404000401d0a08120000c0d01344038800060a004860352a800c201d10682a001650707042000194008180c444a1450f02d50103d95 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 711403435 1250 711402185 711402217
    0x170a0201140f0a030c091508160203090303070f060c020f06010b13090f1a0105120408070206161410020f090405091f0207021504031a04022e1106010f0902 68
    0x45201c0943e200100001c0004c2e580d188203808240c2169a44028100c0441c3d051040d050041010b446450081c28400b60142e080310752400c090700c02c00444550303a0000c1c0c2500d446505500d0040401101d80d141281d505040004a40c80c0d17910004030b141d15070352030100904c050b034a84421071000742d1050610440760030383c11402251401041c002d803903200300d444000152403502c0001c0c0c841310f9450549402d040000800c1001d95452915011b660410b802020350b41d07603405a44002041c62007109641d10441200d6900c03001413003002c1031200700401d00c58003515200030001e41060100e10803070506800b18202400100c0c0d00c2c0c10168021035121048904540031800d600101909402c034000c0c0d881780c00e9400094503c11403c001601c06c40910380e090b852824203042d0750b90700c0b4030303a031606004205852007500014103660315451203450080300045a4812201c44040944402000c1010400482d01d10402d0400c51000081c107035040310b16007a240280a4100100000030390300034003040542c414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 711404685 1250 711403435 711403447
    0xe25060f08130c150c06050f01050321160c17010c05120403090305010f0f0b310906180203010e0d022113120302120910050c01020c010e010b0406170a020114 69
    0xb0021104e074400d003076442d03d2800d0360141c6017034001d85e0001408a4002d00e0b040d4010842c81e00c0008005104481c80d609000ca110740c40c40368400c80340110b09201c40c0890306000403801344180d00310100141d451040c42107440121540d949401c0c1c5208021000006204000d242d41e803820704048140c0051003440e026001954a4a8881c2907030420b4a442c1140da039a0340c40c162503464580f04801c885c0000f650510001d10040c545107101210401000c0034030b80000d00240c00c1c100c1c2541c0034070301e250f502c150104070300419110380345002d0780f0028040b40203620b05004000c00100000b01c005158000307a00802c0f285520780c000782c20712a1700c0307580b0008034002805485190220182000064810410300024186082c1002480c1c0744071600d10801000307007000700001c641c4840e240042a00b0036410507a80c2c40c51102d038158024803424555040f55460401440c4000d58107400c14074403980d00b15414002c0b0340d1502c0280c0850a00000154401c4d0300c40d030700c0300005501802d8524510076200c892907052813 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 711405935 1250 711404685 711404699
    0x402030a0e010c03020417060402090c03060d0f03021005061801050f0102011e141008070918050114062d130b1c050d090501080414010e25060f08130c 66
    0x10000b40f460008070741c02040c14048014010b81c40c203200f4a955004040300d040a401041d281d44000d40b0804000c0c40c000005181074030355805109050b907100c044480e020080d42402034940100148a40480f030814010400c0740c43c001840d0b20071904031506104290b4680301c100000ca03184482c10a041d55200d0300550300d80155907200320000204400041a02e50742c000c1c03070082281004140e2078141500f004207003d910800541c4105a0300ba0391360004010300c0d952141039496003040c000628075030030443c0529017540365070f00c03260169605462a1001042c50110041484a4403801d441f07501c8880480b03801c5881c4c243d201c415004c034810000a11800c2c800b01140785c02c03100112101c51101c66100c90002c200080140700545640f5203400301c0440d00f0200000c04994010740003030401100c5481c0808007000c00c0d44214281603c80080754248524075000e8264040211a4503050390f210a00000d040d40c061441c0b04001a56552081050f0f5503079441601c903002d09003011344261035001000f01d609 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 711407185 1250 711405935 711405941
    0xc01030e010f020f070b010b0c030d1a1f03060819020904060b150414010306030f021908010204060f091a070b0405190f1e0c05100e100e1e0f0402030a0e01 68
    0x884d00081e20b190303680411304100c5410041030b48640d802010070026203164240100507540d0015005c00085040d10f00c4283d008a009044010150310804001601d240c004c000b5000c5258980240c806018465076980d4041e1113100043d030000b01405540b0419006151101070075070303c00d101e007400150020b409404681040d03203002100280510005086c05a103441c1c103003015100509103003d002180c1503a80303010005004500003070123000c00d1402500a5140c0d5007008014251000086485941c1c84000600f9145000c0e074140c00300c0c02900c40030414048400307448008200840a0074070b40301065a460002e03079402002a519030250b8043d0703100c030240c0d80801c050481e005031070085400201d130401d0500280000d2400300c030300700d041030101d00007060000000121042160504130100b8203c0c000d44a848018003a26489441c400c00c00780c101d50007415103c0c0000040d107495102c000c0326140b034000f42034403468150703000e00c1c09a800c0140d0705d07141d002154880d01070880421000c010303140302402c4d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 711408435 1250 711407185 711407197
    0x160f140c070303080619050f040b030c1002010b15041401080408040305030f040609090b09010e06130501031203140c0720060d060312210203100312170106030b01020c01030e010f02 79
    0xa5a0b40c4c05000d51407400310319491008100500c1d0b400721502e088000344503102800400c1e8000e58032070380300d046903a50a002d0080c3c01351000e00100c400500c2d08ad8001e0082074001c45540c41889a803007a01050b4006600340c50554030400d840c40c01c944100401076800086c020030031034030303e00c0800002c400502c003030003c0c1c00403030b40001015071142d0601c0b8015110344580d0f003219017120310303040480032295280000076045410440c0300d440f4580f41c034400b05002800002d0408801814040004200101904862000701150b941002011035000c001191044181e0f101a010541400f03000003098000e1103507100041b03140c03010087d020700c21000c100b064020904076001140c0c0d40d4801c106203c880c41800440300864500b40100d03d040300d0140e003414000c2c116540203194044001660300c20214000c00145820040000f055240c80e1002071a0400c2c114120540c2e804840001641e40d002e40103104c44264140c0207029401c0d0980011001031540113000710a07507488820441d94284640300601c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 711409685 1250 711408435 711408437
    0xa0b16050120031f03020a0306050f01060c0f0f06060b07140105060f031e0a0c06020a030e0301050c1b030706110307020d02060106090b03041b06050403050c0306060a170c100e0405160f140c070303 86
    0x1039a11f00140d12f40c407ca07105a0080f02800641807407503000640d03c01c0c07102122903024000c44c08400d110300700a40280300c40e41080c200d500000600c0c4051008020105082880d00d074005e01007599000103124050701e5021109825500c40720744a444d040343d032070304d05400c3d6030441d044500f0050b1036201c2c661038920f0781d84aa0b016801c92004a002e0660008400810502c241c0c000d0049060100d038a00940c410700d10a8128042d40030095804030109108543ca0b10b50480f009000d91118030101041d05e5000f0b40781080580700d030648041c0318034004200d8504940c050340b500f030308040c40d040c011160343d40300034000c80e01ca480480c60301440714024116a00030300800c1d03031910707141e60542c6081ca140c016000d03083c0d44207910110810015a8480d44141305854004140e007201140c2480c441d45850407200c5c003030754001850030100c0345a540c000c1e102080b50303604403820b200c2a25007411800e5055a03c40840d00051419100400c419024203460b43d400d200300440b1500d041d10101c00d85040c608130f504114 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 711410935 1250 711409685 711409691
    0x20a0c12050f0a030503130305040b181207030305030a0207051015081501080307060b01170408190509030a021219050109051221060a0b16050120031f03020a0306 71
    0x4080c0481005212800740c0010018030250091341c4002c2d0890200608201d1020070521140040500c1617041d10300030041c82c00443e0320b8200480d0404120403278041aa40508040040c00d40c040300e0000e02d01c0120390f003540b559031640e2a20407000003c1d5102131401d075010700c84c900421603444001d11400c01d28004943c00c0707415150809003e40d040405035880c110070740030880018482490007008171396440d64402c100098402c880d030016a00f801c11510000b0198080208100502c04110010010092003d01d1a060440c4501c0c007681c15004424002e45c059101c5d0890000504003500d01042c030001801c1150303409400c1c0344219040d01c0700014111110f945410b289400c014041102101510165034010300b040545030800000ca0006500c40041c002d011003c40c51649071b0014100162424070346266894081041c003041c0060700381c4045410b90b03c0c01d04006081c0182840b038142d400c405065040c591b84a9040c100b0f0071407409925052042840700d40000140e4a0780000380081d03100d09404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 711412185 1250 711410935 711410969
    0x60f10030f170919091a030715020a2a05010903030507141009030c020901120807060c14030c0c07090c050708031e0f07090f0b0d0515040e0109051e0d0807020a0c 71
    0x28003d5441582e1102c5c003445509481e1400c9a1f4041550303002c2d5030009808200c2c80c41541012480d0005580c005080d802c0803000d2001d00d440c4080382801800c40022202080c603650302700440d1452031501c0040e0005030140142070003d14441c0500c450344612404039035550301e0310f07001e600880c1d50360303081100899100d2410a007103041003d840340c01454940391907a0b02003c00d4850804038481c00740e009000a84e40c2088903a003d0041a20400d4008003100040d168903000040b06115402105600d480f840303440000a80c645240c06214a5060603030b80d21420600d0681c4c079041039410140051000001c8090641035800c10300300344a1141a074031085d1030305414810b0016054801c0f81e00300d944041300e0a07809201c4601084210341c0040d1a0780000241ea90f00e11190042002c8000c01080d0b0007420801c6002003150f054102009060080080da00020b003a1461484445803c45d050354050b000340c10100350307140c0196a01036204a10740180c603503010142c0da85409191041e04041c060189410328 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 711413435 1250 711412185 711412199
    0x80703021315030305250312050a0e0309061c09060219050a020606010804030c050f0d0e030115090b270f0a0207030e0f1c05060f10030f170919 63
    0x5a015407039001075003040003280b40070103005a8006408090280140015403051142a440400e00009035040419140d8520752600611140c0c0381c1c10303905900d5090401080c445e49aa20502040008007001117140900803010310006030084410320300307202c074580362030b509445190041d90b141c548200e0380180d840c07401070800c1a00d400d6180d00716040000601038000010b40000303c180e001042424103903140d40d10b5140846c2c05600241c0014150300030022003040c101c100142603030b0141490345500040d8003003035040c18204c444040e04001c14100c01d1004103c1ca0581c2d42c05843d044034050700000d00c07040c12001c5100d480e2a205c0c89031214050b01b10400425035a034000850f0031000211302580380c8107154400826095841c0c038154401c000e810f11601042c1e50300d011140840140080b480c04192050801ca919440308407041000400f500c0300088400f100604000290f03070f03000321805108141500ea00d0108007079080141d1801c0c004002c800d41950315207800d2101100e500005d81401030803c22 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 711414685 1250 711413435 711413449
    0x10e03030103022d0103090c0b18120f03090d0809060f091306052202041802030906060108091b030106030213090c1a0d0e120304140708060106080c0d0e030408070302 73
    0x180400c550585006044d1030035516a00d0903140d50921740800c50200d5414400399600c12540482441000020542c401008020303020380500d03012241080c00680e1050340b02e84425003807850f4400b0303030070400c2080b03810325040149010f103900800a45017006101e00220780d281e40402107680a00d0004200c1556902d0404103290a0f480c940d035003801b89510303007030104010385000c5020082c0718024090720326100270b00c0d50503100108140244c000b010307025240401c001f03520580b07410040d8000d00c00012841d5018501203401204140010404c014203c2d01048404648500c0c0947c195200c0070000050782d6490020704082d50b245000080102051400303c440320400c0d0300c6403101103899251030142007408810b803030412008060218064a90400103418079040e00b004020001006c02030205003d1081c600c2c8403c52400400c40f01c0940d20342040c240c0c4c44009104143c0050081000194800c4402c006070888284a100120742202d00092150035904650499101c03a40407820070420340c90901 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 711415935 1250 711414685 711414709
    0x70f0819090b03041e020a120c0504020406081812030a02030f070f1b0f1a061005090915030f0a06050a060f141012050901020307080a151511010e0303010302 69
    0x401c1410020b0b140110020b0745010041014050003921003038024841d05102010300d00960041c14071001d80d80340d0100c10480e028038801500c000701614000f14280c10030344211000d4030360b191240c0c0c8540c0c1d0340d012900c030440c840c00e2504a80303004071481415048200c101a602900028401507140e141944688000310002030994040200c0418038180041d00102100304207001c00e100c5235652000b900b4070003004080c03550300030015001000156890702000f00c03030350b02610301100e08612464080104403114019081c1c0c041c1c2c0901c1c80b001003161710451b998201d8442a0150568801e4016882503909124001e8010740c0d520b52604c0c100050b805561003164043c00f450400d0724405400c01c0e42402240070b42500301e50080031032a034a1056075029540400358418010428482803901240b600c2c040c0d0400e582100c04151000d001c50440d0703100d070180d0050245100d1101c42440d280119607507400310341c0980e00301849800320101d0b030070000038082c60201c510304500441d5a545144113000705d00d03a02e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 711417185 1250 711415935 711415937
    0xc01080f131709031905010b0d0c050f0f09040c050f0a081005060109050d03050c0c060415080402041805060907050a0e0a0209010e0a03030f0e0a150c08070f0819 71
    0x80810095504180c41c0703580e5a1580000000701d036103540005092a40c41101c01d15903040c0f08090314401c0300340914007841d9105100f50021300c40819031400380803c1c410306500050003071420b10301c00d000c2814407480141d901c3d04002c244904240c03202c004079011290541b801e4900d003802c3d10003800541000c038981114500c040d00c06044541c9000740003601e5400c99108944a551103002061090703100f00140c00c094030b0000c1c51040203020313070b00d4042c00c0da611008908140d030003098100003031454070000f43d80c01c6a040b901640c0c401407010360201c50f4880021b1040b640141d5411001064404140449483d41c0c450700041c480f5007440740c040c3e0b02e04071203a8040e5115543d00b0406010303542c0255960340e00103542c02303400740e00c807500b510043e5a16075074110003a41280081c5030001c02e050740141014803404950704c859a1112080d018021640001d00400d8200804061407202c03451045802d00310f91409880c0b01ca0a12000e80d8403520b11540b03281c1d080d5490311010903043d00c400b52070b1111000030491 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 711418435 1250 711417185 711417211
    0x14360708010815041406010b03150d170309120c0d02010f1109100e040f05070f020706020c0f0402070812160512060d020d1b08010f05040218090f030703020c0108 71
    0xd024406a62414010000102603450380040350410a00c10222001ca1540b13a0603541c49603100c00640350103403c2241c4d2810300c02b807000c901d01c2050529030990304416410000e841ca41c0d2144014079422580050519a11481090018040c0144c0680549880090040a40446d40d043c080090a403044d08100f908545d24007496603101002000890b440c207201035500c50129420044c090703401111000d42e17035410070305000007900881a00d901c10b5118201d541c54100468480a0303013281c0c3e90f0054000d08026038080701841c0c85500d40300300071161214000b400546018295030795107026130400340d21065044060720a00403092034111008204a040b840c02c05d0604031203a00b0907400c1d107009004640901c1507200ac0c1800c0d510741d20700d00ca04581d00080d00d0a0500308400718449460b80601c18000d080d440c00b05d907040c48455900600d40175640041284a09408a4500038200da401400003509440f03103403c54101e0784003d01c090b16500340260060001441030000241c0b5600000700110724001d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 711419685 1250 711418435 711418439
    0xf01021c0212181908040501081510031e0603060c0201061208030a0b0103090f0b04030f02010618050c121302090c0306010f140c0708070524041436070801 68
    0x80c1042290340f00d00d200c0300e0b000d4a41044842d003400e01d6003540e40005507810b088a004148286103006008680c2c003030341c03030314119916801818042c107842c4014651007490009102d0352944a50400e80705010191545c1c0e2482561070f52610403a140d0b9802162034a031500030341d4504540a1190034002c1100032441c56045180355034010085c44000e0540d044d080d40c80b034060a01e07034469800141c2482e400350350202c03046010301304211b290208a40c1280010480041c04170b9151040c05510304845185188074004013401803000060030004206282040080c004608180b2080001c80e0084441001900d1942e8450052145d181ea0007016001c0c0a8420403d012007641d11003041420f80a0901e010f0990b51446805d0066a201e200c0084902d40b14881300846c500f8000b00c0c0a904480741200c0440d00003c40d0400c4c4095213245040c2c1c030540c580148800c00c039400c2c00c100d01078900b0b01c0040040b03c401c104040406801203400c0707884285d0845010441c60300c02c09841d42c1383c1d0040383c1400c10003950340c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 711420935 1250 711419685 711419707
    0xd1e020f030d0c03140108100e0c01020a030c0218251704021924082a070c09020f0d0b0a05030d140c01060e040506011203050412140f01021c02 63
    0x403107900c1c40d518500e82d4481d0000d00c0c051185d80404000b100590360355507656507840d0000d907600500300c802111280b8200300d000b8040d0380040c2203030046d1410303000351002000688080da0b0800280074180d0300484a03180348010742c03000228180c4992098000c5e0f1800b0042d00303e0111900d042100d08030240b0400221101d094414030740001e030700640c12034104440305040b18019090340c1c0305074494603801e4180b2422074200014150054002065075880c0503181d6501c08066a0107a1294004424102d1035074000048940c50340090000c00d0003100b0507012b0300d9554500034104d90203408a40c80b0110003141c0c10020300030f80d01900c04400011079030261898240000691a000b025040c281884000c0381d003540c1051040050b02c1c00741588038000c006040e51074251f07000c441000c680c00c40700d600901c400440c0d112000710141000f283c240c0e69141c02c0504001358030340340c1d400d19101130780c0e04e0f640707202c101780c240204008513080c800c0380d8000980c88000300c1c00c100c241407903444014140280144042e01d03001d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 711422185 1250 711420935 711420937
    0xe13020114032503051605090603060d030c200f241804020c0a020f0d0b072105190c020106060e060f0408030d1e02090603040615080d1e020f03 63
    0x40c050301c000c4107903a621128100b01c1c1d0b03000d43d5016116100507074107903107601c140c055020074420021008501440650070341c0031111403080e070084690100c002d001103080c41c2010039550301054481c0c14452280b0503503494140402c03801c80045030300c1c40248013500b0914204501000710000e020341e104240380f500841d040025010300726503044811000300d00d0100260040101e60900c1d5005081107599a000340121515002405416030040b00fa4000101003030909404600726030350030029500ea2526000b00c01c58080451801d40b02e03013100024020400c0d1a05031041d54000e8548071400150300420580c800103544074103400c0030035079140030420846c180d0092180d28240108692203681c510000c18100c0c1c81e8055500170a0007171002043d60300c0082c41d41d9009291240b02081070190403a00350450205a204190303455410502c2480440d00041850700705c0c41d1460341c9001900310762130311040042c0c5405c83c101e000cad1000440c10704585103841501c507840200c121940c40640900059002c03441e5407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 711423435 1250 711422185 711422207
    0xb030c0405040b071d0604090b03071d1501170a0f050a06060e010503040602041502301b01330e010807180209030d050403051504020f040905010b030d0201060e130201 73
    0x500280c100c60300d1034a4a45e00407442c04450080c406520f468481281c2402070102e0301007540a441401c80c00f04036070f540d411503000000d500f5202c44a0640d03461080710351422805c51000e0511416000d0b405141c440c00d440544500035820380014669036141c42003095070005416021003a250003400e0200075446800910310210a081144c0d40e034840d460700c080288242d90060070b00c10140140c9040c216800b140000b198032100030420403038880c2c0702824607418400000c0700d240e007008002d003d0036a075032102c42d0424040800000101446040303c80b0740d00c44800c15400d00442d010042c805c01c16245101000041d1860404c011055810190569134030700b054081c0342180030b080442d240d00038125404031075000c00e0280a81340c00c0102e5030750140c01c941050204035158024100c01c00c256250899100341300e5900280080308035608079090000401f203ca409403030a5403905292065a101088000c4490015900000c2c15500d440e205030b4080c14068102208103241c4855000035070b900443c43e10f2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 711424685 1250 711423435 711423437
    0x6040621060b09100c06020309010c080a23040828090e090a17271008060a06110a1e050c013b10030617160b071a01090b030c0405040b07 60
    0x60064138681094448840030700d00103103594000002c20141c21010740040c0708402c0d06440e0a26680c82d8910400700340c501d031a04181c44620710700d0a05405103010b00a894115002e443c1e0f6511b00b180fa86e03048020b0742c810702e284042d10700c980380392981c0c01030340220807000502480d0340e13040315406c1440300385807078040c9200d014003120045500c0000c402958422590000c90640d140804d600c9580303604180348140031102445403084141074510313140100540c0744107660091000c840300c1e00b081c0c02600c03689011904150540b160707484000006002000714200e44001000760b0918080e5890520314210407505414100482c001a0306c0d801e0074081691200540228072959a20403140e686c0440280c2d2100c4055111100b80b02104003550142c0c0304400f5184030407131903c105040c503610310f5a43c0c101c0c003024071408102440c0400030351032104c0250912038400c207a0000c04800740c8030103041e00002a040004541e03a1011030401910703080016001004003510107120b10300e007580311842c102500819401c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 711425935 1250 711424685 711424699
    0xc030405190e090f010f180f26090415060503010e0a1b0c20010203090405181606020c090c0d0902030c04020c0d0e0604030c0312050906040621060b09 66
    0x540941e4101034000080c0680390703082ca803075203494000c007507480c80071025406440d441c112440410070302c180101250040303500b030111000561517443e00048044988280c45007040081c4285c900750b82c100b030441000881c075013100d40b9550b0800400c001c0700c44051101105214000d01001460781200589045519040c5011035943c1e5203000346000d410f142a9021102e03008540803035900d6040701405056500407086401c00c480e6803803401c59000c210700c103042e0160340144a200e2541c90035400143e4810890800a90400448900c1514084400c0c0070f250860f1200700d400d2202d40d80c100310208801904550030031807410507900b842c20fa48106c3e03250402143d103902d06181992400c0080300100040030700115900c80703006419540710070308104d000001444070000c461302460010185d40c181d176006201d245086241d07039581e1a081e0030a21a00d020b00206010708801643c9500141c0020115602d503c0c02040054040c00e100c909112454505a49004810302c81241028190381107034205403008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 711427185 1250 711425935 711425959
    0x130302070b0a171303080a06060801090b0d050109051f0612030f020c10050c0c0904120c1a07020717010c1d06270a0509040b1f0b03070206090c060c030405 68
    0x7100c03c21030011040c00401885000c0c05502c0c10415003200110307000360380b4140e40d83c458141c800e082d940340d482000000b51682c001803003400b4541c1d01050b260b25004110310002003642da01c00b425038100c1c0000756010b4004048404c03107841403071418019198844000c00070503003420140426819002c0b4098200421a003242c805a802000800c0101c0c20041802000701040140188107034041c41c80b05041340944041a4003a04003c901c0c01d000701c0c5d000e24001c0f90403210713000c22146810980000e881c070030140b1800d03012451007050020f0007401300783e02920586060410302c9891040035030001416a1402c2d2402c24003541c0000407880030560030080070035034683c182c0040c02c3c5004010000340f114600300404205a91b10005140c4034000070b0b54940c400568400401c000154110782c00f6003c0301c0c0000000f5101e140c960401301000c24134203403c1d503c50341c481c2e0060140f80c10842f01c610260b840502440b441e103600304690444030348119481480c1c0041b6621460700d034022407154034012221380c0d0304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 711428435 1250 711427185 711427187
    0x50a090902030f01061202040605030f04050c061809010f0509070807051c15140612100e0f250f0e030721030305010e100e07110607030b09130302070b0a 67
    0x244010030429006549a0800ba005100740410a10400c030100c6c00400111403051210b0081d54100d4945451706400c48d503400e044260200401081203406011b100018484d40e0780381c1010346941e01b52121300c445414141d03c00d0001320201038124051000c4c41e00010862a80c440c984036511500a01d0081c0507919408030a035603070300400108000e400040c1e8a425a0f109035a80042e080196550094640603500c1c2c04001c01d2004034403d42c4d8200008220003803680305501d2011390040e1000c62000d6880d40c1e50b00c10280009010b8803285508450501481520a03104001064202003106e4804654000d03150290040b046130311440c0601209824850070b5079030034444000100003c2e0360a03014045e0101c072a4170085007266007180802e2910002007062030303503180d001d449080d080c0246030240b400c0021004507000014400301c20000507022402c4100003d11400303008154545000c1000966042001040700b4020241031400c00100c40b02e2001c20b500003200b100b1200510a40c551359818408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 711429685 1250 711428435 711428447
    0x20010207030606120528030f05071b05040e0106060e010e01020c100c050609120f031306060e010620030a08100905010f050406080309010e040f060302040504120f080f0403050a 77
    0x440502090710f4030a00040c030561a00a48030024402c0d01a520400041c1110640142c81c1c041e014882c981b012a0440000c2d008942d604c10071841402c226040080035a202c4031601403101c03015025000c12181008981050300507079810840071b0009011050034064020003040ba280401410440311000301404c0b40d0081c0500303a074041001e0f0820440e0b0f10181c01c042c03c00a02d941d001c070307a10300c1648001261414042118640307280010441c81c0380145408481c0c6160700041d00700030000380740c10710030300c0082d15a1103900b000301140c15841c0c0156150101c00780036004520700211a447d4113075009503c68102004540b08074200f810095680e485221101610480700d400034410302d8074000021030718032001c40c525001c80e542180e06004040c0c44961064480c02026510741c0030071050020701c103da240070b40205000d494917403400946240c2d00c1d00050300391401502c00360b542d00400008100c1e8580e000150401515850804098030b05081000714070940c401000078041200210305814440c2c440c40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 711430935 1250 711429685 711429689
    0xa02040806010806070f020613020402251a010f0506220503031605120408060f07050c0a0b06040b061201180b06030a15080f070b0313080a0c110306010320010207 71
    0x34100c4980d0368540b128195034071800e95030540031486810345482c0c07091000030f8a40c4900104442020380091507405e010280d00f00403c6d20581c1e5070038103d04560600030b100d81c1c8800038005c00780e80410201800c03282d141c11406810218202c3d050207410f00c9191038040403030b4507982e0300390700d0418082d14100c4222480c40b8950003155041c000002c0c0c0036580c09142c0e0700100d550b401841560544508507400590710b205a200b00030b020b4014400181c0e40320741c1d07440d520f40c0c00130306030500515000d41541032600b08502400300f103408003202d8040c00f00c039092070f01c80d05007842410f542240c6132402c00410603c070040e05100c0d061900d80003807000d04254221750443c40100da40901890313224140100740c1e03805464442d90204005c04030510005088400240300c400b40c2d4040009052424100b520401443d80014103400c01c00081c1c144820004040d17100070700d1140743c555100e031000f036040c0c60300e5603440801c030300400d2003540040f0050005c00d0b032a201421001c900407032019040c1c10f680300180c2c00d107000d40d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 711432185 1250 711430935 711430949
    0xf0201031a1e0420031b070209040807170a1206050603040f1205041d0103063806041e0e1b0d05130b04030807031103160f0512010f05040e030702180a0204 68
    0x190003c801c02e884c440c007440c00b4681394451544c003403404100c0f2007043d000d14400a903020103500301090103d50050000c1c01054040c0c6250103d0903012180030f4103962003441c100000610340c8611401100c164425100070b84811102039140d130034103442d003004041d900400541086621076011b0f580d24094022a0014614aa0310710021fa070407500c1c01c6041c0c0c030b0901c4180c46241c106990000d8030524809a9003005003698501900b11419000b6103411895030200d60344c001c0c9003088045040c12820010b2039100b0401815003809a0400000301100c1c1c0000c0e01d00c4518150107035002c40c044091009813401091a0200011140d1b20f15071500c00d00789020502400d458a51001d0006242c0e2050f9454412001c54406204240c901209101c0c948030458070107a82041d103001c40129148900f404050300302c0580340030760529910301c10500e4054000e80c41540401c1c43c060040080d4281401402007003104500510b0401a440d00400c00040c51a4040b642ca0f28400780083d8030340700716038165005440e00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 711433435 1250 711432185 711432221
    0x2011505060c191a15240408060906090114070503040602090f4209091e1302030c04272402071502030c041e0e040f0201031a1e04 57
    0x1070b404c00e076a020007502e40c11095110100b001420a03160240c070316006440207071104401d600d000a01c01507040c0708000c0f00d041108200000101c040c420010076015132006070192006050194056003100d24038001303903603108000d00800088a070021305480d405034200ba000b50b40e4011b003c00003060203081c07405496000582e1101c001880381078078020001660400e41203410003000301d440c04011942c945419121203010805103101d4141420b4143c1c220200303000383c0100003085540300ca4140400c0364004c0c011103034034602c2030552904000d0b400f0400f00175102001441150b4041800e2074420001e800b401d40400030581c41001045007000340006a1583d411140d0604e09007a01c01a501009040d110403a82050740d0b01c900c02c1d10720885c0d02410008800b0f03031606240054102c0749a0740d030070b10b100e0200115900000c4c45071221424a104922a01c1908101d181c180b00242c1280c00305200300720b290481307000307980040e1241000e9070380d070038a051405500400341200080140c0007020802c0d42d0058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 711434685 1250 711433435 711433483
    0x303020721030203070f0206060618030c0901080a0c0e0f0103020f0f040501060509010e060f1204060902061902162114100b1f050711130507020f070602011505060c 72
    0xd4594055802035020765a03c480c01800301c02d0888c0c3e1884162100c541c441020800f418441d038080c11080251440a01a0b0303800303003141000682c010900341c0c0310710b102d17402c502079000030002584483e1002c5c08070f200350310030742d81001c18581401d072005000c001c1c00340c0482c400d15645540d034201c0010325840300810510842d80c65031401000e54000c0801940130600c5004614004e2408074103803429506e08801c51410014002d040207490480900295401d6035204402d2000d40c90310001030002d07161050003800d005071007100003858031000c5072045601101c644424010b801c81802c44c1142a5240b030b0b202e000b40171240c01d080d0201c04035441c44822500c9039845810400880c0e0b00100d011010480d9841e02c0503d01010b100b07011403519a400340064020007021000418081484c1c1c580d41c03014200328407180320000780908481090340c120007da8044055400011000c0003120041c185910080c40004504400b8201d10640b5005107807160001281941c0b11080801146080e10302503084000300013 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 711435935 1250 711434685 711434687
    0xf0b04030309300c081509100b24030712090510020a2a05060708100e15040e0a06061217071b0b1210051e040b180a0f0c0c0303020721 59
    0x2504c0d00c04c074035190040b540d000c1e4038074020f0031080c0c0c40ba4000d00050500104190b80303010007401c2800700b055210101240010181d1045141d0700c1c420320454138025660f05003140050841302800c144444014108000da400045c0040b81d4907107030020003000561900d80b4210141e0304120703d14501404513001000f1144000902c0d5902000c1038010019a800d913154050121110001112444107129845504028111b500503502e030744400200e41d00c2e8048403819000800383c89043c42c0340000c84e07003c0388051040c42003070f10441d8014150300801014030310b02c03640d54141c5164861180b61015801080c05000c0c0428103410380104c00800008049954840106403030a030007180340713075074441c482c00005805c071021118144207880700103062510680f00440401807503088800b039250020b450b0064010540c40341450361140c804884241d004514003030f10018101c031503182803042000d080003944080990800e0030f0b03c0c2030310b070107280c00343c1e49074000d0500f114034603a45d2002000401a40034044045 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 711437185 1250 711435935 711435953
    0x9020c060411060a02070e1f0b030f06011b03031806020309060115031a060a032009180105010516060e0d0509130b031f0b030102130f0b0403030930 65
    0x107907100300304092901c00c606061120364025a454000583d005c290240980b2440005150b4000b50a10f6500c0c40d40c2c0c41000d400b01c0315099503008035000e0002100340080e01c0c000e8143e0fa0381c001401e1816051104041600100c21040c0079005000d1650700c40b51400040301d44c1084040b10ba401810542d500d0900c1e8442d155141024410f889040103110000321120b4424002d040307102800750b840f448501100700412001d83d1080202501307050355030110b5030001c1c52010440800c8002c10030443c2d20780c26050309014100d0903007071500391420144001400581e0300301055400234103030103241c140c1a0640c3d10b400801004950b595400d680b082584038859280c1c000018039030f1243c169132034140a031721707002c440741a40c1c0b000d41c0e21a40360f080900c4002d2450101441115820005070300801c6460840010030f0880e407104108108102002c4070502c03500380a03662500c0140184400c080c5805e00d19100144000900d0145e4408c20400c442140c586c0d103100c10840c0030608060800d001a1040ea00c1e00a1038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 711438435 1250 711437185 711437191
    0x16051e011218050a030c0b180c100507020306010e100b07080409110408120301030303060816030b09010906050907093903020418050907080f03030402190f080102030406110c030901031509020c06 85
    0x343c04400030007d102844128400c03455108e030f83c00109000c40d0754004205102001c03100900c20004144940ca0150798108850781c02040b0000b5a00c9042c1004407542c89606041c0d0450354003080100070420000d030303021b41140e003100c403164000103a403079040003444c1452256501c000c01a2081c1c0444000c0381e610f42c40198100c03480380c0c608010140c1c0d12184a92250784d000640d0282c860b0705038007040812106501070360b200312080000250400c2540d00d49040720400c1c1c038900b0165220358828000b02c18544035840500307010f071070203095502c1c000c49030319180d00020345035010811103502c8c203510250003a0142c2c0c016102a103410088064003007081e0005080c201d0784190349100307a1200007a07801012034000da0b5007003400040d6145685030380900900d8840504000d143c400c03065000208030505840540103841980d0000da0b403030a080c00c06c1002c1d10b80c2c1000414901d1800c0041d075039100000800c56103112801c1c00c4c0800c510b80280440b100000003640000c0000b400001c1300c804880c004a1010700c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 711439685 1250 711438435 711438443
    0x21b010c05120a120b060a0c140111030105040c03141b04091407031d0c060f0409023106210b04110a030513080403080708040816051e011218050a030c 66
    0x1512459071030760f1314192a17400e18a140c004808220501c1c0c07152049140800040c05049041c9908081240c4103084030000388210040c410040014450f0740f070180125554040640f4003800f4940303078240f441c0304500003c0c0400d219449110051840d4802c1301c0d040e10000c000b41c4104100c910181d0304c18885c410811107045000078035081080024001c0b0700403c00c2d2100030180100401111a01808904d600041e201c1c01003c07424800050300b009240020003454041c0c5070141d042c100300c1c400302c6c0043c18461010081c81d40f001c074024890300e076000d06d03928005d00c0384200c01c00109021445610050034440b207019005800c041007103000741078010041408000e199001c103c0e5580349031400c025014a82002410001c0400042005c00d545401030030101c1c2c0260021440c0c40d42c0c1c1d1400500d01030400348607580e41e074a03020080090f403610480c0b0060760784500c41404890041e0303500003400c0c1d1102c90592a0015a1940d8003c1032030032040780d2580b1581c1c81003c44031224003a0801405079010100103c1d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 711440935 1250 711439685 711439697
    0x10605070f06090c1d01080d05070c0b0d06050109080c030a02060306010c231510030228060810050618090a1808040f170c010c0213020d0c1b03021b010c05120a 70
    0x1082035100c4940b94100c0700642d000d03240062315081c046405030f00c1040e0646400b40660b4000c0b0301296050000c0500034010000060311070b2810340003424141503540f19408035002140c420f042c94402142c0036000641c1100c0456032030303071034000684200c20180e0000e0f0880c1d9110003a2039072030003030100c0c4041c02482c038411600c0311124407410340040701003203800c5440b802d01c0e0a004c00040c18030318009170b81241ca05000b81004c034850800049802c2a40d40904001044842070200c011440324614014102c00c0c0d46007407419185400c900041030074003102c1350140d1744172000544985407562180c50580da5125481c08082058245000f4030b0b0054014840c0062002c240020000c00c031071000410880c604014010316000c6000554508054030004d0380c00c081020159421003095100415030402e84220005103102140401407081c081000380526a8000302102c4c0d011070740000d0802603044074442e0031400ca82e002801260560051000140684900b01000c080544944050032000015988d20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 711442185 1250 711440935 711440969
    0x30f04090f14162a0807050a05060f160c0b060108190f0207050106090605030d050c010b0a03050a12050412081b010e0a1a0103030f030506010306031b0801050c0f03010605070f06090c 80
    0x41c0b0002c0c00e040007030344c1c1c1051301003113141c0001e2064001d05401401041540c00f4442c82e900d400e800e025081313a08019151006041040e1400500d210440e06501031410b07400f583c01c0343c1c1e12030314009009013005041c090114000380108660413010f01103264482c03024400078101c103a50001071340200804513055402d00074086002c007034030320900045460040040441065195080ea101c1d44005c0407028a9521050b1010090b103821800000844c4140002e05c8800c0303c5082c074002c161034511400702040b008000c10482d21182c00300000c402c0d608805110f60752600d1154a03154000340c0c1c41d4001c465400c0c107200e950b10f11004991020007900540658403440710498802172100c3c030900008000c84c2d848009900c50500c203510195000030181000121681c0f66100c01d140c14040000b9030720070714160303a001c2c012038803307024854214101d03685003420000b954801100f6800305000708800c001001ca004001d100c0e402200e100c2c1c864000d901000041c04034280042941854003520044004136512 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 711443435 1250 711442185 711442217
    0xb091201050402060708160512031602070509010614070209010321050901080c16240609090c0603020c1e0114060f0d0b09070b0c0309030105010602030f04090f1416 72
    0x1090b1007694024a454a02211a5207441782c60b040344c40100f001003014100b01c40056420800380b4140d120300c400d0140c50340381001e001c47d40ca4820a01d0315045400603442003029454412078281519010704000364281038002c0c0e1700c00540200003020350301c059070400010503c1030b00e4403403c0c1d01d4406400160311a1070b43d01002d81315032244100300c600081c01600003841040b10310024100041a00200400400d002c4e15021444c83d420340c00e150308800381035480c1c080003e040c481d6400804040005201180440e2900ea90340c0030703284251018180c0010b0f102c4072141090040440124051003040581e643c0d488030300d802480805001c290300c0b110792000ca00c0f81e284c400075407100550002d050203078140c0c980c0d0315400c040d00e02034003207140c0340310b040008180c04003241c0141140b0445880115110b805841c101425520107a0100c41950020400c0c1018180706c401150241c4404210114880030342107041c0c2d000300140100040000d0320042403001031249904160501c1d84d103540d40d0f0988103e1111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 711444685 1250 711443435 711443441
    0x2307140304060507020d150c210c120207080f04080304060e010c0b040210030204170105060901060c0f061a1507151112041e033501050f13060b091201 66
    0x400340400d8003401010014986030900344041ba100341c080707081c807814000e044010b4401207020080890640c581c080581c00f021054207081081c04c00301480188600040134003003d41c0c1403107054019030001403042c24009120115880304104081e00c59a6170340d50b0340e000703840b50031502440000a4069209042c0b0f58030401aa040c03464200b01d6400140d1265420841050460210384050640a0100090024010800c81d0040364403100100c0d49140460811040c400705810507800e00408081001c007060500100031141540598000b5035016203040031011200d040524aa1207038030f030040a840002e80c18098580240f08440741c3d80c4604401e900c80c0d0035100300c040c440c84001c000344050b0582034000b82015030068066400e4509100c41d810742c0c03031100f5080d90030513808510f80750000c0c544020301141d0012501110038410a18085034950040403010601c1804d20950880e2140501c95a502e15090341c0e620003290100f210340c1d501d00714002680c0110000d46e2051042e4102050b070010180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 711445935 1250 711444685 711444689
    0x10906120b03300f0d150503060109060503010b0a060f08070c0f0326091c031e021215010c02040b18010e06120703051c11010609021b16030b06012307140304 69
    0x103181c4c070308042030007070312000a0000e4402c4992003030400b0000101c0e92030600000f4042d124500300880c0480c2044181800d45101a07240b601400d1419400c11a90368440d1603110740d034026252145413600d58280840d01001d8195005c1c000500340c1040004140c1c00c0503030100388420a8400c0f8020b20340c01091007081050807100040e86401c03031201007100000740000e4500302995824000341c4030030220303a104502002d01e1001c038000ca41c00101820503101c508520ba80c0701c07e010303070f40544001007400002c002c40c5030100001c2c003c0d919100307180c011f0f5941c1502c01d44150300e40442c10282d5a92012440b000305000c3c1d81480c01444003582101a00101252034025650004006e1600403a01c4101900c07400c5810801d07010081641900c0528600a0103034000504203414050b031101122055031094221100070001a6448044414801e160340d1a0038004c41c1d0f00207280b41c0c5155903020040c2c6502010f8240c503001d5654001100c5040c62860024081040c021031200000124613611640d80344114 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 711447185 1250 711445935 711445957
    0x6030b0a12030f081009051f082407050c0a05061029030702010b0607030801030506010909020306041527110402070510091104020d0507030e010209010906120b0330 72
    0x40f10403002d5003401100d00b143c101c440c075800a108240d88079965021540283c070501001c2d40240b20b0303400d2031855080714201504500300a01000002080c414007100440711040c19024080000074003214003c8054400d6000d42001303130780c0320240ca031a145d85c40350b004641600401030390034800308803001d4510519000c0c2002400c0601004081142c0200582005205501315922007031100d0a54480304d020700070b102d00c2601e403800c803541145061400c0c00416000000c00030f140070141ca01603500082c035250403540021801000c2c1404601e15406441a25819413204003c8034614041048618200304a140144904412440e40c1d504100507031040300405883d176400142c982c10302414685c85201007505c41d001c1e030083c165421011038260782040c5802c11700e0032380c0c03542048002505405084464400400210301d40685100040c140081c00d002e10b000b000700e038100300100d05011b03034096584814010111080d010456aa0701e141242c029891460308110401d01c03042c0030051000d4900d46190 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 711448435 1250 711447185 711447197
    0xb06030729090301060f06020307060b061e090d0204110c060c0a0206071107030c090212060a15050a170109062111101806031b0806030304051c0c06030b0a1203 70
    0x2400c1034048190004102c560b4103558071072000940002c00365840f0014901900a5501c501c1c90307003404000c841030348071250302810b4200b1604544079540d401c1808140c3c19040c6054907514001c011403521051054000d40051501d5152000003110380090320344090382d00e0031030344555902040003200e802000a00b50250f44038801141c151401801030201c000101030442c1c10b042e1380d98507100c1140302c00d5845291120390000e190b07a002d42481c0009a4810b40980d0811655440d011241015240b40d8201170108840840e0381d44046204402c510441100000c0107480e55840d011117200414003885800e501840c42c42d058a82e00400c5050308944940040d0164001040c0e03800b4040041080e501041c01c00102d88010400105c080e004040a850325a800041c82e80c0401183d00220300d07d10030f08014440040308000c901c0d070740042250300341d5030141d9070036071845103e0601c40d00301c40101c000140311808010340840e46542c07640c0911001d100481f03004816941c1c61160b03e25a100030300b0054005a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 711449685 1250 711448435 711448499
    0x10e0609030c19081e1c09060c0c2303040b0711181e0703020c0a03020109050607020a0c1401020703050a0609060515030309010e0f040c020f011a030601031202010b0d0b060307 77
    0x190751301c45c691802d0200a495162128200c403c11034684074400c2c18100c0ca6480c4040c00500c0b134948904081c03c803e5040c400440a00382d01c4800d0f1200040d1407a808c07500b04000c0149100c041401610010711060602903100d0001d460494407858140900750b01a5005083d0742c1c14115821103c54020a41012200d000c40340a04040481390401050382080c180c08000500c640c2808006125100703019500014205000d1700d0400d00341200507000b80d0840d80310340084000f0944415010085504d0b21048200318410f050060b410000c0380d602c050403900540c00c0417814010706400c40c2031494840e0100300400daa407400e41841e4400300d0b102842e0543c0c400c1c0140445940642034030012128000d068689064040d0001810385075203000010068212807010f02c4841000d001e010301f040408040742c06640c45420200c1e80d500014030002c0c0c41a900c181c03114008500030342c007006052030042c10031050b0015908100243c520241e1f200340c00782c0715a41b07000441110584c01403a01d06105030003c1c6582d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 711450935 1250 711449685 711449707
    0x905100c030e0927010b181506030702030a0221040b130e01091e0b1c06090501060f151106071d0a0824040506040f05010e0609030c1908 60
    0x21000d90440611204070082c03252039542e81c401a110307450265940c101d0340c54820001c00f44a0800d608686103a06085881006941b00c5050490303034007028145590940c2c590030706c3c1d00902a00b0b01015084000041070120140d4040001c00d802d580503001c880321002d44a90201c0444895003210540000a000a0000d060603400911044082c1c01030000004c0d15481c401c0781701a0300383c3c0f0806034159200444515013403400c1c41030140c9115900c04002210303030900410001d0744e40522408081003001c00382000c0209507841010451f81040c020860140c0380d11618680301b0b441d01a40034001c802e0114054814402d81ba210341e0103680d90003508440c1c0b190381c03055485089000c880316210a500080f022283c8990300520014940000100041c0d040081d00c0f0800d417003540140300c4111503c0c0300708404a1800142960080e512108021810055003070036801400c900290450b64020703902031100b1810000040c00050303058009964040b912030283ca1020029a10005c10101003800159012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 711452185 1250 711450935 711450947
    0x1704050117090a050106090510120b130831081f050c04030b04060f180503070f1505090a0210020c010815010908070e0f13020d0b060102070810091101090510 69
    0x920300000c581c2481001e5a0313180c255041d58105040c51541c1d00c003040b480404100002004104403c200342e08611540c81d0103442c0000107086070198143c045130799007000b900108a41001420f0031550101003c0b210003251318a40840b044400c0520b0428041030041011842401e50098220010340c0c021400d003c807006800014901c2d40044070a00000000c00d40c0c85904502c0f9511910700002c20445050300c000848041c1540c02c9414a40d0850040002d100080bc4458150300300f40031251036000c601e007210500c00320101500c800ca0518060202619000602c0007843c4d01c201c400461050102100320780d1040842d54980c0043e03402d5002c91920702015074818030116040c50000c1c6280e40312405546400314580c0304020620340103041010700703a0b402810a4014060b2882c446849499400050740c800305000b001c2c10212403400403e8503603000300500b00c024640b0300155410302010f6501e24000b400401415500503c203100d540c9800d6125441d001c043e920b0040c208030500005900c11909 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 711453435 1250 711452185 711452191
    0xa051e04121110060819030c1e1415071112070611030907080d02030316030e0106180c02010b030c281a0405100305040c05220212041704050117 63
    0x9000c281e103418a190803040c4a91030f20081514000318032940f4203c0c0103464040c20010032811380c4000001407002aa00c502130101c8650080c012a40c22601d130355208440e2800700d00d00510702200c95200911441000c0b070300d00350a0320405249820365a65802c1691080c048a16540c070a40040e107102201c0c0300343c0c3c0c1c0a8060719005e11400149441d5030702c60702903698020781d43d00783c0640c05446c0c10490b000d001c00650f0010011072002c2c500710705000d24942e1219407400741c5a0107060b01c90a01640d0071109501c10002080040722500024001c072690400612600010400550030040510150309001450282007079001c0c1002d54011364401070118030703030b50740c80b808401480911000500e009a540c051000000c12032210f540c1c0314500f00400044c0d0145035815818542480c1c1000b002c124100001c00c00ca54050312500000040003000100c1d0510000340d210016102080105c291344042400c00d1046204a401c88ac1e041c10301e84254007207001c0c6125190000c2c804107102000d40d0a40c81425030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 711454685 1250 711453435 711453437
    0x30601030e0102160506060307120b0a02091201060b0406110a0f0f140d1e02060f0115210905010b010212090112090503190e01030606020c06070302240a051e0412 71
    0x4241541041200e581d42c04c2c192055485034440030a2144500d0f05000c680f0080010322015a03041000b0380c0d40c500001d400506605082c0d070b000c6480c400a0303c4041182480504440003003100b1a00d542517003825400c44e00405000902a03103410200e80000100e00e00c0d43c0c3c0c1c1000001081003410b69031303241040c0f40103804881030034000707800d001240420485c84960820b503031264031904030000408850910085885001c5500036020300040608041c016030541d488511a8080390450b0801500d01a84906200366030394207010001500050326172280b906107104400030701c8030001c000f0049a5840340802180e40904082115243c00d40c01220000c801d807401c52004503900f04651100c0f810764010443c2d401901803441850001340f07602c40c1d0305000c1c00d242400c04210240c01c102c0001e5442d0543c16010303000d0740300014158181402000080422640c0182d42c150f41000314088801d5800c0540301e0041c0c0c0b40c00c0001007840c0701d00102c00000184035019420011381c0c1e860b1582129440d0b100d21a070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 711455935 1250 711454685 711454687
    0x18150902070c051f0806010507020907081f060305010807090219030b0f0a03030203030f060916081909050a0b07030b1503041113020403020319030503010e0a0e07030605070e0411030601030e0102 85
    0x405031244a11302000606030020025074028164010b8039089000346024108081040014016500c031001560480ca080c6082080d59442030031a54602000241010300b0f1404100001400d56064108034103858441041d121107070341d900b440c10240d005440303074101c080081804100c0c200f4400e0b4800042c0140007040d0b0644c0d02e2030200400d0f60054039400c181c006030800810003840003050218036402984c141c82084943c58035503000d00e040000b00074440100032500b00401c040c0e441c44d0740314014070444050104180c1450349801562200442c1044404c085820b00044800f402031080c80c059040c041d04031529041d03020a00b4003076a000800441e24000d40c605108030381e03100d803001c801c00c1642c1e0400040c0d4031070840c0101490b114952803004111299014100b0000c0d60060071350341154111441180c00342c6030389100728058441802200d21500c1280742c000140245504042c1c044e060b1030300c4413620202408107000580d40c80941c41010b00780f04101255440d48294002042001804001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 711457185 1250 711455935 711455939
    0x901060f0f051201030c0e0906010501120e070f080303010314060f060f0d06091407050f031213030f030903030e0f0a14010203070b041b0602030a120504030c05031318150902070c 78
    0x3041c10f250080c0c00070398240410503000d0103003140f40c03c046a00441810000c058541c5050300003848000c4500005480c03d031200d0300224030003000c101020180c00650000d411440c1c992002551b00d030000d200603111540c000d04045503160000ca4004d0180e400708280c0862035482c0d606111400e00c9407036200e60020860180720300424418403d80b51074500c911540d00668098003680f03172600e04103410084c401d412004807465036581c00a0000c86a2940203003841e00c03502c2c21003021038104003591015241c49020842c406c101a4064081f9090348d1003038845c0d250300c03429a0b0612462107069800d081d000003444c0f006000050400c210048508030500c1102d1415001c0da80c2c01005c8017099034112a07003034a441150544090340e55424014010a02c0110708240700100010448034441491340c08507565034021809062155841e041d17550707040000c07241d0b00c41e1100400c03640700c3e849106028100d0700c05d8040c5440581a80200c09045d8005a0070b80359582c240103011000394000303a011101e60900c0000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 711458435 1250 711457185 711457207
    0x6010504120b13060c0c030e1c0204200706150614030a0e19030201060504050f0408030426030c0a03050708010605120c1b0604030905040221070e09090c0f0901060f0f05 74
    0x517074803100c1c0f02562821100052441c0c046e04941520b0b64403031281c3d030510b100241031959248405400707501100e0224074000c162000c528443c01c0362410411000c0001111414410760741c001c4c19501d00380340740d003040b840d41c2e4220440d644200040d40900d10340d410004600242e0035a01302110041070082a02d6540c45148110a44003507205004c401607519000100034a107805e104065000b14040f076100c2e51031405680e11342d140d00c8014001003c1c2040f00911000013889104500751a40705c0526059682c01c0c45084000c00da006003c1d1000082e04010004680a200e0000c1c14121010340d101e0ba42081f01c840c0000e039a24800904080c800b04d028050140c40280c913444408074030400307201034001350905043c0142003003e25040580180d004000000c109a103403078010702256801f0f000c5030781503112a40f044078038050039114207a0200a00080c0000f2034800f14890520800464004c6482d032148414454102c9091040314003140d9008a41c03c009030040c64008078040c00c61600520345590340c81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 711459685 1250 711458435 711458441
    0x30f020315100e0c0306010c1b050303030f01090e0a051207060b091008060a09020a0302010c02030309181501021506010e0a09060305010b1e0d030e0d02090a0207030806010504120b1306 81
    0x54184010045281e00f000002904282e081c1c11089010310f0600e140391600003e01000481e510080c41460030901c03842881c41c407200c0c10405040000e069a64174100004000312040c404e0261003076003440c1c0000e440c50000002049030392180c0c004040c2172100b101e20040e1950f600030030001c0d030313842e5202c900500c45644c07000d002a12800b01c01d10001e54042c1026407080c038083e001002c5005952408001d07901594850180d02c0031a41c1c24a0181e0b05e03d0814400b1a046024079100103804c50480420900e48165401c0304a00c210018914102c882000782d004a07501c0c0e440915500110b040341010076a50f5220303c044181200d005000d0203c910b6944c02e4031404c9480560055449943d00d8040a41500e07180e41c04a2100410407280003c0c01d683d030000071520014a40010281f21000004400780c0d203541d41c5a60485030003c000d19618545000080040d41c000902100003501c0100021413640c000c20640381a550300188406540400c2e03a01e03118850000f518030740c892003080b08690000f51f0540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 711460935 1250 711459685 711459691
    0xf070315081912090e19110711040f110702240c010905010b0d02030d030e012903070e09060f040f060e0d090905071416020d260a0801030f020315 64
    0xc82400a0039000303040c0701000044503c8071004004107030400300482d090204689410010032131009013148064000744c002043c250001100d400030201d04c0500340030003000804080c1c0c805517018001c025180c0c08c004103c501d25408407144200511503a0003604240405803000c8500c1c4c41c9481100b820200c0342c1400d504442c58440302c0761744440d0b548040100030f028502c06c1c1d00c800da846002203d07a03070340002e459804a000301c03803c1550303a41507070380510400d4100c2c44d0038103a0a0f01c0141404c00402c802c00c90300c921080510b00074441d0007400210890b46e2142944140d20340d0700901120349451a52240e40807024005403802800484200040748580c480c10400300c0c0e00c01d005107001089608050040c035190f50101c10054548010859032541005090300507040441d00300307598240000f4041002400142d020750000f00012082003044140c8400300c06459003410715440795078801050180921520030b00c0e00001d4551030040001816400b11002801c0c4010300b92a03164003103184d1604501412 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 711462185 1250 711460935 711460963
    0x1062102190e1b0403240603080412050642040519050a1a010c020102071a04060801080706051614010f0b1302090d240204240302030f07031508 63
    0x22003071101d070403c03050204818010310040740e030405140d51030307060300c01104214070140c035032610221541d000c0d1568400b10103594055241500d490320f6022854040c44105002c0346c444c4180300c0402e294135404013491b5003880c280c000b808004140d14100828401c0316820249040c210319541c4840e5940314004c0c40d01c1408549611185106000c074554180c8001a003c503501c1460710301c466901c1446820b02e01210754081c00c2a0f075142e0100d01c0101d06d0b110817503100350854100c0410020415a1402c001d000321801030341ca800c0d4a9807240e215a40304d21080c0300308000300300c0800c288441100107407003040c1154002c44841c003207a01c45407041c600b9681d076000d600782c440d50380d0986041140b8100500145801d0740321400c5042c61240c801080040300804c60280602c00450030310400ea030a140800004041d4560f000d544480e82d070710300c00d071540d0341c101343d00024a0101180c0e070048070b1203482541e03c03603d00c020441f21303103407102c01d0300380d000344032606002d10281c142c0703100428241d808200080c5840c080c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 711463435 1250 711462185 711462209
    0x160302100f02090114030606040b031501021c020304350109030f09050a09050a021314090a0c05430c0515070305090604030209040809030105090106210219 68
    0x6514a004444902a41c840c03220301c14850180f01d40d0780880c007185060b200c86003180d6a61140e500244c0c1a0180ba80f00100b000000010042c00400d00e581200300d415003a02101c010b41031304044c005000034400c0c0c0c02c000592041c00100071980324144032004007031007441041c000c2c000420300503190b180f03080341d00384441c2e46070504901015802011202c80e03001e945404072034141042e001a0310040c80b8881c14900307507290750200b840c002090741203842c0102d00d00b40ea042076940d150340081c0359480d0031141d0b9100c0d120120000e041411180112203e030025543c409107460540340c1c16100710958035004c01044130003a82c05105001c460440c40d55010f20054000e404c1c061103250000c10010a0781060b4000c40d180f00100daa12000300007641c034400d40c0350502c0c544075050000852014011a80041d6000b1642014002032000342c4d0024404020142c0083c0101c0c0d490303500130303420f8542030f11940403100f489079581180f48940b42c0341c2900c960b1009103ca4800270188411411240741b54001000d0142 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 711464685 1250 711463435 711463453
    0xb0103032003031603090c0924060c080a081b220f03030816030209060f040e060f1c080c010f0605100c0503030c0906070609030323010e1803160302 65
    0x250104080071000301d0306005510754503001980d04003580110003501c042c5500c0c2d50f00300040103010f4074500060014800e04000e07031840c42450300c0802491400c07079680c0548000010654610491b00654840e40101141e86004900302007298114401098051040000180b55220200c800000c00a02e0006442c00507807020201c200340c020304c0c055011204800b442c0004000081d005409598064990202d81c0e0081c0230708036054029110b8568180d52141d00000d2110303110840c4c6015209a030312a4924500b01c8d6110010320240760610720946a20140036010a02a107a072401c2000340c030340c0b10b03070007050420840ca4001401c7d00c0e0b03411050550076407640410700c00b03410030800c10f14044003203103081c1c1401040c41d11680c1d120311010f403120b401d00c400080e4503c1c2136120340f0119000e03a83e21a034100200b002c0c0e0305000340104072502e6000806189403011051a0420900c4a8142d40c4003128110464859010b400348440c10030115a01724003051007241140c604d005146401d16000e50090303c0c08003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 711465935 1250 711464685 711464717
    0x20a021002070617041214190525240f051618030b0f0402210c0a0b1e030703090b09100c0f08130c080304120c0515030f060d0b010303 59
    0x1540034130b485900ba0440310304100105500d15414401c8100c035060064410840000605081c856101d4920f1604003001c3c030520803d82c8100103009000100d401074840e50000c0c0101101c00a24000190640180c110300320b80042c88840c1d40303081e03080c40b0100000d2410b039074520401500e00496481480c0946070601402c143c1c1c0100c0b03440d03544624205021500c03810b50759030031400b10016010310340314100b55002800319140c01e140d480c60060030310030340c801051040030010b07910002104401c3c0030703618840c400660703415403406480050b0301041c0c1a00d20110030031012202900300814560406031294907500101314000348441c040c01c414005003a00898071034a04040d11070079442401017060b840c0141a0095119104980007180c81808115454043c07c200000c0041c640013454103010000300003d16410703600c44420858070030b18079103003011fa80e0400c20015044010040000c032004200040300300c0ea440c03140c40c0e0702200042403080b40c081c8a4841c003584900c2600214040f49a8070180d501e07207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 711467185 1250 711465935 711465947
    0x8070203010e0d0c060507180e0601200705011b0c0b070515040f0201081b0d091b06230d0507030207020f030109080d0905100c0201060302010801090515060307020a0210020706 77
    0x51060030006041c0d034000741c03500404c1094074440140500d0b640350b0114400a21481c954803041c214101c0c903801d003507111038002034002c0040e03415901144005585404103841039242000380c08140c030181c0795851500c0c0c015205030150282c0000d9190460041400040002481da4081c2108101454550219181c030350b25080c1410055401044e094040000003451140d1108055a0a02c1c08102c5910741d086000854801110740d0322500e01c01144d1082c10035010741c8107442d002d00030004809050040c014090411055020b804000b8824171001e8100c0d50301c1000c001d41c4030840d280324514000458080008a90007500d400d0b0004e47c00090343c50940c5040a0b691219800407002000003401e666a82c40c941e11038481440030b07690f00ca1030303c2818414107014034608100105801d1000200852000f0b0081402c0d00040b40401e198200104107030884e0311820303200350090042011000165010018036801c01000032007107100303000b140c4006848146c5032401304000c0790000c08516040204c042d00e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 711468435 1250 711467185 711467201
    0x9150909020d090b13020f040902061306081504140f09161d061e090a09050105040b0105010807020601080a08090d02030d17060301021602040c030b031203041e0f030f0306050d0807020301 82
    0x2440300c0385959030003690ba1f07001c0030418024101c0e40007580004c076201003660b90007400d5a24484030000303200004e440f500300c0802171081f40010245254000c00740c042000f1540e0800c1d5a50300880305000080f094070004c107540b50440303e03410480f42c520f415a050b104102d0401d810809030074640509241250540b840015041f00c4111048a22221020980040041c071310410920810002003c03030301000660307000c4c400780c1e50410002d0184e4035060401d45030605007032248a00040300340f0005541180302059a03416294190301600c85c00f102625410b803c0d80088440e0390340f2881040728400103907803c101c6982c0e0b0300403d0b00c03201e00441c1c0440b044c8240400040c8018000d1b40100034414103039180704460b0007a00e80c110ba0011f211001c03198100c000f40f50101c4069098459002011200b6540034091403142d07100b034100f1201c03141c40401d03c0d1507002540800500a81100501e040000e001d2010302408100302d01c0c0026003daa01c400242c940c034244801642ca441000500c10b007036080038021512 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 711469685 1250 711468435 711468451
    0x7050d0306050f10020606041515021f02070c0b09040f14370e0a0804030f110a050a050d061506090807140f130608030d05090d020c0109150909020d090b 67
    0x2c145041380c1d10203901c07041300070007041c441c6a072440044003c00c80da9108401402510f050f6001600c41d6150296444040c81c00301c001c00d42c1e81c1030030103100a905000300c44419a0202c5100c0c0075a20f0031440e203141c0c0c2c200540c0b01e6441034035001c928420019611903018600c4401c01d88594038201a000c44000d01383c42442c0c802141035070b52100d00050604031400d15100220702c8000380680f00146080e06000c02c41d000100000300000e1b0000600c000f28088081e2240100301c1650b40480b060100145110b4503c1003982080c12003004209034a004518001c81c18000c03031002c20310000c0840d843c0c918122541140c000729440d81c4052203100020000031001e00000700021030341101c8000040c0e100e1408070400c1d4421641034100e3745400d001b0303401100080c801102241c1d1a01c1c41c500164002c0c0ca403c1f100d00b0202d00c42e40c480c404619100260f9900311041c1a140d0801c29030130500004100d04030428040103110300700200045c43c00461008140628120f0000100300980d441c0c41580040080d291103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 711470935 1250 711469685 711469699
    0x1b0b0f1602120a0e040209040903020a17030613050a140907180e1002071703012301052b270311160e1b030f010905090a08070605070507050d0306050f 66
    0x1d002890b80b41141d8480505050401a4003014000280a40f0070149215041824900003108040c1c00080d0050381c1886804040441040003020312154002103a00c19404802044d0789c600c641c856034840d82c3c000d400c8100c0895900445101110550030a07074055a080d0321000701000000d80c201030400ca4440d0003403042c080507030300b071002c0c5070303034132100c2180e08191540081c46808004030002c1100c2d058030010b8500e0380320f60303458404242103c55461400078030b418820121540f580304000b09d41c038a414003180101d08a071100c0020011000b81a000c0d42d40130340d80d1001148000e0790404101c071140b09801189030450303003807030014040164a00a80869400308a034032929242800c0c86400b41c1d548101d00141a541e04510041161131614010408001c00070900004040d01c05609040e40c510324424044c0da00d0740000075580f4001058060a103910510090340068240d0300000d07000009031500380d081c61034030f4956904041740440501c012070fa42d20420441403d01e1040d507030603000100c1e415 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 711472185 1250 711470935 711470953
    0x40c0203040e1602010e0f0c1801210c05031b04060e04081204080d0e1e0c130902030c03030f04060905180106120905030a030606090e010305030a1b0b0f1602 69
    0x40102c0019000d00e88440400b800c00d981c10780f0035404400c1b040020300854031482c0c0a04001c5889400038040207000c1d50705007894012032030040c0c0b2154100c0300e02c000c11082c0d41c2c08d0643d1481000d070201c40102c4074100c0045000a0541d01000403012203407800d00002120b4154200f0002111040d0b0702168100c4102e00c10040030a681c1000d0301e402c0942c80c094200740c1d81d942e14111030984a04064601b50b14032b0044807010350180014442154010407002031400700f1805030072a9076140751441e00b40e02841da00d05601540707100c0d8000d10491751000e0102d6065107180300019055400c9811100700c0454041001c01c000d903480702500c00104010707164014500aa10b02c0c222410005002e00b40070b00803201002465900580d00591f03a82e5084402e9a03114800c5507001000340040380714103000250499008144044102c80c194120ba901000861410500c620240c5a92004100d015013030007440741c1480c0854100300d4654460000b26504005c0c500e0003124420b4007104c110204011540a040b003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 711473435 1250 711472185 711472199
    0xe06030a08040e040501020705070e04050114091222141003060b030a1817130824130602040b130608060f0427200d08190c1a06040c020304 61
    0x200c80c180c1c0d1169200341e00603504ca042660180c400c0c800020443c1c85240340001d03202500315400c5004921400092100506400400c981c20100341c0c1c544030150065110707600080400001031202c00d500e054115460340a07400e061031803940310f50148103050440c5508185901e4962600d1040341090b050800c0028108000403210303010040681078205c3e5030f03081c1e140c540d291000402030350741e5004011800b00c078019405545150081c02c0c240404040c1c17600301007262000864a599200f61440011609200c92a404200850702070320b500c640a8401c4540c0e800300c0c075140001d101408044000c140e0350080070000d40140e0700168000c00800030318005001440e40c5241800742242800c80d0301003448028034a0180300304800c400f624844081d03460041c0104200c0030401070800c64600804180011030b003007409100000f016009040c00c00400c06121450710040307605800d00070503d8a20013043c920b03a26244510390428080c104450108204500c41c030b0503004000250301c0c503202542c00d051620007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 711474685 1250 711473435 711473437
    0x3c010f0e06040b130807080d1a0d020d061a030d02030a0e010503060d110619030f18030c03050d02270a050103020910080402030f0115060e220b0d0803100e06030a08 72
    0x41c01800f07013041d4030b240091000800036a81d900c0d8004200d1640c41503500d00309002464a050300c4000d41000301d02001c86468104003900905801070b00e5070078550301300e0723070b403c001826460346a15020050906404190703e040003080c070a0141f0790010350380d40301044009850208820341b01810010204101300c225107885408008550f803040c0d110310071888903000907906014a1a200043d2070040c00035000651b4140c11800ba04e48000d401003140702504000c1d60500584010003402140003074078441d001030b100308000c00b0f0300045400012b080c5401044081030401000286410311485481910b502c1e140044401c80280001d003002c40c50301810501250a020050064205101108000405544084c07000c21001500d030002000142c1105603241502165401100001000203c641425042c580f450400b0180b10117503c24080d4003084a0354080d004400d4041e070044541c84c142000114071340003441c080c01d21959410845802e0446050700148010030251183d8408606540030500c080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 711475935 1250 711474685 711474691
    0x306011202070203070801050a0b0a080105010e0420030703150f05010f0b09040213030f0c0801050f24030601030308061c20061c02072001023c010f0e06040b 69
    0x3400141e100d003124000030313003000400d62010105508120801c0f075054902c2e40045407140040340c40c40083e58940c429070b0700302d441c240175140c0591003880105011170340381c03039a01d207141850500c134960140720039011074100111075004a03080118900412001c010324004da010007600044100120b6142150120b0425031600c40c00900b11400907501515490321340449045c51800c61058004555030f02e072120011142c10410b82e09507510b480701003003c1c00e06000e40d50080107103441000326600e80c5034601400602d41480321459092000b16420b190301c050041c1c60007980a41c0b5001054600034091061010508d0138080e240000d000c46400000e00101c9500d801c9a108a580d41880743c070031010801030300c200740540c4000d00481c14100c0c0c01203510b40092880d103110703c92015030801c0c4590381d11200ca038811401409a000401800b0340f14040780743c0c00daa11281440524908540c107885c02c001208000c03500046d40e5103502200e10b01d9281c03801854000e40a2600070521460962202c000c400406 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 711477185 1250 711475935 711475967
    0x610020d121109041e0e1b090a0912020706020d02030f0403061d070b03010602010c050405030a0f061b080f06060705030d0209150c061905010503071403071e0801050a02030601 77
    0x5901140d28641c0e502d010344990b0103020300100007060030490b02240001c205040a40090700f8030740004c40b29600400c00194900b030010403640614406010440d0601004044922199840315640003003070848003c2c291261803034015200407803c0c008000d080411a80b02c150555104116445203420310000711030032079801880025846c0310140c1900c03118018402400141d22034540c01046207081c2d0070045040714031980003080b4040700721500340e540e8040d5110741ca5164000d008850701085104e03030b00344107481c410b640004240f2600a00000070300041c000103000100301d00c080000621010508541081044800c0c0d420000c10741d0720302c0c1d52480f45070745820042e9000704404080c0c0c0c07510f5400c0d03452011144c1c3d0300c98942000303201840e0f40380b0088800d140c40040810303010307060340c076a44216816100090058101e607800e200b00d0400031004500c10a4051096950005020094002c00311406100c00407086d0001d203000e2132242500c1000d455410868410000e009880c5e0f040010a00780c440b41d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 711478435 1250 711477185 711477191
    0xc060504080d120603020a231c02120c04020c070e090102070c21120e030c04200702060c0607020d0809060601020607080603250f0801020310060e0a1703030610020d12 73
    0xc3c907079a1801805055100a400803141400481c00d44061040480c24040e10958080300000c03610400640e50424400049090305000f6400058182000c1c0d01d040000994200c07011901c2c10340118040360301c05000c03290a500019414011a0b000c0e902650b0000e103404020360400d11562910071944410380f2445100d484010b4040740846144c0b84c6500801c0c0d004010110700000030360015001443c032540c801d11030300070b824102c11940380a11a240d20741584a50750003140d250f03280e404071560b1084400760f81c006000e0013554160301c81000010320441340f6501402100c80b04032000350020343d0280402055401c4203007003000590b800580582c0c40551841c00040d144c80d076502290901812044608448a07400b00441b0059424110103042760888121074003501c1d50740300310508134001900d06007403500158038100718051054400303004004005099100d401c2e52140071004003030300003000e060a5000401001041d03e40003014407420030060024104100d01c1540041ca1038442c80d82e01007545130707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 711479685 1250 711478435 711478457
    0x80a052e05030708070e1f0306050f2d04031808010f14010b03090303060f010e090703151505090415050607060504060b06120601030f1b0c050105100b0307050a1b08070c060504080d 79
    0x47e0400170000071038214004000900f0440b8810340521070840307503031189000b000003208080311103000760f246544070000d2000302a19207a030221442c0c40c40e041c0d0f011000b0088000032408032001e01c0b50100340c10b81400b000518078080400340b1900b240c145d0000d11200002d1041014141000c412030340c2c800e40c100c41003031100e101d100045c3d0b00400e10380082504400c40000b001200c85d090790080c41c0c85040805403030307000d50b621010004911040002080000e13001d1200002d1424039070440600025004080c0e40b100e6102c202196068104800039100035484070280814000244030302c5031041e8095803e01e1030902003004401403030802802590405650315000700c401131480c4c0c8012444056aa2000c540c084003040040a15400d0301e0244e819500e0080841d48049407024142c04035003030300740c620b8115981c11000f40d03150f800a100703000900192506001d0041091280302d0702052289500d0342c0c540d03100b410400c19a12950b001a018810208802d21046000044c58202c0058a1603d00d1000c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 711480935 1250 711479685 711479731
    0x50a0c0201050d050103120e0f030c01030b060d0207030210060b180906010905040c020c0f0402030906010b13030501060b0406030b0409260405120f060a0c080a052e05030708070e 78
    0x4403903034103c840d685242c1030001c801c002d074080c1401c0044246598401d4051564410000760152001517580d140c0c1c0300d56040d55280d4026003001c05169030043c201d506014031840030740141e92003004100c0043e0820700400084107110b218170000751907020307141410101c540d20500046090002da083c414102000042d003140e128038942006003078050824060a403032003002a5540b818012010300c546003071031008a80303003014803c1d00d1045108000171300d20350b4a400103002d02030748407500714040407840a9010000c59003d001c0c0100034800a603805544903d000e0006045440704072030140700d103081c4407102c0c0107c2d100500618030b90409050928041da101000703d0440d100300e90000e9000624801d074240740b0600491048800040c40382035403c6691022940011900301e80e4641004c1580b03040452207172403041d400141e02180b1090003030303c0c040740042041c82c801e90340300c0c400784000c900d140b06101d1814184036040051100310000d048181c03c081d041042400002e2a001031204c0d03c1c04400340c20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 711482185 1250 711480935 711480937
    0x5030d1b2d0c05040c1701090c05070c0e07080705181309060f02040905061f080a0b0d0c05041b080115020a0b0406050f060d08070308250801031202070501050a0c020105 74
    0x5800c00000056140741c2a1502d00b885520078811648150302d03120805480d240140740980540b41340e44100e040c66820080100f000303050420f20103003000f00c02d010310400034403000c403800e000c3c0142c414801d004c0c1c507018000a082c07050003416902045410b00c44452002125001d108203810200d8a2107120100700014100078040032030040c04480c2000413840c2583c92580c010006c1d00c080442c28001541c4045c144000b48808111038040003007680c140c40c0ca00c92007060740540010700c5000228100412300b00003000e00c40340640c2a00c1080c14410104003500c2d043c40340058507038560305546d01a81a0507006415a0814801c4082c00c022007000c0d90300040c828080d0858070740e400035451201341080e090810080908a50703869030703850800e010030001e140118540c2511075101054614000707040d41e0840d40440041c00d0400300e005640010200c02d00b0f9029100c050390060b40c0d40c28540e61540c00c04081c55401c07191b4840c01c0d50420402805141d030703c201250001c85060411026014081c4012070301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 711483435 1250 711482185 711482243
    0x15100f022a10020c010f030b010509060c01050f1f050f032506110c060901180f060309020a0e010515030403051c0c110114130501060305061005030d1b 66
    0x440d528211641066081c49400c01568070a50350101540e0100c20142d80c4d500d05072130960f011814125620324201d201c0d400100700200d040c9881400d0070044000f180f4180c00a07110766aa03a5128402c06c44114903802003240d001c080d00c03000c0440818156207280e06ea40710780c050b441c015841004c200c4c80390b80701004403409506035817281241890041d00418405501c5000700c1002903000243c104600740001207134000490014140752501c01c8910065030625424110b00ca48405a4040080e40b00b40c0c0080c035100a0141d40c42c04070b5401c1c168030420800701c80c1e0780c00400c0701402c4c0c01d00622098032031080c0f45081c5140900460b640340c8880c00d0541e02c6004856030b20640e20898080444000d01d55002548c02d101c0300e48039030840c0090204042d003a201100242084103002e203002a5100c51250f40880c0032a00440001906c40c0d129100c50f420040110703803021028150084c1001203040406c031140000d049442d0180c603036980382104041440c070300c003405072074a0220750300740c91300c40c1d20b100940407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 711484685 1250 711483435 711483463
    0x60b1801050d050f03070b041b06050406080601020c121023040201030b03160308070b0109021602060d15030803010e10120615080a030807080a0e15091203010e01080615100f02 77
    0x91190750f039240c084a86c00003144e040362704e04803400340040c40340c4d08909004181d6607151a458123060901c40304849a120080c4124114855140da0600300d0319819040c141c0ca0b450b84c00502501000030200c034050b5105095200901d00e90034020411b040004608150041d41c2480e0110744c2410324000685407000354840b0385081e003543c200000400c00c1140041c0085407041003000140d80ea02c45a01d8124055001341491407060b521841006260000040558071035806000642c106003000342c4919145075001110903040010040c8500c03005044403e501c43c0790036800484c0a030609204d8102e1001e45640105119250b001400c10880f4001c180b0010b403040ea41112041049410020703c506000c0d52568041b030b9598010481035140e0b4052aa10041b411009100c540c41908080c40640710041030000540a6038941e548045006c5c40118000c01c0c00c0d00350000d040d41009401d17824000302a00014080d031000341d103128151104e0107494004090b0b41040101c99520f40c10903410600103950540c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 711485935 1250 711484685 711484687
    0xf0708030702060405010f050f071110151706040f0f020a09022118031e09060324041e020a020106090f060305060c0f04170a0519060b1801050d050f03 66
    0x814607030b900185451041c0d0060009000139401501814225041a29440f800b00845c00018609900406100c110114284c1c22202040000c1d0840b900f255904401c84002102034001040f020403100104003540000e0405420b40f8100f903035a070300c4051402400100702c2c428440c050346c103541e18901c46900404c6014001d6607030320b01c070707143c1e440020900c0c002c3d003082c0e0a40075010409030510360074100501c0701c003000114a001485c0d212450044c0f4454981c00f9440300030040e000c403585460024602510341141868110440806900044106903001c00d0085103171030844e00f02500401d0001000d0040740c0030042e0b6920120b402280500140d401c690f407043d040c4102c107910542507501000c212130040060368542e03107504150203520700c1030340101d288050003404180050040f450740c0d00a103a1000048854846003075407480c0c203204191401da50140c4010301d4040501015024a070310b00841118041d8800c0b680350b5084c0342c0e006041c003c0c2c0e0f0103050452240306c1084410000d0301800f00040b0112 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 711487185 1250 711485935 711485941
    0x7030207051527030c0c0d11090a0c031a06040612020d1d06070f08070f0201090507030b060310021c0b0109031b0e0718030305090a030c03060c02010b01080f040215091e012c060f070803 81
    0x1003030150bc6160740c0700001030300d0325107108029000e20310b5140400100a03e45854680b82c04000c40c0c00c0c6400c88030200c19150300700305586034a0f00e00e00c01c0d0180d0700e42c40015104801400c00d6002d0425800400450a1086a002405c19030398481d0840e640300003581403050b14102e42c2c20040307004003030310f01008151b1700c100c40300841400300190fa0325110302c80840442b90030850480051080e40a400941d4102c0288440300d40c1c1a40310725044861001018501021800d541741c40c1e92000c2d100345e06403054440320110301031000d01220500c00c0e600150740c3c240100f0600c1038a081e40f0b4207019510014007040b60110340503a0640d0390114040c001c5410010300d0f89a2a03c3e0308140000307141d504040b40c003543c80c244107080300f5401200003c0c070a61181c0140340381540c580d000d104c2c080030424000501104100680a074640d02c1a1070090b0b0840326507864850510440000741181161005212018614110a022448120382d0302400710405481142d101d0300044040c001074050504000d011110110030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 711488435 1250 711487185 711487201
    0x30709150e0a1710050c0c060103030c12030612060f18110a0e0105090f091c0c030828150302150c01200307030207051527030c0c0d1109 60
    0x8410715920200c07100808030750364941d03111609a0840d24100345401544488400400c29031149a00c0011a840c00746081d00502c10303142404000d82084001c590011004000d0141c0c2c200c2c030450b059001e040800116040c0300d0039803441d080402c07008008a03261a0481031840703880c0c001e01b00031019685005502c202d149040034184040001d454000d410403440002e04900c10340c903842c102d500261102c000e9484801000a035188020911038103885a44101075010501c1c443c1c1074008052952030440000d89850018081c1030040c0c0038082c0300e00358846a5103c14500081c004002c180e05400040c1d406174801030301107003842540f001c5d6200c59002d400445d9225410010246440c40800820455a900c1c0210000c0140341208032940c010034400610502e0080d801400c215010308200d5108121100c0701e030248000840310100070000f00c280510380040e800c0c10400448590101075400c1804205109580f40e24144089214a000d9006c0720103004105540691104028001d500c0c28640903807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 711489685 1250 711488435 711488447
    0xb0403020a15090f080d030f05010b030c0a021203070504031b030503160303090506040b0f0106030501080a03050f0d0f0e010c0518010f111005010609060c0209060108071206080a1103150c03070915 86
    0x40b074540401e040c60002649003c0609c0740307a05807080c0c9003015055446624007100c1507040400340005601c10780c004080207001e45405184205a1a61b030346640f10306624002c03015203c00281950b201001070401d000041c000f009075483c001c00052410201061410120b01a12803c08042c016001e080140030078000f0682c01680304620701c0d8280030050f42e0381d41046044910910030050190040521100001e01c50130003031981000508002d81400c00074183c08080b00c001404203071270f041d500c280c03e40c115071080c05550b405007010306185040c41600303969070b01b01c0448860464100121003c01c0412207010b0b01e40d100c0b81e400d000b000c5500440c044014440200750a02601c030119103910000070781c80e40b00d0744010300c041e0f50161046605840700303401564541d001400c85ca091080389800b0300b40b45c210503c51030009289c00c6005014041c0d50382080e081e1203078500100313806a040200210030782e400f16070100b034100d404560030640d2aa0707641800c44200701150020440e00240b4000400c071240c1c080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 711490935 1250 711489685 711489703
    0x6070c0821010305101b0801050118090c0e040e070e150111030d02180a1211060c030a0509040f06050306071202070606080c1002061e0a0902060c0a0c0b0403020a15090f08 75
    0x5406c0000c140f8404010300042d600381c103044d00060310540148419440b0b10301b000340d45054426402560380e11800c050086c1c4407200031040016003001c448007000d203040e0103018608103d00014000c80c0d41001c003201104840107041031120b24403c0c484400c264450401c00813030303031803500a585c5c80c0d080403129400a0342c4032254403030000c0b049100c000b101d4a40340508200b01c581d4282c1c9003800101c0d99a4800003854811541c07907021000b0701090340d030010280010005031409599a641e205030401c1000304036810308459160403450140107000503100002c101d50000d91505041c48914010000c66002c0d21032000020f02d03541c2480000a01288000b41034480480205c5106e14641881e4004986d03408013211241400081a0302c541004000d03e8805034201c8402c1304d0228034050941c010501c5588200c2280c000c50380510f09000a000d4000200400f90408110241c80c0c1455034000610386040342c0140c045000403500f44070324045c0540c0c00c4000800140c0401c89030145d50b0104152600001c1c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 711492185 1250 711490935 711490963
    0x14120f0414030d051b0a08040602010c1e091a04030204140712110d0b0613031109010f030c05010509040209090703050601020c0625170c010903030c0206070c0821010305 74
    0x4441c1400c0c1c00d02e4003003000341000712596500c90030041024544c450381502d01c214025a03004082c65803011030b0302a0010030203880c0c15000892a0b0341c501d800142105418600e08010b00c80051500c0070b401c1d48080e40e081102c81032080714040300300c6080e40ca02d1074420b03584000e5102d4a003c180e80303149000c000c501845001d480d01c0704568102145020400d8130020102c02255100411100d003010480c0e501940c9400710182c034050800f88046001c1c01002c91070b0300300b0755510b243d13810444030600c2c002e8200c0e400b405940c40031898003461076403481e0369038019000e4141840300c0030400507810389031382e8103443c0c100e03000600c084802e003030602000d0024a001d0fa24cc0e80180598001701d0300300c2c14204119041c00381408a401201c0144c0c0c00300401150418004444404001092101d0241c2c0302024150740c640071400060030081902c0c001c2c046039039000240b001c0d904110704005801c4d420030200c9108a8001d41c000d503580718562546040c1c002104922071107403c190380084180a00014400c80340001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 711493435 1250 711492185 711492209
    0x3080109381203180109031505070507020d031d0d0b04060b0301090b040501060609060c0b06010f020309041523060a0c0507151101050a0203010f0314120f04 69
    0x310300381241591644410008101c00d403022541c6040c0c0003001c028826880320306020001d05480300010346480221100d062280e00c04195507081140c0030340004600c24007404c20342012455955010001001c8a049010b01590740e0001040c2a02603821101c8290b40107040503048440c0e440d003d000004100000c40c650141024144601e0401c01c2090780602e4210f03c0b454110750f56580c81c403000d480030720607032a0955294140b500018110347e9010f409240304000100c0c446042130030060849899900132001c10401d4201840442d0040c0c8420307070095020300c2c003448200c01407070081e403640c481c21030902d41062078151a11558152881d004050b40c1c240f003051140c501580d80c0201d022005015002c0d440710040040b1100306000c0c0101e00e04042c400c000341d41c107465031104445000050000f424011661400007031403c1c0c442031041c25400302e0b000d0011411941070541d5055a503096000040c034045200b00b1401a0560400c00071389a0400c080c0d032683d81e000320204c21449030700148034941000070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 711494685 1250 711493435 711493439
    0xb0a0c02030f070f0503040f030b0f09010b090a051308030c1e0403080405090a09060f020702010e090907050d060213090e0d03090215030414060c0c070806090d111606020109030801 79
    0x3101104580200d546181c000703060042a480310010040703009030840e41880200030002c0c5a5189554020046004641150040c54002c1c00000300c0c0d2002404000503903d00315004c1e01503135640c58100e800818640313000940b80d5a5140c5010030f82105071002c3c0c0400b9010080210788a0501d0040c110300d0030a42c0b2044180300d001085603003900a6010041800700c0500c0207200c0b50404809099102410160109400700b4945500c011034900310682c3c01c085e40c000a188041d544c100a0200981d034040c0e07006103c2d860302640254032000d160040512944002c41007800780103070f03501600c078000088028160080e58075800703a8010b00d07024010800174050460000358544c000c1c03042030045500580032058004c83c0700c11110f06580004e004031045801000b03d4103115400300f003143c0c484d5064034045a5202e1030210054030b003a8250f40304c801150b104204108203031102052080b007100881c18a5984902400f03600c0d81070034035251101070420b8041100081d03903941504404021030003610b9480890b6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 711495935 1250 711494685 711494687
    0xa0f090c0f050a1208130b071101090512070b090d020315010503120a120209040608100501050f0d0203150a0204051906031d06060d050c0a0b04030501150315020d15030b0a0c 76
    0xf4029104841c03044142d8605400818900f4004010301700009203019002501c03410351510316000000127950201e81d036402d0039041e580140190000c0c080896041e1440c090042c8007543d9407031640100ea40001c4081040c18082c2c845001e45180203030b004003500d50140c0d66018034030058100b40700d00c510a2240585455490084030102d614a035481d50391400d040d00840c1040010354000386c1000e80095903050000344901c410321039000c0140000320042a82d52411080048524100d02c01c2c03881181c0190300f20006a500003110840d0040c8054156041d503039100900009001e264022034002d95240d4064100c20140c0110100340c580603101041014010382d0b00c4000e07010f441080032034035885a00492924a00b582040034081c1c80b60003180c0d4403401050124003480c2d074035440b0f03101401011809000300301007030140081808040761450a601d2440e1102c00e600351048031440c922683c0040c959054160903001601d104424080302c00d8566034919040c166100d08446c03522815151141501450b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 711497185 1250 711495935 711495949
    0x90219050306061b0a061406030622060504060e030f0c011b0e210f0a060605030105090307140a02041e1b02121309050c0a0f0203070201050d050a0f090c0f05 69
    0x4850291215051000c099030352413240e0070a08a03881d030340c482d8160010000b03001c3d029448980b03010011000403403c2c40818180703031200107070503e070035928000d0202c3c601180c146410011720b03030496008241030300d45d801c001004102d0004541058040090405c1e0081c164200030002542d6200080042ca010403410ba00190040d119400008502c040416428909050341301c0c21110008a444158040340403103e25200c284000307180c403a001220b0460502c10750340b080c40020036094000303100a1500071041034030781c420300d03c005107111b03100d1400080b81e040800c0121001a0702400421200b0034103a00481d100503500080381280341410310309615068008108190000141c005050910640f007140c6001e8000c00c10b4064500440c04002440400078080d650040c0010141160789180103400280032013080301d00041035500c104600b20050360b004c400c0300c00c0d6040c04440003c0070f80301c0d5030500002e003001c0c1d40c40c588428100030000090105024880c0c00302d580c030f4101074800541d00d205001c12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 711498435 1250 711497185 711497191
    0x609020a091a070303020c030c1615050304080915120405010618020a020a290f0702061e0403050912060a1d0d02030f030622060905060616030e060d060902190503 71
    0x1060b02c1032000300c00290181c0c000c1c04082c42c42d801541d05108542298526094900006580d0350407046d80c108601041a9034400e0003004c2d0703161241c95485c0988512043c0c1c81001c04282c0103207040e140e00600b01064005403a13500c103103495011102d080c10b0038079a000e400340340034003e03105004401d102c10340b110700c3c401c491000b1025005011b00d8040b40d2140c000c050040410300180141d0340950a0074a410b1441d65482400d01150307601c035905007090000d14000c00281039180c0000c2e96854844000791104503560310691515120b42d07100b0030480441d05401035100d02d404184505018000319984c0394009000c10480c3d10360701d01140000002d1aa900d000e58004070001d60410026040c101e4940e60041d40e00c0000503040c1d1181c0440c80d00a00c4500f44111450444030340d8411060280c8101c90280c182c001b502254442e041000c861046041c0340f40c103d400030f09000036004031a0140c3c46040503559861000c507010061507681c0c10703041001c0c1d4032105c1e400c1c9000d420040c1100845000f81c0a03280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 711499685 1250 711498435 711498479
    0x90307090227010c06090305042c0a14010308091f03020705211804090c0e0403020706030506090126030417070510090b030705040905040f2907050a030f0609020a09 72
    0x112213034842d101c0400411141e201601005010000421445110b200c00c1003096440c1390545682e0200703004c0c0b020b481c9000b0b4500c40145091448400c011000301441e1810741350083c002c19034034070b030100020b2410010f62040100c160481c280b201e040341c2c4c040e030240c0b4085009005507044100910f034a030390158000d18940c0700c00c0f40c0034040002e02d03541140980e1146000038000240c0070701e02d0344502400901503880b844c02e018101d420402050703418400c14004140a060a000504100000034007854050003585800303805501c0700c0c00900380c4000f40e9440c0d401c40005880d550380d10350120882c800e079501c0001c0740e03910640b400000c80f401d010304540ba60303048603990410001d0400d068081994006031143c800c0110074003001c0340c1d040251007018021803141e00d8070100d041103403424818041c0c1000c142c41c190b0558000d103920104a44e41c040d40c1c444c112345812030b95504401c00c107900034101c0c2c0402120f101e21340174003c100b02c941540245404189070700c4156a0b00e5072070308002058054129800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 711500935 1250 711499685 711499697
    0x4090803070c260a18030503030f070c02090403080a060f08030904021c15090c08040203100203130b0c030a050c0a05162906010305090f2109030709022701 68
    0x592802d10681c007000c000352040c0c0d0440560324900b4460312440341e01001100079500e00040c1c9441840d00f280000400f603410f0554032040d58034680710580c80b03002c01000788055945900020705928484c000d000025940104101d00c0ca0406040081041d04111490701d10070340b0700355010035511a24041c07501201c0412001314944054001800702070741001111035250f502d07103d14150030301d12a0040e0100148100c0b0041800d514201c8050165540d41c0104d0b014030100200f4040941c402040e80c203500c079403104c40942d413a2103401d5100c15004182e18050290004038060140b40e02d440340007580100308001007800281c9030100030050b140309010251001c14010040c1d039200c2164a000080d000c1d00801b0099040c0b862824090039407901c110b4040c92440f200000c0241640e01881410b4111120030010a000030782c4000240c1d88240d11183c0000f51260045d900c0c154849031400c03518001406000e41e5002542c1c3c401200107900b28109414801c6600d00490f10700c6c0400c0e0503140b80340101603480f6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 711502185 1250 711500935 711500941
    0x203040e01050d21020109111c030c05030f040311030c0405011212090918140705010c0209100b1210080a0b0103110102070306020c07030c050d050c060c1903091404090803 75
    0x880e4180285104484181520f110340a04c040b0303078820f01d03c1070903154002144207900c0f440c0c01c15100ba440c2500394801c050706121403005402c6003500c00c2c02c55a1508008101490b54103003181b440c003902c803121841e6030000802004200340c0c0b074102c044800007502144c1610801e00d00b0801520402d0148020002031074180d000400c1403001505008096404c2c246c0016440c0d2814000391542c12a032017002ca41003100c001c00300052a40490001043c0201400302d01b41004002000f490030068007a02c2000c9110101303050240c540d254000800b4042d6590b40d441244050040d0410b10407076040f039415007040000a00200c1c04a8000b10b141d500a035519041d03801c50b650210300b03282d40113000e4110f01c034064002c80080d00034070080a00742103450062101e90310b907280042960003950032840c0a01042440080002c40018100103440022202c1e503445079214445603242c60191941e0401c006a2030750701809244e04000c08070706440030720508084003c542024001a550902c000400c035403c10400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 711503435 1250 711502185 711502189
    0x2131d04030c0602090a060504170606030d0e040b04020a0c1208040f0204020d0b090a1a0613061b21030c1706040c050c06010b1b0a050c04091a0a1406010203040e0105 73
    0x200360b1240b08000043c240500d00000c11480203d40c0c11203004108005400d114000589444194a1290f0340007807005183c010042500c41c10250682d005001c00198480400d0313030385030441541002c006c0c0003103481d00040c0c0001800da842406042c0c400c8000218009041885012058070441d0000d230701c034110000603420310001358000404005003e03910060450b655480e08c0700b05001e20540c140115102c040d55041200311201040300c14441c2404000030014240d2003e0b00303034100d480c103040030000c0c401c0140c541041d0b032003041c400812110409082112584c120140c44021200503a8108521f90725808262184040500318200d003401c6400020f91500d001c5c1c12001c10b5020501d05071381003410f08c81580b8500f803000e8100c04110000030030340692011400c00364100c0e95070340c0002082d5940e09903e8040c1c54000c4500054080d941f41d22602c800d0155000c8103201007040028801905d1800c08000f800410006040c259208409404110150704c00010356003500c003e0555400c6030b074a0101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 711504685 1250 711503435 711503447
    0xc08041a0d0203130606210b091c11010c0305040305070b04020307231203091f031508010e1b0a06031d01060e0118020304082a0f0102131d0403 63
    0x31000040480800c42203200030034500295000703c00d120502c0d03250b01070514140003646c420b80c1180d040769083d04880c07241d1600403094080c140e0381114080403152541c20110381081c8402e03103000d0394041d850442080d186c1d40125801c280103a1000208100380e60f1020480a45000342c40c05800a80309000d02004101909440368000b40f00604451060796907010002401e045041c0d4000301410300d03805622a030070604070120f20040a04080c500e0001d0150004e00c1480604000d180e403146a50402e00c204c90091f4018848280000a280d00f4a9a1041c1c4903000e0a840d54204542d40a511124000d61031f0b40e000c80c04604600610180105040c204120014104102c180490340c00c81c0682204440b801c1c41568058804028500e0240d8141824029040c00358060455214410420000407070100010740c0c0d4035220702001d031004005000800340c442d5840c5c07e030302d00c4107000e12040c0c011082415170041c8800106030340f610942c103982d00c01194030340d488503005c0d00c004200341e00000d0010348101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 711505935 1250 711504685 711504719
    0x60609150e1306030c0f150c050c090c18040b060a1218050601051c230c0909011a012c180103122d050a020703060e1b010c0804 56
    0x11810712840744404000442d110301e0b658030072030165920301e018411302c40c1c08103054025103003080003064100d10b0305503104604903900c0103400400540051200c1085000d002d4200c01150003000111103003040400c00c1c14070361010940203000e211203040a0454141800740b1001084010901400c11000c48130aa84448141c40c0707559031280d45210842e81000900d00400c0d589000b1002003410758100810b028410710050000d8483e02c100c04c03145070002d8400746902e81c50505070017021220b1200308041c24500f90460b40c4095000d0b0300d510810030311b01e0055011030104c03001e9000040c3c4400142006441644e1401e40210240c80c2c21220402d00c8901c4035100c0082000c064200d0a00d0920202c2c1040e41100a810480d1042c0e002007a05200990109000c0408218803145080a9404004a1040010319080c650038840089490342003031b8001e00014000b076401900920201504207800b580722000040c003904183c0b1542c4540040c2e51055110158540e40640110b1a0504100070f4a40d074110301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 711507185 1250 711505935 711505937
    0x2108040b070518040f0605090f0c070f290a0b150d05060102070312020a02010206100e04030305180102160212150a0905031306020d0e030105061e0f09040b0403030f06060915 76
    0xb540f5039140d19250f500c24450741c0039183d0000203045060204001018001622061021502805001103014a181200d01243e0f100308072200c1c424240c90a150f11059100e910320009621803001c1041c3c009107000740d44500a886420029016250300f00440c442a4240f00400900c061007078410131115503000c6a00480140112041250380395650030b804808814107100503080b040315501156010001150070100701d00215030400e06102e1070b4028088005c101604068803000420400e02e44000284c8076205400c5c029550b500180c5103540c0f00c0c54814408070301807880280e6450055001190135030010840e260656a640c441111100182c2520a0282e466000400c201c1c06207055481d155001001039801510b044c00c00b500b4041c260700242d00915002e07074181810001075989580d400d07032603800342d039126084910340348010403035034034103031404d1900100000140000c0c440303405059441540700c2c2c3e07418030104048802c924240ca002e171084030003180c03082500b4061002c0300c1d03a000e5110182 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 711508435 1250 711507185 711507217
    0x1207020f0d050a050d02060f04030c03031806152d1712040e070f0903030206010b0d0906050f1801020423060705071509050d11012a2108040b0705 64
    0x16600c850341412080c0401301c0346036014191101d500c40d018426194005004510f4110b0780c0b03040c0c0c402400c40ea501c00001401c040e070703a0510182c40b46003012801c40303040d045042000002c040054464031103150707001d8000300198180b50312600b048203070030340c0394451954060307a00090302e002568141c00311808140c0300b4600600c00342c982e00c00f144001030401062076090540302c5007007804002c0d1175010101c40c120f04200f81c42e401807010a8000a01d0341c1100c1103147c1040d541d4810300300000081c412008000c01643c100418802c2c01287e2801407401008507040d24601c0001c0c0090143c200c0c0320303a10424426404012803940717031540c0318007a10403c42020b41031900e0401c00e595203074200a015000690340d003005410f000d00260b40b11a031400503040585e11100c0112030751301e410141d07191408041e4100719032805c4642c50144240c42c0510700c0840301c4614040d203540c52130207480c4d1800544041407840f40e85507405010074410039016002e035420000f0311039580c486c0c1c50102c8582e440175001080180b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 711509685 1250 711508435 711508459
    0x512030f040509040819030903090e0601020a080c16080307050111120c030615400509090f2e06060e0d03020309031501090c14040b0d0b1c11031207020f 67
    0x8850806c02c81030115590000d030900851401504c4000f55420001ca1400034000b0056543d070005080c030010380c3c01507076942e00c48503060b040602d030000c480707903020078541e4240000401d014000094041244104005c0c00060002614502d00e4042c804001c50030203c01000b04802032070b003400460308240050030000c00c113212611800aa6402900400303c2c2c400562190461700e2001d500c1c0140741d142020440120300d1a001c0403401042d41d9019184c842c020150119091500400050300c24034400020317500c4a005402e00d00d4110020092401000c0c400c030481c40070460142d21807682a5441e0342c0380c0e05500030f600c0044c0015148a83c104074190311041100c2c02d51a50100f082d50303010f100c130b20ba04109940c100303d4400c0c1607420313800c050014084024007903030052801d0003d0300c0c1500c500c0c00001c1d03120241001c540010b04040c1d10304a030486076001002c0000c116070b5002d40c0c0240d0081c070841c000750103960245680c800b03a001480f00c000c07806012400c014a081103c614842d80005c0c00010500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 711510791 1106 711509685 711509707
    0xa0311031e250f0b031617012102030601080a0302120c06070809030d020a1e0c020306011a1b011401141c1406100512030f0405090408 59
    0x90310307085020200d0342400ba10708020560b03812000303801c9a640804c0c1000360f0041e203040441050b900d0f81c2c504044d00801c038038180c81c0440220444242e103080c03036201452040c0c5a226040440c01a601800340e0740800004e8060b00a08000c1e0061485a1401038500038004031420b8841c0d10a00c42103218100100d517070380d804841810000c2d52980c55501d024154412408402c02c490303c04a10f01d0f101e240c0c000c04d0700d600f40c146e003111103e4050507098255003c9081e07980080d4581d00020044c040c05100300028200102d000c00c0d11410032840811400001d107148103110566903440a90202611205032814010098181030300c241b0b944071700100d03002c600c01e4141c1101c194009403c8008110321210601d01a15100c8251000750404c89804002440c0078071400f0301c07902c80700500070148140030040712100200f44006616141c41c9c04e0602010003401002034454405c00c0c4100f81440d = true := by decide +kernel

theorem cover : BRFrame.Cov 711330935 711510791 := by
  have h0 := BRFrame.cov_init 711330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 711330935 ≤ n) (h2 : n < 711510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
