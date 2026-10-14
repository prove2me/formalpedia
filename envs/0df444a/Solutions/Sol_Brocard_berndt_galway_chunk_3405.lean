-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3405
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:34:09.117239+00:00
-- url     : https://prove2.me/submissions/4ac509e0-a3e7-438a-a23c-507da59c1df2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 612230215 ≤ n < 612410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 612231465 1250 612230215 612230237
    0x604080723010f05070213060806010f080f0303090604081b100b1e060307030b1c050c0a0e13030804050f060c0c01110301140d021f03020310050d05060406150306060308030403 77
    0x441c3c240302da559003440815070800201025042149420448250030f1001103542c940d1403e90070b02c1c3c038009038811140c0e0388171103200303000084083c0541030100e00d0f448000c40c00e6042070340c7c0a90303c3e000c001c1c00052071201d0005450104203056800400965a0b0400383e80100301d0700c5c84148081d20115905620402200d406040b13000134080000c0e80740c0402403d49410340e501c07000103400900c68107207240c0d8090300c120700c0c020031200c501c141c100b4614410ba020f012249002c0d03050090503142c6401c400d5603a1800002c000602c0d0525a84040031034140c40c081d48162500e003013003405c0002d8403121508038004c01040001c51803075000101282d8020310000c204140100f001130300b0b030303010a0080ca45c175407d55400003001072a0040c00d074880303d0300050000100001d000c0111405010048a10004c0703500842000100e00d120412000103003001d0f101345116680796918251150030041004000300d40e11521803611400d0011a10045c40e4049010171025482c0d0070304810703642045504500150444000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 612232715 1250 612231465 612231467
    0x726032106121209010207031e020f0a0608072105090703031202040602071203050903060f010e0612100f150306020c0601060201021314040b0d0f021e011d060408072301 74
    0x81808140b425015107181511810341c01155801078a081c0e046110384800480403d280b100d0841020500d880c1c20400c0c4130503031051204a000916070a48680c42d802d20800c0341ca904204440d9110550b8908003001d1042c07c2c020084000440c0381707002c4854900020010700d07040000b1203800341ca001c0d0f104c01e02044403a603003c01c00d070b1182d0700402c0c0050304540c40c200700005400e030f250102c0724440d041490500004102082c5040360481d0007030440000c0e4801080b440041049040d0085820345800a540c2c804100a41e40c40700d8031641c001c185659143e0b0f070f5024107001d92110150b03c46180d103110f041c90342c030300b00000030703402103903616005000e01400060001d00520840703045059803c04180c00b185803070951440c040c06044819085912141c0d642c002c1d54a030140c5443c41c03440741c0103001c0101028010710072490a20280c80289100082051507281e03002450342040900300c0a103240c2600c02c60b008103001d4041d50b401040248203150010030294403000c0c010b00c1035445600354280801c01000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 612233965 1250 612232715 612232729
    0x2040503070b0c100c200a030903020120010c050c0c0a12030c050304051306090c0e0603010506070f080a0e01080f0f0109021b07030507060e120726032106 68
    0x205299255001400800103030050302c01402a80700d00e40c0c01c0e26040140c11820f00700751084d144442001449120301d03a085940207040307100c2039140c0c10004090502c4c0c5554050b00e070036040c0c08064140300403070b101521000c20360300420400301012002404511100e1902402607000007419403400e0040101c40c84071810f10100c40303c00c0303400001510325944055142502c00082c894026111404100320203c0c1c0e5888200301103030170750400000055054a00201d4804580da981140410000c0f04140c50071030790707030b0030741a0b9041d20802c40d600e584d602c150389810788521024500007002102c0100c1c1c16120207400240280e4a1039003070701c4011681e0384100e001070300140202c44c0c07140d500d5401c100500c040a4141d01400b5422055202c00000386007841c43c0500d0b0200941c42103900e5403204e101807000d40d5001c2c128884800090300c5d4000460031098160341c49003081c2c081c2c82e24541c0700003450308140710802e408100b145005800d5a0f91140c80344030403182c154203848000d80510322280891101e00b440704d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 612235215 1250 612233965 612233969
    0x40524100b031b0f04030c030f0b0a0507021c0201021219270308150303131e0f090209010507020604090b18071d030304181d0312012702032403010204 66
    0x5101080e06910f90940364400d0f8000c2d2002155401d028080800002c020f0a103141c051030040b0000003049260740b034046801d0000030000301c5401d042005200d4601d0b00080c186410064131801203260091410080b4024004d5a03001018149490f06020b00c2004400003c141d40788410400d1205000400c0784410742c2200c230701a40305001c484e80c107000c0802d12a1040b241c00183e19003902000c0d10844001920b5500b00c001c80280700044200f0400c08180100700c2908594100e62030780d1503045c0341c00d12501a61419102c3c3c034101e2070f000500c48080d81e03c11802c40d409143d000748002d44858440b5288001803418044143c010800f018043e08007030750b100c240c58403400c0a41e85030000c1103801601032842c41c482140342c0341c1510003400085482c3d510468000d40c85103103c540040d680d0010940720781608110420a44190420001007200d561107001ca281500c3d62440c0035425950018481003940c240c2806030b80c006440802800404c0c08500c0c40c4520310003400524a900a1403842010b080f0300c124 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 612236465 1250 612235215 612235231
    0x204060803040e0a020309120a0512090105060f010507060e03070c06030b09040b04020f040b03010e10110703051e270108071701210b07031409030307050a0305040524100b03 76
    0x481c00a904044c0d645c0045610a01c0fa0301500d40b051a03041c0c0c94012a042000c1e590040b400100700c0c46580354021913860392100105000784400d04205020440086800f105581008000115041449007507000009000d0f9020101da0b0341700c88a050044200d40e8500400d0f00081c2814101c01e46850209050790280ba00300b15080c0554030b4580c02c201c00d0412844000d83c001d5190740d641d00055500303206003165010051f01070075086c00242c0c00c003011950141280c4075048014440040402c0c0d00105480c1140c00b808400074051140c144240d5460060300101080541c80c006a10032038102808000c42041082e22524078a4444485c160742480924240c9e143d00041e400040162060072119203803880d85030f1140b4560b008054075a4148044200c49010200381c03101d00003911041e040b003c003680124008086c60440c1050100101140b1400079020b08154845000c2014032105102182400802050f96141c122003c0700e0044011001c881d081c041002e030490008080d4841001c0768805c0000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 612237715 1250 612236465 612236489
    0x1806030601050402250c08010e1506061b0f1606030c020c13090813030209010614121b03090d180f03020d0303060807090b090705040302030c0d03110106060309020406080304 76
    0x2e102c20321000303410855200241500c0b000340c00040340b2142c6210450607000b001c050085034203118540d404c0d40c001c7e00002e800703907200f000d03090005852101c4040d085034080761100d64840902e0310b0201c04491420f005000c40c001c0015032010701c2400141c3d50000010203100c821043d40c0e811082d022140d0340d401c4140940c0154402540038500b0401e82514602c4100c400a42d01d201d0391256020713600300c00b181a0310041d2040042c405d514026070740301c0c01401a40303009002203040720040015406210450352800a81c200450342d400c000e84202901251a810140d0312864000c424a6071903d00e0303070b0000d02041c1071501441400058038600c1c015900340884208021349580c1c24081400c0580c002a410159108004500a00d0130701040004000c15480400d0b505407e030100111308101620550510108120400060714046a40e4549100440708503181c02041d0030151901e0341c031a550b501d010b528004000c50b50a0701a402001e2140c000d88003002403946030004540e4a02c524041c0c0003891103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 612238965 1250 612237715 612237719
    0x2407090602100531060e0c0607171606020318031306050c160e0f06010e100305070215090f061b1c0f1814010c09051002031b07051806030601 62
    0x40c5402160b00b0903258880703d50307006925000c21400a007895454a0400340034042c24080c41054002c2071003251b40d40c0f0141c0549010107000072160f10810705c008000012010942042e44109801d481020036130181c155407000c031902e0440c00960046511400000742c80341001507000780041610b92101c0400007805505050940540d6540c02c0b01c068689548140440180c0d0b000f4215142d8005250000f00380d0740310704140d11030070401000240102d041044000262056507514214642c0d10802c500f00020641c450705d20803410580814000003c48814038140540c804000034400551040c58003a00c200c4d03151684903a83d600039181d00b42c01403000074400440d220044040c00d50075003503400c500040b102c0d200058a001e90b040b00060014131001d25024100740058881c85108040c40320008015218807034002070f110b01803a0007420f0007050081408204d0500030411182d407040ba00550410202100070501d949030804d000d071502030b0800f10040710040180b0300b540d40c041c1d034005000e003020380c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 612240215 1250 612238965 612238993
    0xa0911061b030c0a031205150d1506030b090709020c030a08090304030609080405011e09060311040e190e0a0c14010323010302030d1d060903030c2407090602 69
    0x80c1102109032180700c200062110460030800040c50200f0b0070901a040c1d46519043c0645000e50344020700c81c0150030320302000608490f01c41900e030f120604444414200501f403c140c50703c50f01001e10700b02d82e945041004401d000c1c089605030712488102d411690582d4a82207c0f100f0380c0540d0101d004594003e005540c515405883d000780c1c00b007a1201104e0510741c0c0d980302c410903112840c4044d00c44c010005410322103540d00045401003070303403c0080c425820341e902c680200b00100b64442c0b201016558600180340840034421540104488640355446003400190640c03100310508c11410050b140204040709600c0c00705518980300e8001209101c0549030a1200c52401c82c1031490b1410140e940d50844010703d262910300060810b000701281056042d4418140380c41c081ca0070800500c0b101038403081101d142440189450700c0c0c2a00c0741c94840c200000482d26502500c41110010f005242c0c651200c0c10124150b0743c6a0854445210415114040183d4010400e0b000c4c290041e001415030300340d40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 612241465 1250 612240215 612240217
    0x30e0715090b07050a050a080c0111030c0d05060420040503100b060d0509010212010303020f0c0307080c0f040b2d06030708040201030203070215010f05130c08180a06051504050a091106 81
    0x140514140c0e05040c0c1540d946d03038113001115100311220361011440b402241300920030014110b02c01501145541001885003503a400342e800011842c54482c0001011500d40381c2090540d400d03105d06400c2541c920410134241f0380c0041c021035019121f9400e8920403c00b5038001d03224884001f500c55031a02c1084104070000e070000514114956408000808000061181d518000c40c0603a000e004460181186d1a080500c01440e40d03200307500c01501481095070210700c0d5111100c007162054090450080800c003d825400d00c85035200082210702c002202c000705a41d14004000002080c0c040715907410081c03039002c141d031041c00040041c0c000400650281d0300443e0003d03030900480385070002050480410700c2c4260441035400c501241e08001605001d080c9903400d810815040c03041249404002302600c2004081036402131110204138540001030100f809401d030411010b003d00d01e041659690f0104405180c14001c0f45800300003030070400b243c40340700310a5034401c40301c0c080303440050104416 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 612242715 1250 612241465 612241477
    0x317070807020108041a0c0d1a130e0c0315010609080a05030d020315040908360f01050d0606090f0e07141b010204080a0b100e010306020304030e03010903030e0715090b 74
    0x40244c241d02080403e43c9554144a0b440308001f0b40c0e035842105080c50152010000324086c2035181010201c60341d80c804030242140700e0003000009610351f40b09001c80c601419002206c1e0540110214400021850007002e41610b6454881d42810350346d40c110030f42c1d0345141c540c01030000d800910003400d0301403064004540005441c04c40c1e0200900da2070001c0d0403690007680c103c400c08070005540403841c07220002c00352a80c03021074051002240036080310b100201c140001b03d1190040c8108822a6030054041c4d542803841c1c0c10341008100c0e103a0078085d11070071060140000c04a030030000040c1c0c3d40e401c04080c902c55000c03683d5125803582c55014045140e00001401400c2c900c030600302040003a024800303400100f507901c00602201003907080020b4060006459100c403000041824440c84003820301c0e45044a602c1440140c0c4d03a611030074219091112a0f02250b407650800e04420240359058000600d003100c2c00082d50030a941d100d0b0100c000c0340301c500d899008180f0903602040241c00007405001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 612243965 1250 612242715 612242723
    0x3180d1e030f2d0603020307030803180f010905190302100507110f0a02090c03010518040515040f020109090b0d0303200301060507120804081b01090b10031707080702010804 76
    0x150039205078500000d4600750004040781c2610f070100b1000e24442d0f4000c4612984911000300030060440e00800d46960b030f1804082c056241c0000842c840030403643c01120240022000d45d41e00f00c02602c40c0d0f5028040da0301c0f0980d5548240002200e01407620803543c600c1c2d9074075400402146000210502c00341400600d0103062003450101100e681900344034038101c041858024011181d80e034410003010000140c07a898540f0b10620062000d80c948030101c00c40040c0510120145a40d54601546000120700d107030415240994240400c001003100800c0c0158800d0300c410400716150f1041d5021100c0b082c03105c640c4a8214003086010038002d901c188140c00740213403d5407001a0003a0b441085070300a92200c40050300002e1003800b440b4070300c60a804112803503d0568264240340d220001180501c901444418080301c44d0f200c0100d009500401500e81d021440f8a07040c607181070300180707008c240d2000352111001440d41061070140c4c1c0e400c503071000d6444a8603508110158004503007281d00140216 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 612245215 1250 612243965 612243971
    0x8040210090801020c0c0102100207050c0913050106060906020c0102010c020c060903120c210403111c06050a0203070f030e061308160510180c0512030904090803180d1e03 75
    0x802d4012081c0010121107101c20010701c131005040000910304120090703907201300f81c0b05101c3c0c0c0b40000c1d004192141c150004a503e5601910b8940d01494540403020000b4107941c600640003a200d90001a003030129a12078080c0d03606c51007100016400e90700070105410044c1c00104030250f981c5840d03800340c0088080a01164503664066088a41a0b40b140300f800030f0a43c00406081e01c0401d840255030080440d419182d804c140c5142e56040b04030210700000e510580c1703042484117079000003041e10441c141e000f66003400f85080c49481c2074006d62055503040000744840c0e02200308940a0702401c0501c0d0307a80d200403d26a034920480d1800c0c03004180044500d00e004021034000c80c403204040702c1e4428003410103000e14550340e041440454480042888800d02680d00384e0021610030305000b401c0b13500c00e441001c040b9000c1d0444600710b20910046a501502e8010307070000b88081c13080a140304946200540c0d4440d51a4402c5541c0d032401403201e00005031000c2d180002042ca0396200c45410751031401c000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 612246465 1250 612245215 612245219
    0x50109050606160311100e0a0c0f080309061e0304060b040609140103110a0f1e06030b0d020f0a05030304090902100302030105130b190b0c0105060f03070311060d09050604140c010804021009 83
    0x382c1b083c0c96800080390400d0744018040c40900c44403120410003071290400e91441c86140c60f07081e645900518104612032040821081c0c000018071555815190070040c04550f40e1820703140c81c800031301c1407210031b500551804202254410f042d00c0341e02c0010705001c01200c0c0c01d07845c40c0c2d501c594850585943c640c02162101c000940200144ca0100151007a613404441e4981d000d1039400900a06600040416041040c200305580701c00c846449815016903000c07200315441d81c04903410315011b0788450740500c80010001080e5103250b100c41c09030f0303108950130032000f07030441403c4041e40003e004140d44848190507445101c401e40e800701c84104c030040c15038640c4050321103030340b090000f2036404880070240c0005c001200b0042807007031550108080390030344251901000840c0c3d86101034080201650740c4008000d09961350b0320142c0302000310082c1b040c041600145816506c66805440c1240c0c400c03228035141d0714100380409c80e03003141d030010703901d0244550b40d603002c220030011903000d080c090003150b80d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 612247715 1250 612246465 612246493
    0x6112e090816140d09050a0b03100e01060309060b0904080301050613030206040b03220308070c110901060e03070e010501080a0f020912010209100903080337050109050606160311 78
    0x501c05000f0f0081a000e81440d46002015080018040c107150400400d00700a20096a90075240015100c1c3c50b072880d516559214078504064886400003110004445c0000840d00d0389500071204841c414542800042421414045000c005890050011405000600860a10001804454a0103c01103c5a55403038010034072590198009121003030000040203908603451460403080c1c0f654906c1e01400740e5841c1c41c02000140050040801c1090035a1108203102401ca0308a101300c3e80100030319001d50351000c015224503038080110703019004400c800035580b034442018504a441c1a158000b00da5503001c400802080141684000640e00344200b0300700380c4920296260b0000b07594001a681c0c410074081240000001e0b0350b81c0d04100c50400207100050141c0182c0c0c0c4c102000c12030350603510340c130000701b1480260140c00c10f900d50310070214400080c1d40c05422035412200501c0c2c0810458030b4032010701096124002c42c5c22070f02d101c551079050009218940c1c041e0301d84000e5042e24446060303070302c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 612248965 1250 612247715 612247747
    0x6010c0c0f060801080a030c0b0601030b0a240215070c031e121104120f021c0803070306050a060f1103041d01030c060206071d180106112e0908 63
    0x100221041c1c0080520080ba00309841c0e60150044030010010080f079650001c00020788040000e14800100300860826406608400854200100326200e200d4507030760400b644045076803803006075442d030001c0c2070620b5001040c00c1c424405044010010b69507445401e480c6000300000440030442c18002e4122101400341900403194195602d080f818408400389106503840c508140095100401c03003004684a110140c140303032913000010040d41c44840c00011003100056040c1a43c4444e20810781c410040c0318001984034551301e4404010072600c90341070040d00704c170a001d403402049460044072420381c0a031600d082c0a00c642c7d02104e24103900d8090101400c0e90001c440c00c1c0c000341e804014000c020050488001900c0948010282c2d0319096000400305c50303010f074065200d50030341460040cad5920350165041c00d5003a1401520965692694005c1820030040d4001450b0b02403003804011000da4200140245024a0300d090003448010500784001e0042100c100c0300f07030704100590ba86c003260000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 612250215 1250 612248965 612248969
    0x2061323030316030c1b170c06040501060f050d080d1104290f120901022107020d080c22050a06080115032c0f1b01170f0105060306010c0c 61
    0x4007a645908150705a024078452075030391a8181410070303561440e415802a5203409000001225071500413507030802100d150103010080c943c03003c0014080140010015105009a106000070049a995007540c65020641030180c5a03210480002000100da5114080c2140040441d03000401d582d400345030754400d80c4980c3c0106000940980b258508081d80f002036070070441c0d40741010f4a000d648812129113407103481300d02c400301c0ea100d202180101d20300b54140e58060b00d200380110a00c0310a0001b0b01102201264041c1c0144609500520300c0c510445d00c1a00408044091504003141152501414684404140c490101c440b20020b0f1130f42d5100d0356117004004c10703114402c165040103010201a107030310f031441c000e05042c2201000459001d035420796a00b07070703603c2d6400700e4103034122551820060192203402c0703140300780c480d0308481c030301d0806240540c10000d807541d40311500509215410500e00f00d600402116842d0b00402807030400c2d00085601c500e0500d0b01c410340342ca0640c0ca8501100f100d07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 612251465 1250 612250215 612250283
    0x90f061f060302040f030204022203030e090705180f1909090b01150c0204051b031005010906021203011208071719031a040c030b030708010506100e01020613 69
    0x403210300280842000001015000c02d2506515040c2001040710030f6110382e110090260340d0020711240c680004210720180e14100e000c9602c9000c4d52410000c05140e00c15440030320464000c000701e11024056000c5940b0040e10491906150180404200c0078440000d043d6801c4045504250300c44208040c4090207070a1001001810210504000c40f900300141c00082509109040080c22039030006503001916034103c41c003103402c0d5248071f4001e0445804184034040108048240b009000c1080411000da880c00e90710101c1190b034a00c001c0f43e0700c8042c071070f03520f010a0040005100000008181c846480d024100c0381f8603000d5540e03543c0481558280460005e050041214814803482a01c529142401c0345010300140301c4d4071080603c1c009000d1840c5110350380d10803440d040a8000c0c0c01c104807000c001015610950703942e6003110b0107403900b260200e100d500c008440261190081c5440c2d40b424106a000302110ba880400c10142850507100035100c2a40b44602a29a5451348000e4600b0581b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 612252715 1250 612251465 612251491
    0x203030c0304180615020a0f0503091011010509060606070b0c07021002030403110d150b011e0e041811060d0209060a1106092a0d0c0f0e09071409090f06 67
    0x49004074800700c4803645c0002022019245114030310640c0054485171035a002400b1005244007450654514400c41051a070007074a5080c001c54a01d401c001c3e031041d401e0f0f4400081c410f99032400e00c025103900c0200c4166510400a01c0854082940d20354103980c40101d0030130303c501d07140050300040c5800504502d1240140e200213020f0041003811606414521015142c00366031101d10307600d001301c80e0980c070f814001840c2d6407a000351050f071040410715180d0903100c240c983e070681c4190004000c18200758980d4092424407180c45903804c1c000300381000003508400441c103030407171540401c9a103a02c0000d070801c603e0703028040030101d03540f510010f01c2a45140c0e21040504044440c5440c10001c2c000c05641241d004600d0441045010091008606610400041500904d200090105001311002070204a200c00c000704681c10108240010b0310800074844569940700d0780d040303940300614000c4000303840340004504400d00b4202182c40c0c2183e0f11005880032513803d5511149014012203050b10b010b40b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 612253965 1250 612252715 612252749
    0x302030c030d0213170a290a0c0f020609030a1809180b01081501060e061216020c0a12030c0c05060705070608061c0b25050a0e01030b0d0f0203030c0304 67
    0x240b00c410040202501c0340c42881c0b00c80c0155403d900c581d070906c8003030691070b54801d4a400005620040711404000d8491440740d0b030800d00103100c010b081400c0070101264103044a41d080c2030001444500c500c851500440c50804128000c030b80e29030020711903008040c65504042030340c40c05270040108541c0740b09440010a890342c2807a0140303500691015040c0d40051040129040d860f0740481c2c1501e003242071200070820440082060340c490000e0b0030107645a40b01c14805030042c205090780d81845180c0c00c40e0440e090f000101b00c5407131a5840b1303528813810710401140010340216490302009010720890900c8964800200e0000d40c4a483d04940d0741d0880035091000d85d8204000c59044502581c0105c01c00c10b403c81c500c0000403411130003410050b4550700180e0f5903141d8442c0e140d541c6511442c40300e11810754400151190b08042048000714003080380b410500e501c00e01c00c440c0020401490b00118075641d03141e8151510341140d0503070309400100b12140b00e51100f000240001e1a469801c007075200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 612255215 1250 612253965 612253987
    0x309020906210a030216091a150c0f030706060e06030a150f091208010905150603152107060c0b0c0d0b030313051e0102030a050a0203120127270302030c030d02 70
    0x6c41d10b030000a841458540b0300720038035100e240d18614000080c2c070080004035030f0382c1400015014010b401405445003040c0070842d5503010024110070381c4201800e00a0340d40340d441034005488102c903c25095480110341c1c0740411032404400004000e04c1c600010005003500c1c0d410305480300c0c05c809455100c40501c840da2480c3c3d000074014014146400104250b05200981d0310920120318040c0f4841d03603007c408610303032101c80c1d07103c0c0c030b000d1000928000e0f6516010a420880e0500c194030b0380e503980150080001c0c002c0c06081c24030280d41d80032041d60030710780d0341c1810905981c010741070b51010f060b03840800c1c6400f03490820061981c854807030001d0a11034504410840f0704400c030303c500ca44c0c112412000f1140c0766000002e45404860606200703827680c0041104074a14001c0d0320348800d24015040000506240425044410358030000c840500031030804240d806444141104401044030140c1c05149002d0754143d91600ca8802d205907480e2003500868940b45410450042c440c00ea40001e032803041c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 612256465 1250 612255215 612255253
    0x80a060b0a050415020c10050901090906030506010303090b1c1d060106090810020f030624040909060f0510051002031e0301090b150d090602040e07030e06070309020906210a0302 78
    0x405085c402000503d2000300812503c059200403042442004500c460560780102442e0003c0c0000c404100b002c0e80c0c1d40c0c100075036920400e20065000c10a04440418030001d0303941122240d4000c1d464000c0d00e40070b01022040200032035038402107030316100200401500400d0014500030940307596450358060401080600703204c01008005042441001044950100607003520380c08a8120f481e0696041d40d06403040d0740503201c00c0f039407104990000b00031410203d41e40c0704440c0789002710740400441030015149800c4641c15100301030f950f201c22004001c2841d01030000070300b140741441034070b090404801142a01804880c00600c0302e090100040c8208186031040007a08801280c05094034264800c044502d4854000c07507107102034850004000703104694040350001d00804140b43c80c41d203032000c2e000740202403011000c807842c0070301404118545d2090254122140d001408511142c883d403040240a0a00c3c13034040c2ca804c0d9841a000c1c00c1c0d500c040c0f000a5000d40a900500700390740d07110300c02200b9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 612257715 1250 612256465 612256499
    0xe151603080a050c0903150a27110901050303031503010e01060609031412040909021c05030702040b090c1605010e07080d270b0706090c0f08070b03070f080a060b0a0504 74
    0x780c1301c0140b04e40117035a900011038500340081c1c00c92103080354844407541d901501e4a01e40c1800910a60036140d90308064111402c00340702d0164803181810076481081002d1103500b882281d500d9842400400e0403406040740348003004074003d000040c1d42c0f0b00f10450328256a496801f00700450f8805201b081031082c20880c40c4141640c00000d400d0740308654240d14450f01940c06920503440d030344d13100c0c502151a4090521907044551002803072000403454a26620750007010124016030a20b00d4640350350512000300c6000d400b24038040da0a01c001e2007a8102540100f680a890139900c60108861040c010f10000018040507800740203040e000140280c03a01131185140c46050080242414420490b6007040d402d42d651284c009a4902c06410164098110000054001d240da000000b038a40c002030f41081c00c5076861406da407041a9a040c5d058240d00040703440c20007050503101c0d007071012032098212950080d80c0c2d003400141542c40f0080b0903407030341040d03d00e0350110340006010710101c624840c0d2000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 612258965 1250 612257715 612257731
    0x501030f0c0903170c0102181002070f18060308070804030203060f010806011206020d06060503103203100c020102030708090a11100e03060c040314060103030e151603080a05 76
    0x120904040c0c0c001c2c040c0703815200180c0b0000955034802c08103045001141e508641501c025034540d28403500c0c0810065403950810f104c4d08020f03c0d40c000642c0040381c0c88088444481c20340003540c0ca042c486a00f8000c1c0b1809401c0910f0b9504000b00c0007400d0704025060740b42c01000c000c7d44070f60841c4185441c2c480090018002c50a0030001000508400103500e070640b43e61201c002503c403003a29100000c0e0107144500801e01c2e081031008910181d2241c0a14070031403d84010040c036a03981c07041c0781c980c0750203401044003000d219100b460225900d2045684c114402404840150000d00e4040089a01c0c00302840700603500081400081580010f050ba04402854043c2c286000740e1f0b0f9030f0701e41a40d89010780d98000c402d8049452122401001d0510740980c1c0601036808034900040c41c40d401c0e51103400200c0f19030447c0500d04594100009105050301d030302d42c0b1a48009400b040403c11050041c90000351280b80030414a0b4800304145a40c610307091083e101c9500c01d050958166088d41c80082c4101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 612260215 1250 612258965 612258971
    0xf0d0e06010b071104020a141801090603020a02120702060c030c0a0204150501021c02010b0d1a010812030c07060b040f090203010b1017060f190608070201090c0b09030709050a060501030f 82
    0x602291384180f00400d440d0089800581d5804c05c0e400a88800c1e1904006203502d00b030100301d0000c030502424107041103450076601d605070f03141c8039007055007203004580c00b0200507409076000040102400008002c1700340010043d5041514910015180d6401100890416040300914904601b0300d4000e2481e44244c21092610030f900f000b0000b0b50b51888146140b17420940d6504950000703000394040b074581ca401a002c4c0d0151043e504240382144d46c00d4071002e00049030400005050030000c55400c1101300e00710115450768541d403114041130740080700c0a03200c0c6507035045000b5159943c5c0c032a28200000c04070011400780312900401d802c58403400d1071a40920030071460144690750003103080d11a06035524280d07502d41c4510f00424a0400c6c16154560000080751032041181c014418030800c0340d0107a580c0c0340c6944d8030220101e00762400c0880060010304007030320034001c01580501908811a020301143e100d1035035918444203a500595914074156500c0f40700b03000c5540e25004bd1984421511014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 612261465 1250 612260215 612260227
    0x3190903081207030b03010c05090312030105100807091d19151707080106081f0b03030d0f0e120405030708031c091416050906030c100f050f0d0e06010b 67
    0x111100d0700c58040129a110ba1900000d03500c54000c1d4440303441c0e1040940200b200801c0390102800980c04520310174400c0c441e540911010200c114103c0381600d50207030052034915200c3d0301c15550b07103001504120a101e030108000c1a00002045120285440f03003910403c10b00708000c100301c041800c1c504910711141001013a400110000e100c8004a440c0e91180c02600420411000d0a2041e2900120304550130442d00080003032000440c40c108075130b0b10000c00f0810392103070112002c556040b00304507050380090101d20b018040960001c0c00e401081d03200851200b00b000c808c5803c000e1400314840d038030100414244160700701041504082c00c0410021450050b41211029040c0c540d542900c2131242c0310404001000000390402100c41080c078101c03804407809002c3ca02d00050300c1d0085c0c5008205441c0040d03e81c0c83c00050100003120003803c0c2001070503450b42c0440b00200f100c0c0860041c8402080110204107100d0010010090b0350140010a40d100224050070860180c0c840c407041038080c400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 612262715 1250 612261465 612261473
    0x6010507050606120106050604080c01090b120105041121010f0906120f1e0b0f06010f0e0d060612060203010e070806150a0212030405010b0f010f05071e060c0203190903 74
    0xb1150000c40c100c030341214080c2e0004486024041c07680107107800c82d201180004000c140041d821804502c00d8a8450240d52500d45007149402030b02032094450b81420010045030606a00444902d11014002850441c1c1d81c0808a642c01045941c0450b14400300b0042041001012015000e812081d81c14803045282001d002908440b5940c0a000c01c806010036000308941c22540b10441d292a8205903460307030580c1414202c0e503004603000320842a0302c0001440039032003142401c40e00c1e1540e0319055140d58000f014040d9220a9440444001d50b8520011425903030460b1052204d80c4140307c0540e4940c10b0108155890901034070b00014010282d00340071150b42d400c0b900302da8903c03500f801c564685040303c41c01c03031a0142c104425035800c2e1000090100f0f1100641051a180070250362103c120b08411004480301000380c40c0c1940028001c2c0325420005c0e042d41201825240b400350114000f0009865450403a41110ba5444c00b50b40b000642c104c84c01a030b010502041c4240d410004415851511 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 612263965 1250 612262715 612262723
    0x10209010c0b100f0e070201060603141314030d020c0c100e0d0804050d06020d05070e0a1205150903031f0501140c01021b03041806122405040f02090601050705 70
    0x20014600406000080c030f9640c98114003100410906848800807540c812030b0000c2d011044d1041801035080500100e1820300038090b5413001041070603c1042030380d0344440c440c3d1144501c08204c403d2868071180d04045102000a0b200c50ba034402c20043c0c2c0c03690040381300c61400701c50301e90031801919462502d0950b99040040e00c1020803042e0381c9000c4d240203914205026100d95001254400201c140b1482030140d00d901501e007014280400304043e40f0b40000541e2000440c140c4e0f903501c694588004c2c400d40040000d4070200900c224111800485246883c1441802c101d584a129038404010410240c0704909036180c00c0315000b1078074a00a040400003821100b900b2030784485824001904e21084400f54111030079080140040154a0041112030b42c480d4013601c03c403000034141480c074610710b0002d0700c50710f8102c48108000320a24100c941e1203184001a0103868074840450b008501d4007810640585803180344113908540c543c030841d10410640f000081d05050400005110501c00564002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 612265215 1250 612263965 612263987
    0xb06030604050612060f01180b030715030225111206061c021f0f02031815210702100504020102060414030405030a03051209010207020a14210a0605070201020901 71
    0x74502040565500011406980b61051031140911514003002940d980380b40496060320007611082d80e07003c0003040c0c8041924281d0110f207616030042d100030480c2c0b1030a02c10309800c00130380d4140941032480c44044003114605d07040c4a6101050b0065442c0d04000c0482040159608220790090704095180d06560f0381c1c000c000c143e0b5010304a01e540f540c000c0c1034501d07020381c1348035030082940c4030a084e0410380340060311025160501080403045039440460010064424122621900d81c0f22415404200282c000312102802c1c03100004020800340070004005445540d017000030390a4240c14249002407910441c3e1080094192405041c00010b0b0307030114940d5046904028480310482c5180000c1d411071145a0121754180f140c204118101074000e009040c400d000c40284007d00e54804550034240e20404000a601038075914060050114400c0c1d00303070110714060320170280c1001011842011180d499104003269110022550410541d40a200c1d40207050303200079401c081031240042d10002c030320 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 612266465 1250 612265215 612265219
    0x2030a0b0603131709120a1109010b070615090c0f02060106020d08040b0603010e010e0115051504030b0c0d062d0e060f220e06090609060c0a030b0d03030b0a05040b060306 75
    0x429591314030003c0140a0f104590002016195407805440115980381101507044449207120300c105021480d001c40c54a040b12503c8102da46042c026681d810010300c0207840c1603281040f08040414500340794070074550101c2954840c030503c242851b801a141070016488a0119808201e4500946500402442e0086d505c80c004000f00e4440e079000a002d040741700c0004210358600390711941c100c0d00c150082d07403241c003040482c2501661110144410f0002207100c1c200303803043c20002080099010074407a82d01005071502c99041100c80703c240400d0318089c1c2d02c50014524100342d030100f0b005441c24080040001c80504000d01da180c401c01c0407052000405043c0320f254411640003954860041e04040b400c1302c5407c9030085103056514900610302800c2c0d5800d00e03c80c040000e19288000183c95009440207402400980e0b01d00c6014807880d40012100d03c205601c92481194545402c025038090038403a4801090038110b00c0144130914507540c1c1f04512841c24200400003507107881d000c40c1c3e000760381 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 612267715 1250 612266465 612266483
    0x90c0108091b060f0c1f150b0327060708040c060305060d03050d0204030f0f03081f030605060a080604030905030c031501090b06090a060e0f0603071704210302030a0b060313 76
    0x4e41300300f080c81c0c0a0540d94807810301648130710507075000c80c8400380c403906602d0030010800d0503210245070305402604d0141900d00601000030410000746040011000801c1d07041229502c0010b011041c1448000e4410703a010482481c04e000070042c111218a000d444145400c0041d842e0401c00292031816400014051203400070348000c8080c501e404950141d900628403c51036180d1b8581040f0102c59039005171300040490000c00c140101540c0303007620f0303840c0700e51400e0a624110340301d150040401404495000c50700c0c00c0001a5101c0038045c07284550b010352036840d9101c2c90081494100100209614444d4100c2c00d4000c011f10302c010407403419500701003000900e0340e4581700800d01c0c510504224540c0610302c94400551683e02c01100c4000c80400c1e510905001c100106020f190300084c2c03000e2011844100ca00801c41e00300a4855500074062a8000c03e403201b51241403281000340d240440020b500001002079003c4e050141c21030766030040c2c84d107603c0c40c6445400c2c0d506414407800000c00c812a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 612268965 1250 612267715 612267727
    0xa0b031c0327110d061b02100f090803011404020d1d0c03032b20070c06080613050601140c0a0c15020c0d1b0e07080a09021f05070b090c0108091b06 65
    0x85c0c5502144115448007105411032001e0000a5a1100c07600c03041001d06040001c030759030032051390007a5404264440070540c21079081507080c1d0010320807020501d42050b400d1011041002d6070307001c0da000050001840f09207607131105141304e00740004050418040c0c1e00800241074801a1103054180100071900300384000f4009100c200301502c01508001e065a4910441e01c45221a40700102200752160710300000f01340d940c031000c1e5038030703035044520b0b580c002d0480c5a48004119943c00090340700c0c1c41454015402d900b010190304460700403864144d510740c4060303c0750b02001070000013080600721484001110540d941e00c0250788020aa001e00d000c1d0315402e841c0010410b0b40c103007400e00140d0340d000c854107043d16080c0440300c50031b0803110100043c1c40740b00401c80c031140c644603050615030041c101200e4000307403803400b003406598230500c1c60812104101d0380010030010000325000c0c0044001034105111542c00040c087c1801070b1101203950480d1101c1c40b42e0034009051703d00601000d4134211b03280c038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 612270215 1250 612268965 612268973
    0x61404151802070f29070206010308041401170c2104020f040e0a0602070614060f03060c0f040b070b250e09040303090515010503071502060a0b031c0327110d 69
    0x190015800170f00c414040c03540c40701411100f8698589400b4112107210855407283c070203e0303681d01c081c070000c1c1c1b071b56108000a01401209102561010350b041c14504508044881c018070b0029088411288060300031032021000710f11560201d80340400c40b44040101d04040e00012588841444101e00c40e9644007042c0307010ba4000e100e441021500708208544440103800c00070080c01309481174140c010314001c002074140c035101c09100a0400007070b00034641c3d5600c03884000d003a54480780c25401c14000c1407000091202400300100501445540065001c2c20101c1c0006907914417144101caa04031707621441440d1550001e01d41584480840d0b03000642d450300c1c18160003e008000018059001d0514150f12030711441c4c81543c1220b07030940886111030b030f4a506a074203e110705075100005801c41d102150320200300303400c2102072440c0102a902001501540345440e00400907036800465141c0070000003e03404812800321703004c2070302c2d2280c100d503400c1e40d0790101c00c912000141e84690f1003a01100140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 612271465 1250 612270215 612270233
    0x1b0501051801031b050d05130b04110609060f04030213020306030a030c080f0406020c010908013c05040308010f09060308040b070c08190b0c0412030f020c0406140415180207 76
    0xf459482070200c6400d0403189000b0f2041d03001b480350034003e50a084c0801c00e001e51102d005501176402c0070792801c03640c07039540d20382c3e80f440aa04c000a911000901010703003e9610800144000300c6100d0760b40361348a2030351050141d08c04d500b40a691865205204014070360321301059800d0410f516240c071400140f11480d0503c01409005080c6a008001003000306440e50001190007240c00d098885030003044d56046000d090341c02d82074200f0400590344a4002d02080000360401005942007200240c000c01c0c014854100c40080310240c00154501004020a180e16160b0764064a105030050150344d00715142d000d1075110724415000b150728000307108800d0049241000003d8822502034900a039a00340c2c0c48144400400b40550b154480d0b40e000c80c00c00314601048500322614684c18036403040807070300d05403100030443c0307240010340c0034841111420759250b1080001500569030342c0e580c01c808030014842201c10350500305000444250f03043c401f603405158072100c03801c4201c001596a40c0f031441c000883c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 612272715 1250 612271465 612271481
    0x909071206030b010e0f040309050f0d120e150a02060c21011401111518030f0a0207060306060813020613090603060f0e0a120c17030907031b050105180103 68
    0x214a141c248003204001014070b106040303614002c0742d40015100c1000d0710302c1c00c150948006000c503081040c100b0490500300d14002d00314100411010700e0000e55140d241c00d80e9000882d0800003084118400c602e45800301003041c0c0342525108107801e02c03c108902070f5650358060040c3c0780f04031010800340d0125859181d0891091b100e00207031020755966000740d8551460806801c0e000c44c980346854000500c0c00154103c1c40c00350441c0c40780c52a03d807007503001c411003000740600c580c0380000c0004c4200c180b0508000c0507040c0581d80200040d074640070004040b06c805400810400c09164280002100e55070f00344034645804903243d554441d080b00b0246181003060303110f02c1c2304509150001040c44080d50000c09400d586210500c41e129032801c1d03440c0c0b01c1c403030700e0300c001c26900c402841e2107403851141825450240c07240301c1114150b0000943c60b48213410440c0da5100943c07006a0034820070558203140000041c02e43d004000450500001818601a445c0c510501c14100c101c1c88070a0381c460342100c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 612273965 1250 612272715 612272747
    0xb0a0b040e06060307090207110906040e0312010510080c09150d140f0c1e130906080c1306060507080904140403080f010f1203030e120f070b0f0408090907 68
    0x8a00355886080b0388400d000c83c1d5151007401a041c0014942c0740724002c44015076401580105400c0451007082030b001400b40450341c00550380d00006160311000c20050001d1140301941146075898036007007101a5001100c030350104440b0900348102224854280e40c0310000c1110865400450840384425600404003104025800c0101b2003454803416050b0b203004a600042a21031540d40c1e0300104030f280f0901a00315000654038079190b441c0000c0f4800343c80210051104204000d5440d80f100080d5086c5400440e45a00720160141e0345180c811241c00400e00c1400042c41050316005010784240900b140181c9509000120b590661f0b035503a00c400030110b154428040c3d0b9042504005102c4c500803240d40781c041000d0030001c180d404520410708200c581d480341140a52250b590110085d103810316000301c00e4880e0010b940e91856205010708030401c40400d0081d00c80c00740d41003005000300701500842030900903405000c0403d41400480d85040f00c00d884000050700c03a840d0480b00c5040c2c02c0340582c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 612275215 1250 612273965 612273971
    0x191811040b0d080a050a14040503210706090303020c1009050601180e010c0507020a17120f21070e010806100f17150405061012051b070c0e100609030b0a0b04 69
    0x5081c81d40000142450807101d44d0b41800103260310100c10701b140b11358050a40d01d80d1000c0a2006641e00300b00e15030042002481d502418100c0320b58540e410b071083b00c0c800302c02081d00410b62008054041000307000c000d1f0f0040c07041c00039034015214940c4850060180582c20300d8810041002c2c00030300e42013200b102c62020001c00039182031050007000e80d005881d04034414180c12400240c0c00446001111807401440c2c060003440c04800e44105850b803010b5a070a00d445018402d8107507000f015012003204003000c007a0720015191a000041c00381c9032800400e03050004050a000c2c96445114604040348201d040c8101580801c500c02e0341c44000d071310f040b40d01c0801a82c003005151140b581d02c0b4410725205550500c8aa00c80d0000c11680001c0900c000000074502d0a800030241c186802c056004a001c010581c803680c400416500541c2c07000d1000d0750680078101007080308948080440394881e4503020241207440c01c0c04801800ca65442c403014242c4e2801030b0100c0c442c240d19501111034418000c10030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 612276465 1250 612275215 612275227
    0x20a05090604020708120f01050a030c060c03110102070614100305060c0a0207051e030d0e0d02040b01051c0204051002280c05090f041b0513050c070605191811040b0d08 74
    0x4e0414046c08560410b42d120020740001010b003851030441007540c0d40a46041d14440c100f44040f2410305480c4001d030100003605403802c608550a1000f000803a000d40030214468410383e041e1520035801400d094481c020b100d0040000c50f001140303031038102c1c0c0398040c840d5441c004c0040492500105810440d1b0040c4a403100c0d005120414040c4400d00c103040d010f48a02c03400d5000c054581082060701181c00004c5040490018a060391141c000030205040050901101c031041001c0710321583c40300f02d0042d0f40043c00348618a066454010341e0740240c4018840f15002e00c40c004501000c100e2210f081502c40c898000030407090002d07500241c44050b0006450b45030802042e400c01d40300b5541038608000304580d4103640a00101101d0545034040d045111030100300803100b008002c002c00d15011804103110301000981d05011b41801001441011103950710010f020400300ca92140c404805045c2d44170003080000c030b10462542c541d00c0c044800058100802c0007040d1410030021000340050800141 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 612277715 1250 612276465 612276487
    0xa150b0907080106020609070f03030c0218090d09150903150f021c0c02010e060606070317040521120c07151d1b03030714030f070303060e13020a05090604020708 71
    0x102c07070481d0903d60899407251500d41c14a5205c01039800341d4100500032210500110380140501031030241f000d08401122602d02e01604440c60044c0e42225942e004429035248440d800b41c06840604850100c0b071003d54100c10380540003820700c1c4001040007810b000040c0011203035900101001084100039951170352128012480001c0d1444088030382d83c6400007150f88644144200300752060b800f00108415201c0f2810008a078006440071820050204554031400c03243c03e444038065803040c0000c020b0301c0b4002030b40d61a50034840400000c02c2a045c03201c0601007400716500c1d5088101c00d401c1a036607154500b000700c210700030700302c1010b001800d1445510840000da440c8050751044c0f9401c7c1c6400703180c10700390300d54140384402c12070f58141d0060041c280401c01201e800401101e9201c1204c1c6440b01da001a0740094011220941c08240d036030720300b0070070300c10b006e9101644145218440e8400c070b2016400180c030340409008007402000240005003a5480340d42c110381c04950071070007517500c07030400d488 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 612278965 1250 612277715 612277727
    0xc0709020703030f1823010e030406030516020d1b0503030403090510210509150c0406030501050f030a06050406021b0c1519261e1005030a150b0907 65
    0x3401c0b000640f82482500500c4110b110b851a50304a20003400c0004404d038030b41c00ea03a00e002c0109031841d06198200018507070000d108900c1010a040081c41d1124906100902150001040491806518000400440d17400308400c1403c0c3c9040c1000901e08500c804540300440e0303112801000b038400001408185600100c4040072118111003e03113161a400108840000e4200400c981c0056030f03510044031170380560004d0741d016003d60f0403243c0d4a450300480f02a01701064827084154840007034240320340e030340c075000c0c0034050001583d907440103031010b001007940c07841581d4002c0c01c584c4da00d00c0802c0400c222601140c44982c038081d1810140c44222a6041d190003407400603a208070040348540f50700d91204410740780c411407000b48031268040045001e80301c2a903000a601000003200c0001101c07140300c6401640920746183d03014451000b01d40031201912405020b0600c06400c41004101c540d50014096100791b1380031140501c544c1a00000b000940303a61903402e40d000310b003230701001801c60703010b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 612280215 1250 612278965 612278977
    0x10806270a06021806031311040c0e06030709090f0b2b120e03030f0316020a150b06040504090605160801030b070c3e03060c16080c070902 61
    0x510000450005409000c030618010340111a26402404071000803441c0ca5016203045089a041c0c01c22001078140058000c0d131040360300c0820840554090000c0c040d03802d4541042c40801d5500700144644c0040240a4071080140e07a8402c060000000706d00500c904a40b20042c903810105000c0c01c6000c840c1c1c003024220007040b050041100101c51481d1a4060300d0f0044920090b482c940c2e2504032a07158140b1a0130000c01e00020b000c580450714801d61400c0000303060100b1352030700207501c3c2d05040c1d0700074264101360b03011001158020b19400c1d0110f43e041c036a0340542190740c0000a0b4003000c0301e02041440c000c55020a5001d443c0c80490300c1800300c40d4022620944441000302240e40c1a8503080c0c0c2d8107002804040c251421040009021502418800110382c2c0600828040c5040d1032505c2c0c03000713801403031000c0710041e203849000c29041c4c83c600561080700401c4001d4113840ca0540c510114502801c1c07c403018a120760741010f0b0600c0301220442d0111090f6205880a1544840094007e9030041d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 612281465 1250 612280215 612280231
    0xc18010602150c0403080c0f0a0807060e031926090d140a0906120204120507050a060f270f0801050702280201031e1d100b09040308090312010806 64
    0x2c02c1403607a962090b2120b4800c1c00811516410300307045486070040c5401042e1ba0b990588100d90790388446070b10030442c0d103a10780d01c02c1c031540c1e036600c0491500d101036503007486041445910910004440c2d03050301105190045980c039002001d404420b089112061000aa6a00400840c402c0c01101000441d00843c200d1a9071101c1074405d00e9510150014821170700c1c01d0780010b8090800b884803a204038000c01c4c5441c0410009820140c84843c42414008101011291503014040410681c00d003030740d02d5401404e05003000054452001d0001d000ca94080005c00a031202090078409c0040d40324400d0b00290040c24841d10303929484005240c020581583d07141c0161240c602540f5040009141a9401909410040d16a800a0b0b40107602504111480d0001601020400300300a40e061003815800d0f6280354000905c442c1014801b0f0916115001000826042c2180d50303100d03840310b496031600140d151501c51350780d0380c900312000c1c25030040c1a1896030981b5980e00025040f02c00095480c00313a800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 612282715 1250 612281465 612281473
    0xd0e0a06150302181b0d0b0901080115050f2106011e062a021003200f040e0901090606030606080c01020f1b0a080601030317090309030703060b01020c18010602 70
    0x1090044040380c02642c070000b58031415035050060940c00e0901d80c10b0b0000d12502c0010b1903401ca03080c0d440d03119044111420307049640c821401c0d00c54507241244500500300d800c000c109040c001310313540002c1c541502540d4010700440480840c591284003d0301c103031030701c5406a8000304503a031406a4035100e080c4150074004e0f2020400c40c103032001c52003582c8100c80054030b035051911040c400c0c0703604005030002c2e108644410143c1c1c0c13902603110030140d5a00418644e9002447c0d000d10550b4411151030240740c0088140c040c44003180c1e0454000c111001c0d81c1c40004e480b8820307552007810602428496600601c10b038200740d000400c00205170065801d5034840c6007505ca001c030079500126030303c4500440c800480e9200190b07a00303442400c142c01e06514803001d0b01c80720f0802c0d01e0300e40e000c1c80e081081e402200054402d039105180f59400c0242c0c1d070303045055440514508035440c0300103903442c1124007000e05126502c00313140d086a8000c100e01c2901c07000c00790400000300081a10346440f480c0c00d104040c00350003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 612283965 1250 612282715 612282731
    0x9021308010b03033007020706111207080903160902040e010b090a060f09081b1507200a08100902030f0102090a03080f040e010b1c0905030d110d0e0a06 67
    0x5042c0035081514002600841c10711603a00c0d02d41000c036035a4900d50b026044006500d0940e507070003e1850340700c0c144607001802e8043c0342c40340080c00049240c070701c0c2c0f10f150000d940000700344021038112242281c0181d84a1b40381d0b070800f00042d007001c009080e044070030102a1000501d052254000e042201c50400082c1d007039a0f41c4003400d10340341c4680070b4020380c00300702c105061080c103002d4814240d40ca9101d142c5424280d44039000107250070082d840202e411003291709400a140307807403d03182019240c3c58440c01c0c1800c0d07403652100b004445206910f165000f8400c08207926481d134551100007000400d08960042c803c00c4001c00040c005e10a0070b900030700618480707007103041c1d0500856219040241c0342c200340616507214505160070211903100d42500030080087c90246412846018240908440c1d50321000b401e825480d44440301a1810380701c0c20000c1c444041540030064421170345190402140641140c0e4880c0d5003441194102d02100746000300c0c412070790000140c481026442964100b00c500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 612285215 1250 612283965 612283979
    0x2220f0506090603060904110d0f0b070c0210030b1309030810270504060221011404061805060d020a120201030e03030c03010611030c0a0f021807050a0e19090213 71
    0x12180b50740c0300e600035000f0400b08561b424030034000b9a206001e0b5404460324050400000c0c4228041d1400344d03040504004140300b80702e05104c0c85501300041d420035820701d003c154007054500103220070700024180d40d55143d0001c0d4881402410055520040c1000344540e9454041c00d802010350718032309080b03403410340440c0c40910f40011810261860f9410071040e4a2010240c0c00340200410446480d41c00b072110307404540f0303182c111011105180300c0d03a0440b076060400700c80400e000c01c500b0b5846542045410030003e0b0015081031244403103030030081225914000850030108a50600a411030220200001d007150f14042004181d4800d82e000c1c040381880b640c04030740d43d0005a0740031210790400c100410243d0302601d00e14903c00050010380c0c2c10068080c020038141540d07a0415140301e00d074210070004510300b0508080d40484070120744c50240c1803012004100380180f44503c01071104403c0e103000c45590705070107040b0810b0189d03070003c0302c0e0343c0b50004039001c0d400c42c01444038050f0a041c00403c42c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 612286465 1250 612285215 612285217
    0x903051006050a1205010609060b07050d0212071101022401050f0607050d05070201170703060905070f0e010f020102120a0603050c0114030601080402060c030c160f0605030c0c0102220f0506 83
    0x11407005161810031400d10005007501c41300b00804452965a0b4074001450710014020b88004142c0010400e40b21201c0703042003401d00306c425260314115000076008441c0500c0c140d043d143c8a0341c124072415090082c0d000181c0c0b41c43e042c03aa03a00f404400a80c0700485246840c4441416204103680320f12005040000384101c030300900500030a01c0e00a00e07003c41034248104090420240145000b06070b80c112103503103084a00d0f00b13454100020340c48031010b10054109001d0b481d0809090f00e0b191150381c400140092203007035500c076440d04020b0b00b0450188094800d4040d5100d001828101148600344012500000c1c00d03980700441c0c0300d0050015a6030250300138001c3c102c011106100803891540c0d46801118226402003049a201e4424026800039490070406003a031503c200d801007a15210301d4803002c0c00381030640d01c804041d2a40010501580358048240c80d00110704640082d11124504c03011800b82c0290200c420010313800000a43c2e203000303400c3c0c10008031040d00341c200007241c5e10f4000703010305 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 612287715 1250 612286465 612286469
    0xf200c0709020c1608010212060d020612090f0f15060d0804060507020303040312080f011e170c030a0305041a0306061c0e01020a03090605160c121403070903051006 72
    0x9800c014000c000d03410040e00107004841d0b4040c00d40f070100d0804004480400c0c065048190160f5020981c0c0300c501244281031600040701f01c965002c0103400e5030000f0702520030401880c1c130302e842040128116541c10085801140c10980c20b40d15158400c0704060754820031648480b030a104e0042c0400d0702814284210080550080f90a901d890708151060326542d002000c1217805210412000021031950010007600e040b5660350310701c50b0706180721064800b01042e00f1089600c1002c54a060050210000d110212a18515210b202854220300b86082400c001d00b0b20342c0502500c09031004050340600140142c2e2512b08042d07181034001e41700348809020498099400010400c11102c008407500034000390040340000104210030b42106450036a00301c100014042603c440121041000d1030062661001008204801080881d90700809800380024040c00d000d680c2454330100906c03940a4401250703042412a40e03a0902f19002003907c0514401510710380034011002c0307807000e0540500c200b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 612288965 1250 612287715 612287737
    0x16030806040e0a2306041406071809090312020f120a0614060903010f0c030501090b120a060b030a0b150109050306060d080c0106120807030201240e0601090503010f20 73
    0x43d08100955544000d122080e4503200c05518803038030552030711030030083c003886107102e200c03450000301d022845503151080140003001400360412024000184007280f1404840d441c4402050710000360905032a41c0c4c2401503060419800007500c07001d0071914000611440c0c6000650301800d9848481c008100c8149015000e50544000e008202528240e0041c0c480b8034001800080c0343c002d4800500221240d0481143c082529500100400c8000d8440c0200c80c500582e0516048045422555140e4072000d00c000c2003d5650074440040761800c0007110304030790b8000d215410b182441160350b0a903008641d0791a00080141d440030400e810003042880c00741201400c03035030b00001c0940d03402d80340e81c215241e6442d20359030701c9200144075040600b8030601301d40501c000665a80c09410002e081d11001200c064100c0034010b00d078500e114285079214103c1d000d2111410641d2215001200c1360002507200d554903608100031400410355541c408101c0c002035000c4004407001c1c103803c0c05061700461004079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 612290215 1250 612288965 612288973
    0x180a080c1c050a12170f010f0b0721050c03040305071406090102030d0b03032101150f1e09052d0f130e011413060e0303240a0b16030806040e 62
    0x20025508001d032440f16146410140c42c11500e44018000058040386c103154145841390040010006504c5c80300040d007448042a464140030351124a01070907000c1010002040950410300c1d0140b040c4c0c01e07503a154180c00280c0c2d5941d41d0b81d0401c203583c3c9540780030700c402d4003000c10451070b0103140c20303401c44a45810680166042c082c8610140006007104000190140800c001c0d914404901d925103c230402c0c40004105c00c01e5040860000020091180074001d02c50300080c3d01041d40c0c0c0001c00c2000c1c51a400c080382501c210786030313030880d40e250a035440796402c82c0c580d04000324140c40303015a00c0000d80e04040c02e250306004880c2004466003800721b0f8240c11040c09a0042103e030100d41000394040e05000010811800301d031401041c0c10001ca8000c010074003c0d00741002085010b00030b000c0ca8030011130045055041c40d01500801e1209500700b4110400146c6640e43c03140c03200300144004001580034540c640703000c183c0003203040100b9401140080c0000002504900d4140b00e41000010101c0042c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 612291465 1250 612290215 612290233
    0x806071d010c030e0307060507030305090c01080f10090204090524060a051317030702030708060108030d1a03010903030f1104030807060923010f05071e05180a080c1c05 74
    0x19140c074241d080b0260708000200406603000c0e01c0800c20780005148940d241c40e51071045080007801c03924054060340080d0089506581641e84c86486035402c203071100c1d04c0000d180c885010140312900c2951110715107600204000030b01032480d6101d90b1041000c100b104124844110052a0b5200d4020100c0c0d40060144283d1001c68414800f0741021204103140080542e1a5044074100003403505084941c1d510024000381103040034017400d401041050003e0200c0d5042c07001440d2a030142c40c00000c995a0340e00ca0380d071200d24120445191210340035008002020440c00d0003030240a1302d005400f940b074104200f92a004054000b124100c0341c000b030711300b030801c0e90550380c40d8041c00c111107080d12a0707051440460600740038200d00b07100f0318203003400010f00030011500c16020360754024510002d06c05600540c003050018074a5130840d0300041e20300380b940c13034401c228a00e4850507010850381d000301100a0105055100203129120300341c00700e0701d08072218040d081c2c2c0020102c0c00d01004000c0e030011400c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 612292715 1250 612291465 612291467
    0x1050304150c0309020a18230109020702040621050628360618050d121d070f0b0703210f02030f07080a05070504120c0302040608070806071d01 63
    0x25802c0c60151030003041d1001240c00088050900c1c1d00120340b07400030b0520141c6413034010b1041401aa40e004400361404c1d0b590a4038a00c06d00051060300d154070380001d02c090455880381e000c04007a02d140b0b2203640c42c0440d800c146010391201154216181e103e2800031920380e20003e002c0003c0011400c03090003100d80031806910142c103401c507800c070001c001800c1404c81c001c603d13444064000280383c60392051038050300785441030710488101c17140640d119408904c08110040303001a10108142080b082071089528070348010309910f000101c00070400c014007020760384007040160407a55000703080c001c80c68481c81c4070700262140303020040c042501088400c0100c0c00d00c0703150307071040c844030720300042c2c0040e0010b4118240c3e402201d883c18100f001c14108003820703030001060383d08030054000070042894079541c0034080e84500c1c002c10002c07050703808800c0200503140000030083d59010b0401e000c02c0ea030720a00729949240900800c2c0c2140181070000d1649441190302c3c00401c0440c0020000003950000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 612293965 1250 612292715 612292721
    0xf06191511011b020a15051b0310090204140f04050603030913060f15230f09040e0307050102090109060f050301060e03101d0111031314100509060708060105030415 72
    0x1400464070354030707000204005150503000080c5011540c01500e4201a58a40080c5901101e800400707058036000c02c0c022380c045500106030155480f50b110aa481d00c5130300450006c0c02c050360150007640c2c000180414080030302d022251301c6801c103586150741c0796840c04c100002c4e6003013110340a80662051101401c14908031079010302c00c1e111030400081103038440042044c0e14866410501001d8000c405600d42c031640240380800480240c1455640000603c1e1500094400c860212680402c0854144803070f546940c400340c052101da03012203584061300d00c0c24074042d410190509010590303504000600d140201804c2c4c04024965442d03900e5a0700f02601501d81070050a200c1d40c2601c1101d02c44182c42106100e01d0102c035414010450b8404e8030034051170300f5240b540c50b10407800302091061103400111007082414113584070702d09a600b41c0801820b01c0c68440030401110303a550601c0207202d110080420001d000c1c41e01540c8054079a46c1c6e2100654091106071002029a12142d80040d20b41a00b94 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 612295215 1250 612293965 612293987
    0x20d030903061427070519080106030c0305010c09030503091c080a03090606050a06090b0f070c0f03020a050f030d0c0201050903150907050409080708031e0f061915 72
    0x414030591454aa40380c2604071202440b085034141c0d031003400e0008001d42c1507401440c1c07203040d20502060720b83d003914030b0392030744018403900b4006d2143d010320307a60007442d030b004030000f8281c803030001c000443d07403800c042d88201e10511090300c0c03d501e0481c8034122507109000d0b02c1e083d02d070080c0042d03140286c04414407085081103040d0111001402e854580020045c600a0030303030050641c0d0106410399181050742c11210f03542d0040f84108620764003003143ca50015144011a21901c1d03006841c1c4a03d80c01d0f0079554410351000a210600c0300b030b808108514034000d40030a9a0080c0da422480310313280c8003403200c10412401e4403071780742c0d01001d1183c04682c400d00b4181d240c41c0c03040c50441d04003042000440c2c17400241c050305001282d0762400704503c02e00c04218a0008007011501842003240ca919018851b1041d0000584030b00030000004d04500041c0c96540720181c3c00e500354185903c0d00d86881030303e03820240c40c80303841418004007000c40361000326175a000340d45201c0b00031794400c1c3d1400d9003503440d094a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 612296465 1250 612295215 612295217
    0x3030912051504060f0b01020105011d101a0417010203010612021810030b12160e0a1808030105031501180902040b060d0c02070b070c14010c0b091b030a020904020d03 73
    0x800500d401c200b1101c0e1009015134801d03100410180b8841c94880c040d5989541194110380c9840010000107240b130b21003290307098805245a005442d0034460303000358503054201c461040d0929400d01d80d90540c2000820440d085101c800f4203c4244004880c00d0b44400e109841c001950030070300c6a41c46900e07070f00510641003082d4070500d509052002250314001070040740c9020994824802c0801d0400c9142245061005d10203042000b000d034001c3c850301c0c08140590303404000e0840000384407003e81c1c1c1c0500c0d04070100000300c0a01071002d290030b4101c2e601c03d00510b07000b0701850230070080c0720718601940ca040c0c640090025401d480c0a40c034010081c612050145d070701c6a19050358040c951070320f80041c080801c00780800325000b5805d2402038501140342e032000c02004c1042008401040c01031030510207880741008108050f89502004036482c00c11400f01502003401c030814400c6a40c00001c035481c0030800c90f24003102c0049000101034450400d0034020350007042d4580041c2c01403030a410b0380c032078451007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 612297715 1250 612296465 612296473
    0xc050406030c1727070302060f030709080303090d1b0201091802070804030b04030f0216060f14130f140102100b0a1a09041503050a1502041a13050a0303091205 70
    0x44400e004110500079182c10540c80301c00070300c0d0905520090144c0900e1807616005003074491465002c540a0b1103481100c20705c000300400421000c41c40344e2200c40042182104030b03912070074841c08070f07600c4410301c000c00340c080341e03034686004664007400000316400f5070161951600c251420004040c490104c090b18642244d08021480004410b80c000d040551b00920030b0201c80c2c5010b24010f80300090440584040d5442032014011018080c401841504c002c1c1c44c0540c040750242c10203580300c610007000c07030b8101003010034140100042007a22800f1503030010004050175603a000c103e0301140c0c50003c03050041e000340c1d030f0071400000310760480c028058011f40380201c403e81d01c0d002d94004242d012602a50402c0000700280240380c1401901d801c00602045443c0591843c2c1e41c0d15502e405541c0b0050485080c006543e04250322541076034024050686107000290790724000d0b900507400651844050403031080d0101c0c60f07007007480b01581502c0d450f4440c251020304001c031185040d01060412a05445 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 612298965 1250 612297715 612297737
    0x2010213060c0b070309050f0307050c090c0909150102032502010314010b12090c180f0a02040509071d040509012a050306090a02161a060909060105101101060b1c0c050406030c 77
    0x1238200300a10140d0b028401510030505544200320345400040c080030300e18502480806078070360314800c5d2030360061000d2031103252030640000180d055004e40c0d0b8040400418122100180704a12220481901c0c1b00340e0f001c00039546c07103c4642609c0b8000b80900d10a0280600c221070310391805808003600a07406030308585640c82400d00044614a9180b203102c0103442e18800d001d69621182d44054111076040d106504242c208404a4490342004000c1410803a54040c01032000109541d41c50012a01810510061500c0070121340a80700700a10b4810b41580c50010b0a501c03e541a001a190002a0340c0c81e031450300c0342810046042c02c09851414456400c00489800f18541d0004860052080305c14008048024101c128048801032110380250201c40400100c00c0c1d010a91138107503201111000c1512807150340813101e1131800400070b441036180c0600801c0c1080c500380680030340446180d049440028103407200c0700b600c00810308800403c5061000380705590280d0000b201d40405858160035441e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 612300215 1250 612298965 612298993
    0x903070803031303021507050d0f18120e030105060d0201080c1b010605040509010c0f051303050709050609060d0308010b030a0f18020f0303040b04050f0f0303070302010213060c0b07030905 83
    0x341c801d90711810f002a008104008142c1c0510040405c8107440c3c003441d4031860842d1014003a48101400c455006a40b110a00c1c10840302ea444500746228081024200e54180d18050b1581d4100390607141c0881c1d01510b030707208289414081c00e84074080152250740c188205034015507910341c026180014410060216030385102000e26154000c803041800801c50605c0c01044c00b089903809000383c1b100307034108007842d400d0300c0e003200c0e074800750794018682142d43c0c80040c8400b03510340d29140c00040030ba0040351800141d00c00c46400030b134003030399040312036400c40d4032190104801d0a4035034a000b400700305844010070641600c6c1d0040d60780700900120102d00c4000e401c5010007110105076045101440e25540c0e2415030600b201d0411000505038001c51929080804000a0780151b00c1002d1040150050741d28807070f210002c08000c9940003404413612000c0d2441c0117800b0750054013003206018000c078000107050344030b454104042c540012015135181c4541d64100d0140c00e41036000d80751403060760440000c0c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 612301465 1250 612300215 612300217
    0x5060306040e060a09380702120403111905030706050a120518070e0c090f040905060405060a11120619031202070602120901080705130515041502070605030c0903070803 74
    0x142c0403458000800c10524581b011481c2200d02e0007104003803805081c40c1e050031300815180c0d01d214882113001426501c40c0412460889507801c1c6600c03400c17012800000300b1038944180310401d042120f020307501c00391103844803801680c107100e029415071210804001d2503020744014401c1da50585084001005964005000e4800507181810040c0c40c1e00682c1807502c0c2c0500100010305480c14100047d4146030f841544180900792107913210f250001c01c0c0409550340c03940b00c51101940101034400d1441c3c68201175444040c2101c016540604004800e10a01c51450441d101141d41c8412001c140d203038041803000c08180708c42081841802d032080070000c1642448407050041003a4000e0800e14203111000f0f0070701d9010168080d00c03c0c0e00b84031400a42ea00203501c580d020160303191803034a50314204960160000c180c3d100c0740c0c001505120b803490280d01e100060041c2e658107604a600540640812a03a44299102e003100203402800403840303003904c0c640106514800102207800c0789071100703507407821 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 612302715 1250 612301465 612301471
    0xe011b02150a0f29010806010e12190305040f0f05060304120c021201020a0f1106130206070c09051b12190f050a05061f020a082104050d120b0a05060306040e06 70
    0x1e07070000c03c2d804e540d84c82c80030781484003d031020b280144050501c0000a45410040368070301344150145600404540020440412600910350603030000c10305900700030700298414003500b040c41c45c1048011505e1054040070300f0071140050030040c42c56495440303460005c440006050104000301200c1c00160341d9102103048288182070005a44158207807000d0000c0c21140f2250051100e0a003a01041003404154140d1103040c0802d00c100e1908148000742c0e9512034180000c03c0c030344c80000c0104020b401540300d03501c41e10846c850481c404054100003a0f8030301408007180109444880000c0e01c07014690851150f10301a00e1020801f000040303206403d565040f0390b2a4080da540d1810086079103050b00c2451901c408000e003000102d845040002c0d00c0d6654140040c081100004046181d803505140400c2c0b10450601708ac0000c0c280351815680300c030f4403000048001208070409082c090702d548642600420014545110180f92005000b8250001003025038003030394410780c2d40c1d1100414805c1ea88 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 612303965 1250 612302715 612302741
    0x240a080a11090a0908030103061d10090312050c09120309040f151205030a210c05070302010e030a0c0f1416212a03020a06030e011b02150a0f 62
    0xd5081220092000c03542e4014850b2001d1401c0c910310b080401e80a01c203d9040d01e400c400d000c604a540780b401d0140100c0641f204012a1050360350301c080811880c4d0150542610941e2a407072405006034000c42601e205881c0b801c200c11041042102e0762500300c0740107400c2e03504001030b81e0520318980e00044c00c603821900c820520940741c6100c12030300c03203495a100d070142000e41625000701e021610303840c0c0d903030003a8030800703003407007080c80a02d00c02c001c2a5550b0700b245101254241304007883c0f100000c0868018075022005076003040c505131034603c0048151012492960340b42141046261260a26211503500c190703180388500c1039604610304180002d044d000a10510014024a00050215203440054500701d80078581c0380d18000007510307180305a11981a0061010008030300345041d005007042c40c2d100030342c8000e1180d800240c442c1c260b0030144180d0f1a40c00200480c69445254a843c51034086003000141c11041c1743d111713441083c0d0816500003039040c4c0f000401c040d403102220101c03070600d40785207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 612305215 1250 612303965 612303983
    0x1c0b1207140a080118081c0f02070605060108010302031b010903060507050406090603050103030905061b0d0f030b1207091d03071110050a1202030c0f070c03020405010e240a080a 78
    0xc4250802c100b88000030401400200072501c401d860890408030917100007001e690b00012291804003608618020a00a0040030440e0b00500596a0b009602c0700b84204e41c07060402000503c1c039805040d034541205d4018002d85404015071044155107800d040c00d5a0601000c01d501002145507031041f02d00c2140d282d00c5450390b40b4180034000d0103442559001c107041608043c018000079038401e00800440b9815500b4944070030070301003913210414072811103149d0703403181142071403144d035001c90040345880007170b233040102048103001c0c0710080440c01c0103105107601604013000b14100580c84100b4010400c41e042101a1040200314103550003c007058409000034409407601c1d01c2d040920903086459030600d0fa242c000c540780050b0080600d4614880c5899002c0001068030720030a08031051800c1c031145007030ba104001d2522030798005c150301007a8041c9207084004140280c061002d02d0049031280390b40e40e189960004c1c1c10240300703e00100c407608101d050b08001540302041080541e114820f001c51 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 612306465 1250 612305215 612305249
    0x310060e0d150507050d0c090611070e040b09241f060c140c060406171008100203090c0a0602010f0c0305010f03021201090b1608060102031c0b1207 65
    0x9209100c084622031244403504265400214000c10011aa40310154040380c5a0354404066401b40280d602020b4000d06000c11084615882582c1000341e03030b410f44807070305650004041035076100042d00131b0b48071181c160004500070403103801d000340c0d100d42e00320101c0707020300c4410300124401049050311034006548403003804003910310415002000301e0f80810aa45092170590021310000c4140b00c050654510704508001741101848519503041d00a40303125542c5540d040010704196201803010a40018040400d144800010110741101c0302c50009107212103901c00103d0007584007801e000103600c02c09590207980d4a440c50548018101500000383d03440c4802d8110060701d01001d030000803d80303850010b200030329042c059081035175019508224044e9840008a00428034502d000e44007c2d0000c0030450307048211802580c1598169680355a65100d40c401aa900c0c00b0742d00c001c40102c0c0d184040f07072200c0c01b0240e000c46603070301c4000c0001c5008502ca049035824208540c1015001420f85504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 612307715 1250 612306465 612306467
    0x10080c0a1206091a01061b110112061e0302120705241e03040b0a050c160302030c060a0c0f08010b1e07020916020c01090e070809030c030c0105011404140a050c0c03031006 75
    0x88182c1c880c1f801c011000010700a64403001c0d01e51858000e14140325a00601462807142c40d4040c1c0f014010340582103002040848900119000920080784100c081c0385800c98908408140e505c100c40c4007030001c1c0801003c5a050250340056007070076014100c824083c01589490b911a440030280559070710b6680c07400c4ca424501441c601c020500c149031400c010500c41400c41c41021100e00c04810034800000a48515049056100d40c8055030018840c520a1001c1c05409030b1203c0032090080c2c4412003588107514040e0303000361091003070314900001440703c50003000d46002482164040191054981400381e4000b0b00204000d40714010341400109034044501c1c2c04120100d2403001c2400c2c80000985130914009500c00024524420481c52002041c8405d004005840c8102c045901352034803400745c2c0366054000d0900740300300c5e10302e08882c18076800182002c0c0b1074084000002803840a5036030314510000c010f000042d040091298080050043e5820140042e5015005580c2d20740d00030307850b06030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 612308965 1250 612307715 612307727
    0x21040b01090615090b0307030e01050c03090d08090c1302070807060605091e0a1d060103030f0f0509031b010e0d0b0603010506030607080a0b010e0a0303050310080c0a1206091a0106 79
    0x4026031180b00403003d803200f40c119a8490440d0380d0301d040d6603a030740d8802c4402c5020b0081000d480e00d0320341c202010311100100c484051072003801d06004403100d0840b0110111a4450140c0b03078004180c10507520703034003981003000d4601e9056000384009072601a180d40c8100069202403030036680c07140d07500014001d41c0b0740751541c150081c00e0b000c0303411030040748400c0040c40320001070510013071f440e81c8610038010103070043c0451003001c500e0302c00e4510960b501c0c10043d01c1124800200c200082c004000940f10b6130240060b1801c42c3c00140c001d00d00b110041c050641c0142040b00050306100d0740340d24600c603a179101949003200c07600c22411008031341040c4090500f5140c0c081c0180d4800d4204004001246a000e80140e600100711440402d000e44203500594800c24074240440d00b01451000100070300da08030004500484460720906056950341c100e42d40c40350003010780790f0b82c0051524805c10885155400341c65441c0d0003400005032585847d51104043c0b020706d45041d0842f54651700400805030030003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 612310215 1250 612308965 612308969
    0x102010e2419090f0507090516110c03030310030605090705010c15020c0a030804030810030b0c0a11010c0c03090e1905090c03070303020f1e03090621040b010906 71
    0x400501001145011001c40707031030054012200150194001150011107840200d00c00c0d0100074104221485030400c60a0003920b508290b816120703034100040d84403500d2003451310403603450317081c81c003620a00c490031564030290004850440c8143c1c40c912801c0e90701030000318005c86503070480300041880d51510805680004140741029040714004020a981120002203180c0d400000403050100c011403041c000c0c050350608060901c80e0f00c40380000c058000d00e181e8003613802502c2d101000d42d030340704800c603e0740c0040c040203008800f01404203040880001c0504107500c142e05100c8015003800341c6460840e6466014000050343d03080c40c9105160304040c0240161901104841c0d50380b60002c1e038041210001c01020b540150f88600144040074140112606080001e0a03120541d03070b03e05009555918801e48540540a1169020784138103c070440341004948140103141003042400400c08943c1003040080c08000c0000501c0c1d014102590000f44103c1c800c0c8401d141550500d09034404680d00e41d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 612311465 1250 612310215 612310241
    0x50c0903100b060f0a0c050a0308061815040216020303030a0903080603060411010c0c05040e0a06061403070312050c10050f0105040228110708070810060e070809011103090c010201 79
    0x403100520742d54880c101201c0304081003500b01a90352010318002c8038101021070700604680260500c0500f0151301400d030303a0048400300e81c0f50fa80c031034510082c174030113a0040e079441a83c404c4038160a945070900fa000f400302c8094005000f07146100e280c01007811644110340030300c00a0307592040b01040517001907141d0b401103000d90041410746000c0e84c0700c1e40c2da8424510003a040c00000500e02040110003a4540041c0901410a010405c4c0d88101d00740d5800c03281c00211030550810310080340e40a030745c17451a503031b00100500034283d5a246841d509103403e8040d0000d81040010852880d521000304042c00b11b160040b03d00050314038190042102508068210a02c6035004005018007600040d169440d29264080f180c1200c4440b20029651000040c5a01c03170180520040060244030208036502181c1001e4141c0c0d500e140240c031518102c81260280402d82300c0340f51301142115118403010b650012628000280410140c030743c3e0403243d04100d0340c2a03440e40c0410303454121541d0a00802203c4000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 612312715 1250 612311465 612311471
    0x1e0303250207090e0304050406090209151309050606040e07050c070806061e22020903150c040312030e0312010510020f0706121103090105062103030103060b06090301050c090310 78
    0x14a100a441e0b88651080d90300c5541c40300d10080360b002c0c1c14801c442c000d2400904c100b010941c4d030780d0040040d401110440e80300c1d681803082c030010115800c048940f002c182d081552101d03401d08003448020a07000d0000390700014103000108040c080084224050b0303240f522002c2d110030042040d02d2401915030002c0307080d50130100c1480070b5511400b048001c14440c0209001c0303130382c0ca80d42c00b2075035149400300c840840301940301e01c48a440340c0780e0b0300403d02850243e040e076000381c2482007155161102070710f05400c0381c4e03001c2004002084e10000740c441c0b0295a440c010445a04007035481d8074541084202c00c9200c0d1101c00100801d20f0b22001d4001c5105181c0050400020084070b499203501b80f61203540c0900003000c601245140d03031540180c01200d07126241c03a0700c0f41800c0003000c3c000c1008444da28007131241440e680271012200103100403141c41a8004601c0c5a0850b5148005001d03100401d80d007020040c0009010750ba400c2c022103104504646c203041e110000e6400300352400038001c110003a0185 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 612313965 1250 612312715 612312781
    0x309050a06111e0f100f0b010e1e030307240c020c030a030e061612080601020a1721040609020316050a0b090d12110106050a0b0d0504051e0303 63
    0x7601003070400f420000711056454070f1011064076400d028501000d240b25005103200c180b81201c4541c8403807034400e200c03e803c110801c0c1a10040d02e00356200299684c2c031120391121b190084c0b044210f2500c5c030f06400303821f40342084850390314035a601d4600141195991501502515010110b203e03040c0c1000f11480140200c00e0640c004c25102c210a00020707040003940c00148545483d188101c940114005081c1e40240038281055021005596001d0b400a4001e6000c170b0030b150306c000780d04140540c110450100600c2e22200b418070b141c0c80b0808034041c01243e00480c03000529580130b081e00c564040ca0001c1000001d03407041500f440000080050400d501c10b4081c405615140075103800e54040000c030a9580d4000f80005000401d24400145034603908211144015407088440000394510300007404811f848a00704020030080b40100d07001c06200380004860165030382c00064015001c0c4013a9014480e0b01c002d092100403840b0441c200752744c8000180420020b03440c0e016003140c6211065a04124 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 612315215 1250 612313965 612313997
    0xa18050f041109042307050f09010e010e13021c0b0105010306120f05010207050a05150105060f030a2d140a0e0a0b0411030d120e060603060c16020d0309050a06 70
    0x4001e9042440c09024800005400c10580103905001542d800080e0580c5d8442e15000c16550009130195601844c3c07080ea0719101801c01c504820306903141824001d100d60300b444034a02292034020002281803284203e10030141e01d41d455088545030f01200403140d10105810040d000100c181e009034109032038220708000e01102a9060410507501c140c00f40245141402e000f406402200d9015001e0700803601c0040802c80000355800764005070450041184e81c3e01c2080000501540d003c000f60080c081002502c44641544a100c010510951600d05444e84c80b001c85020280025500606543d030441400ba03980500c4020303600071542c28060181c40e84c0004450780702c01420800a24081c80c00001c941081098000090703104805411280c034010031000041c4a0300e0b6404804030041c0c81c0c115441c0c2e0301d5002041691040d00003400400c0540c070f40e8148504030b603201580304480e0b20403401c401001640e8140d0b540c03403030a029507580c0710a80d0400c403c012100034030b503004006100741503541031403807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 612316465 1250 612315215 612315233
    0x1090b0a080d0302132102030607080919081303050322030809010e01111506010f0c0c1a0409110702030d080103050a030e04060504020c1e0c09060904110a18050f04 72
    0x5416529001d071300c5102c103900015805d010b070b82260407421281d49110405000d82180310b800c2c58006c808603091030720354040c1510444c0c429a0200c0381504400b02118114402d17040c0e0b00861446a03890390300d4442d0003480b000c1c100b1003d070000c58082d040090340ca081103281000202d500e800c01d11840c4680c40c82c555481141d4814030500c2414407640c40521151a80180321804168281e070003a07810b410740d20040007004072000c40b100c9010818031404241c0c050307c207214144800d6840840d0240d51800d00c03610303030880c0e501c0d164082e418810410000c1486c4000340100304c8003240121030340b41c480c10382c0d104140c1019820141d150410465030010004a68000f8040c002c0a4150828500f4900d401021034041c00268100680281c000500c1070404100003482c2a4000f5036100301d52100a0008421921607140704151644020341001040c8507242014045400c581b08084078003081c1000e034041503e52181c0d40c48408a680843c5054901c0080ca0103800c0c7d0201d0140c1800c4214941075440581c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 612317715 1250 612316465 612316483
    0xc0f050604081b040b0d0f021509090a0504020301020c071205060c0c0d050a090f180e01020301060e060d06090c08040614060901090902301506060910020c130501090b0a08 75
    0x30000300c003c1405502c407030713102080d485c50181030600e00c0700d41c07800c0142101c031061104071f00400054170b945520225020603202c54610090011074152169000f48001d00b0000e042a0b0b40743d582000812800001041503070000c00b40c200e201d03107040074181880f504112008100004064080020b55205023020881c9035042d80e050806c10703140c11503850111101c0c20150801c1e80101c20140002c680c0346000129150504a1000d090140340449094a42070740000c1c0724840c0400e00b0084104018500301e00074040c0e00960000000c0c1481d65076480d00155284403107020041122001030100340003080c00381442012104c01c08000e2400c000010a22500c0144200c070003450362907090304119a690700d40003110780c04803070303813018041c030041d0403038032058421242540310f44100001c1d508c2082c3e00c8032100b84511002082241000030707450901c0001a09c200380f0030f003180240d03140d460f210b036a00d00d00546074102088001500e507061044820480d4602200c0b40c1c0700c1c402c0e4002c1000405c9000960400c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 612318965 1250 612317715 612317743
    0x9080a02010207050118030206040b250b150f190510020303060306130302240703060905191509020408010209010f020a051f0b04060801090506010e1302090c07020d0c0f05060408 78
    0xc1a0032050141a40b06c600c0e982000394440000140064865200b85c050702407003001202110500c5803001c00c88810203c011070003070542d020100003550480c12048130060814000d04148441c200344000503000c201407103480740c0703041c219480c10701c900d081c1038038170003210b8801e80000c2d032a6050550020303a603408001c0030105991a96180c90007090304c203103c62403004400411444285540040758000300c0001c580800000b850103000142c2c0c0c841c5801740b20b0040b841d401903c0c00e064088100b000180c00d01218a000410016a0006070358007a440184000d110343c400068440c080c0c140010195a07400d06401304542c80b010b80722000c1807022400940340c0602095907900410800c60400c0030305217030480154498502600010025010b400000055216205039106c581c2c03200f00040782c0f0304c0c040c0c03841d498000d00d00501c5001403c0c034040058114200d51a19402c0002c640d0004031507174401c4000325010680d009040050a05007204480900412614907046c5410100c840c4d076071f0142030400c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 612320215 1250 612318965 612318977
    0x50105010b04120b071101022b0903080a0b0105040e0705030402011704020105030a24060206040b090706080c090613091b0e060d180b0403081b180111070e0a0c09080a020102070501 79
    0x10710179402682d19460720302002c0700940d190901442034550300c201d4001903003011180100c0c42d095803046841401040c0754507484506041d121075105100038005c00b0031050501c1401c11020030b203640c0320055a4484c000c941c1c0c6036582c86c1ba140c400108002529543c2d4451a4400424400144c0c1c00a00713407980140c604000250880c150003884424100304456484180c00c00000807503020b6002c26200e10460107103c0030007003500d0741c0030342a580342e50750303c40d502c00142003a0108070724915000046c040124018029414050000350351040c10b801035100f800116991900c103d160300602c540503420880904142c0c41950400700030620038400c00d0317050903205030750780c900801c5011507060032043c03107411500c14042868145805001c0f20401c3d42c030078419220b1850398085a00e00a821903428645c00302410012040e5a0300540e192040001002c1c0d00c1c0c024004041007600030001c1e60f512034040c83d00b000c98076661801014042240c0c039000040d854200e43d01c080c0260360001241012100203113802 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 612321465 1250 612320215 612320221
    0x16230a120605070905040203070c1b0305191401050a0905210a0e030109150c08150303040509040501140c0915030c041a16110405010b030f010e0613060b0304050105010b04120b 77
    0xc40d5840d0351500929807103440402400444ae80c400a0820428420502034000404540c680d81910046100c0180f10b90b0003d000b9050504107424801c1000b40b103443d40204c0d03408004003090945a040754183d1015035030b07599660034414100f001c07102c210000c03885d40115640301d8a10301002d00c203072140390301440b00c01b0313045041d5514254041e2000c1c40e0030200c071400704420116991301801e200700882d000904902c001c1402052620000c492217039000700214900382c50f220502942040c024030650703041d5a900b07503210070801d0b2a9030b400c0c4140b09002c080e0790340780740381000c11907500880c0c03005800040041c070420480400c203030304841c10394041380d009010141c02c031001004144504582119a12038548240301046045101180308900486040c0700e00ea80343e001c83c40382404111540015200e0640040004190b91410140c00000243c5001c40c03e924090140d002d440c500d0f800442440000010082802000e1040f01d015006035550145043d25007403140120180000c0b004d05000500804 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 612322715 1250 612321465 612321467
    0x30706021617120117100203011424030402100c0b040b06040c02120301051c0816110405040b0a1a06070c1701020f1c02090409080702040c080c0a030e16230a12060507 73
    0x80c083c440c086c8000c0a55032507031646805814140008029406030540241c40340c8507604048200d6001b200358150603046507200c2d000c00815030303100c422000a0001d41c0154501140c1140000d62059009012100307850410105020460b0082000131007150840c402181c8440240d0080340c1c1141c0c4e0031a40c5c50000380110074414805402035900400d00316000038450f116a18410070101554055071105116280700400c1c01b0950718201d5000b00401e400b00c1c0015030042d4160300c502d191410003140f400e01c030341d202c8001c107099a000c0354007500c2486481004000d1142a00d03240300c2e205076804000d5003051281107041c07815004603102191028000845510300a407141d056842e070620051050000d0740d841d0902c001c66600000741079000b1800c198840c0105070041040c54020101a4105460040c004c0400c400a00aa480000340790060307030b8003880480c811010010260040500c8540318814480205082d000351090090161100880402003c1c1d01c0204584c615034200001040396621140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 612323965 1250 612322715 612322723
    0x2f0109170f0303010e0106030b10080408071407270c02030f18040920150d0e030d09061b09060c080307050d14060a0f050a03060e030706021617120117 66
    0x1507242040c8800700000907030100c61010141241c40d40c0d20204110450901441800a18041514086180d500206c0c0006a03000300800c00c46002d034030000c044480340461582007075603e510094059101400055000300382130191072169616090070012000c0550019489008051000b41c80f40004240e410405151604400503230038000c0c01040f07442094030300250f00ca410203107000b201800c103003004025420035010340b082041d000c130400c1d03040445283c4246c000c0c2842507142c00315030000740548944008680111803c440c0705100103d00c01c440801c80e02408540008940c080140c146010441c0359080407298044640004516940380d66220068070648200741c605484986001c9001e0382144c070026030b0b81d0040c0011183c0a0105a07104000d0070029130a01601d43d01506d10442000050359540c046000c502076001500c0c00c00195484090407600a101000e295540c080705040400c144520300c0840304a40c11855814605611400210072405000d2000550307007480e00c42e460300390100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 612325215 1250 612323965 612323983
    0x201090f0501150f081b031e030d0f0e101e110301151e1808031902160810020d060308040e0a060e070f0e010e0607080d0f0b060d091e2f010917 63
    0x101842c23031181ea00311746007035881c2d0203c0c0b0008011031030244a030070818582c2c011030313803007555040090003007040c01a00140100404540302400ba003070b160300300d403400c11903005c1c6c6030345240402c1e1f0841d00d0f50b1400b901c01051601c41c000220810943d440040d1511645209094200e0058a85034020300e4000410000800040d0048405031001054080c40300c001001c80c5c00c01c6400036420740c0c02a00064a40b000342d0782a60180c01c0c802d800030000503440711003a50203410204a00000810001d50302e40b9114400d900a40100610314014020008180520700505005051013440ea95191a201e500100025041c1c0c10400c100004004607040f1070f841340e8402000c104004082a5079072155107007141140d4040c00a105840e818814016440b041a00c02e1748100a406400e09241c0034204c05004001c000b040800c4404044450200102d90381740507602d03039524440c00c4802c200014060701842d0503101628035503903c6c1c02c80308540c0b4a69034012000c42c112200e114800000501c5071050301d040640c19 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 612326465 1250 612325215 612325243
    0xb030a060e04051b0f06040b03040c0510020f07080601260c10020a020a1a190306030507060908150c09100302090d12080c03041a070201090f0501150f081b03 69
    0x31041c40b003030207004290003802c4144992403407400407580301881968602121103a0f408213051008205400890b0020f5900510034250075030100d495400040384c005032186aa03005a001118450118070100640c0001e481440d009061a40c90f02c0080000000a81d80c1c0c40740d00c40c0c1040040c54440c0302081281107000006140501c00c001c0404001d54074402c3c07050903407040e42c4590b0005902072166903184070710714030385100310301d03007480c0340390b9145191000e01c604010144d40e2a800000304109010b02d402030640f030741d00c0e140b0091800b08403e2410080107001d55200d240b9a05002031000e0703840c102c1c3d19610381681d05160b00700300c1c51004d030000e000e4088400e40004c50820f100080100c04443e020799140a51102a019100c1c98401955030200b200d0040100c607801c07000d2800300c0404245107034005520310000c104043c0700c0d5110010100280c2c4101c506a45440f20302070440011307881c01020700f401c20208034000e80b8114420740c0e07500c8011015000542001d1500d00c444c0c5040c440364416100c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 612327715 1250 612326465 612326489
    0x110f07080d0f0f0c09150c02120609030d1a130b0604030f0f0506071b03210c0806120c010c080d022a06070c03080708180111040312080403090b030a06 66
    0xd0300b0401c000d0119088000740c41460200c200c01020b0041080c1e01c26242e0450300482c1c0c00820341d01c2603c044251610a0780c1c480061440c00c518454201b02a51240103010091a10b072128481800141c540319820305c0a00c040b888001c07280e60310b030302e0344081406440040200c1c41e000d0702c1020803407034402d070b8101600030308403e80c4d11300038021764094402e901c1e4881c800722800385da2401e80c2181d2203024240c500c032000e0318054406011910404c82607010007400010f00218401c4c0780c1c100d604030342c41100c0c0040030801c1d500400c0711507d0012040140b00708840007400b0401000b0300020105001d00500801c08880410054150304080c2c0c16120080342c01000080203400000c400c4620051a040310f0840d17104483c0010f100502c189408040c032903168a442c0825219600b0a407110400200b421180049881c001ea181d10002d01030b06d40324044201c00c0f94cd9550650070320340900144d0301d0480091102440901000035440078150048801158a498507921103510020160440340c1c09400600e01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 612328965 1250 612327715 612327731
    0x3030a2129010903030801090b01021e0a0515010501050d1107080c1510051c050c090a14060907090e0c0403080d1e0c1202070c36110f07080d 62
    0x440000816581d128501c12900d0a5005400440304200319000c02000a84c6c03450040080c00116049407003a520b050042c1c6400c50380c1c2e0030003501c0810701c2c030307001d0b503a50f500100f007000a101080c042c0400c40c90307000e04490125130500e00040d2242c8250180140c5060340d800c07080600b40205400e0f02c1d4050390018800d6a60100c548a03079940f00000c0b44891800803060000ca40c0c60400d00140c60110b40c0702400c8841101c0803014280d00c0707800850300a692a002e40b04100d10942d031500c544030321490340540002545820f1105030b02078244010b0800340038004031003d000341980c01c600c6000c101d6100d80700c040342580e01c05540d05a20b00031a4801032004001041801039041c0540012160500720441140c00340c07a00310460066401460468000c200c40c3e0000c80210009074001345501805013017004042d0356580105003030704500a240c5400c02d00e10241000c0c01c0482892041038401413498144414000070720342c0e00a511900c05c007071601440020310401040072620644060616982c01009414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 612330215 1250 612328965 612328991
    0x4080105010f0905090a02060d1503081e161b0306020c0105061e0109051018030528030806060901030905060f09010c0c0c05040f090c06020a11010e03030a21 69
    0x582801604500c0c0b24a0720082021489841000c0c80340003224001d000d481019000d0180d20f62080409209070341e120011140c086401610410042d8072815034290fa6400c810080d40221400c0035040a0941040001040074506000e24400c031300c0d0840000302a103101c10070030403c640c0341c80e03000800b0140007064103102d000066000030300c1041c3c142d42c0005115140d000b58030b841c03580120510b000c92403111307091040c2d090034000c11036143d82c142803101c1c0203101c042004066007100e03802140c2035402014021030441c1d10030316140124104103c0e10382c04180311380d805051080000c21a078003031000410550001d03032003a003118001c00d4201058a05505044948221030042214521001d40c00c1010800d202449890040d1005030000b030403440017801d01d806c01000e0034071808004400c2e81c03036410980100c3c0c0c244000398000c0c485900100714150203482d00303404108000f01000d05000600030040820346000c07049800035561843c7c01005142040342580141d089900e0007410cda1070b100b104c8500c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 612331465 1250 612330215 612330221
    0x1060b341a0105010306050109030201020d0e010216030501020304020a050a0f0905190608010902030c06040b04140d050706090612091509051005070917010c050714010603024c050c070308040801 85
    0x38450030f85e018400c2d65120f20042d20880b000b4400240140d100340114892a4840d10240890400500c1910352054040101328000849500160380c141d500005000840c507140d1100c4c0e00600080c2e5045000c1864400a07640d5580e4a20a080f103880d02d481c000b81c06080044071101108081e407104102660312451810b008104a01c4124002d1042428142c07541c941a802c0e038085521001e0174030304c0c007402c00b14043d900600c01000503800108191440e00020302c1401070f4400b400d126611924058501070b0000c000c0491401a21040c1e480c1c401402d020074004515004140c08141012034178210519002e80307891603141c14064500d141c5014407098a9102c1d4045003140e200c007410000380e6810002d074508a810100c07070180401c1003081240005007815042000301c2944030000600795030707250086540c401160408071340c2c0d00b03192408280c041070220b0700013204000d01803031180017a40410500004448031072010b000e04c0004a1a40b02c482c0040150b400555403103203160740c0716541c0b40034890107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 612332715 1250 612331465 612331469
    0x308030106030b040509210d0f240303120228050a0e040e061b0403050105360c04021804020d09020925081b030411010201060b341a01 59
    0x908001c000f900600e41070040034080d88840780600b58011341c070b004850700226010010b485950301404410440301d62840355580c1d0f00d4220b200480c6485441c030b00d0701a060113004c00c014221522284c02c1c0b000c0381d844460b0012200504400590718481040f845e86140b52409a01581c01003456202410b41e0f8080060452004192100c0307045071413550800056412160260750b240d481000050b018030443c90b08210740b407206080b00c40c501900c0c1c0c0c8a03242075a03c02c07510010501800c0d51189503850b2204010240100765204c09080007409034243c80e100e00c07003071001600c0303560007040304a06003a041039030791040f1b040100219603510142841c4800f40640701410380c0708948000000304403180000000e0761032040284042e4105684400075145004050599114000c0301754002d55000b070a4001140030314020400541c21500c1c1c900021309440369038109098040c0140718262550007100c4032601764609041400341c0b1000010704031500125000405408c00e042101100300d40c4002901e6141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 612333965 1250 612332715 612332717
    0xa031505042417060c0d0e1e0c0d080d1a0d030201140c09010203040303050f0910080a110408070302010c020f04290307060c08030402120609010c030f06062a0c0308030106 75
    0x540c0b1541d501d002141c04075a84040c0303070036030401000a0030a504160003040d02070003503407000500300241d5090528081070300030342010018a4076203008144000308000b0b0102801140c0d0140840350a0341e0f01c2201d4040e0302e428110f01030b181d482545110368044203030440e10f040500000300c481d595041c000c0c06815640c40c844507044480000c180c005080c44201c4d04501c0f03042e001903103414915582211140c5c0403110808007680c09100d120210354a914058581180780e98406c03a00381040c00d60001140c44000700d60b20110030401081000f14404103014046a0302400c0c2450000b401e80042160300c101012a1a4054545000502001c42134003080e038007170468510012590010b00b013895942c0f17169000e058080f50700c8042c4400000c007040000d50344184090f0070188c0e150100715800c0e10b001d000b034801d5101c59448020500c5541c0e070500c41e4802002d00304109201c441e140080140c2985842c00d01c2041036a410a4804602100301d016414050f41c0b00340115410f90b500d050400c0305400c02c1c01220 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 612335215 1250 612333965 612334031
    0x10f0e0135060d0803010e0712050a06170d0906050d06080f0307050d050421050a0b04050d110a0f0605091903030c0905011d040218130c1b05030a03150504 68
    0x140c0b403400c1a101d102c0c0d250354001c4000e451a4284500054201c90051088007040060070242d200c50500d40500c60241c0e100764004070701e160607d41e00d14040f517100241200c895000c000414045075000030907004540f01c9081060342e402d60320301044064043e0340c100720007901c5403c000c1e4281540010043c2a100d000d2010b441c110109444122183d00c40c41c440d003650a4a030882070801000122203c0b81030a1084040302c44e14130303503a40c07001c204201c215400c2d40d982d007000820200d00d940142c0c05164060050b80035000280c1240d8400701403050b00b1101800312a940c4000030a035140802c80280c03640d2020746020340038101450001d018041d40c0c4004800910700485c0003c6550203440b1203814088002d07040d082051190003840000c1d001014856400d44400b130351001c00351a000c0b40184c10410755100410442e034401009001e10840041d01e408180c0940b00704c9001c43c074040141c0701c61340400d00e0b010030400158403903113545101a0b000550300a1500c0c000003c0c0340c0001c04108003030403104a1035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 612336465 1250 612335215 612335221
    0x207050c030d08040c15110d0903020a090b0d0f0219080705150901020303070e06040513020c070b0306030303160c0b07050703140c0c012604050f010506030309010f0e0135 75
    0x1c43e09007409a900500c0041102c00500c0b03070602c0020a144c80c060303e4601141009a50140719280420f00d0302007102046a600d418025410078802542c00341100180c1401740380d09200209a10704028500609980070700b80301002190f8070341ca5120055945901c030ba07400e0300d03200c2ca000754076150148100c0d0720030f02c080901da040d4100308406849010348140c001d1801c5603a00c40045d1802004610b44a510032000c0101195942d51000b40e2080001d507124016140d00541080620344a000c5c1c010302480b4005108000b901c0e074000003102ea001c1d18903c200c40507101130038010303070fa01100c4800040014001d1030070400650f0f40301c0045d180e010b000c0d076120100052115200b010902c900c104401242d004242190306550080b225100f070100041000703214420ba084201c032040c002070f2f5084a251300100314a40000000b406040e8200b83c088020314900200700c40040c041406010b80b41052040016503021560301a02c0c0190b05082403e02084e007034500380c0400d00c0345c16084802140800400f81c08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 612337715 1250 612336465 612336467
    0xd11040e03192f01240501020c04020705060415020d02030c0c0d0906020d0f0504170f070e0f010e180d031b050705120310121505010e0f0412050705010207050c030d 72
    0x1103040410f03200c3d0810300741002e8250070501120240740c40003c480d03403203101c501a04003401002c02d5040001d4810145030304c1c02c2070002420070f1482c0710700d0343c4214010f000c04d0300031501c042051500b1640c001042c0604225001c1003502074010020982201480401040b10b445203800040006a13002e8050b618200070f51a01070310122000d004000c0164841c030040c4480760f004090640144100741045402c1641c3c5403880e80741d8030800040d20006400800601004440401c0868044e140c612114041454600c80010080c8014825100d8144a10b40410545848642211007002c51002603a26840f003018014014110312081205003551008843d41c24a108800b40d504840c0c2c004040c0c06001100340d1088041e410140490060f5102040006442d4400181048190f40f041101180c0210303002001401c544050f0701c002c1d0780c40e2141c3c0401c00d00c60003650800e40e000707034420400e4816100100b0211440c0c010f00000810380d42c4001000c10074004002840c1140100440403918000c00742c80d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 612338965 1250 612337715 612337727
    0x100c0203090f0916050f0403140c10050c1b0d0501021219060501200715030c0e010804020d060c2a02030708010b06250204140601020c0114090d11040e0319 68
    0x364251301801040344010f038075101d00f006007070440a138045141000e44036201d04c0d8181d000c40c109034545901104213041a418404243e030040c0c00141000d40c2407130950103020b40c95900000713603080b03413203903140c407156040d0b640c4000a4000d6400c18021500e4140410303082649060907210092481484041c41800e03003004d02030700c4241c0c0c0040e500c242442c1c0c03c040ba80700d030382000c100c9016620700070600046170141050f42d041040e41c2e04d5035030101c0c84104010000d0840e16064030014108980c80d410000580c81e00c5607481403c6500c080f00140300400000c4c21184a111426940b140c1da036006655080c502c1040400000d90340220180c0e20041c0d90380c181c1c1402c0703c4040f0f54150300070500b4000000c941d00c0306100406c084001c0100c0394244401c6900103001c494400c12480008400318060020b15681040701c0d0380354450030700301025440310604000702103014441c2454425003164140780d0400080000110b00c2610140092103155012400d0644030740100d410b5a00248203040804100d510504e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 612340215 1250 612338965 612338971
    0x30109090c17071202120d021006050a050a0501050d0f020c03090102070e040b1314060a050103030f0206040819020109080c06040506310311150711060f010501080405100c0203090f09 80
    0x2400910f181032600d0403c0d880b0002540043e40d00514a16076840c124000340040046902550b024148525100880108507075982e080b00303024a91184080c0051b441e480000e009131102400c2494440c007498020a0140205002c400c400300d002140c0181d000f1400005000e207078000340c0a440e601900c548815404500444025082041d42c4011440c0c032005403101c1c02c003d5001c2c0c07100c54440d1151000c21072820509840304c003982982c0d04010008c0c11350003d03406591310300c2413016291030300303094481400c1c40c0100c0c100002c800d140c400845023841d00135444251100ea10a1010780c0b40c0003007410158480038101c17026074140c013950f800640709042c1d0340560100c10320700003032440d24000c090b48079402e047c04561044003030041d440d01c84040010200001e03569916800010181407a0281c00240310400081103d1981e034080ca080c041f1f104c00141d03490341942c0d403e02c0c20002e55506c034103002d441c0c81c802018201c01e0b5072910b080b0740d1880b54040018000320303105840302c41c9240c0d641018407180000c11 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 612341465 1250 612340215 612340259
    0x10210203090601120503070c0f0e072c030c090103050a21021002160b1303020705010f080a0b1809100b0604030803060d080904060b03010806070801030b2802030109090c 74
    0x340184803401c04c41c03940c0c01100380540112400c1c41c10981e100c0218203815004040c001240c03680402a450018608607071100c00c0f86060414055600c1021588100043c00c83d1103894a116020401d51010091981c5400000f043d0180c5965603042558490f8140b04080c0c4001c60314110003c0201f500c01070443d0242860341c020800d914041c4503a1000b50460801102002e01035040e90f00820b660761912400b815200c41602101403051402a140070955441305040c4446015403060b901d810070030895010600440c041100b008540002d102903901e00c17031071210f10342c1d00402d0101e841000500d0a141c0f83c8104420041e00200000b04070b05030103948001040d10408000185072420300c044040040d600c103403595814001d00307200107800c1d540140c001411004000c401000441d0702000400c1c1c0000b07103410120555410340d1250400414011700040010145084030412004468860005050241011910ba503114904c0713502170101000203031b503c81d10440011550802a1001b80925490 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 612342715 1250 612341465 612341473
    0x2180405091204120614010306020a030b220e030405031912080609010902090a0f06030915110714030f0d0605030d09140f03010902060703020102040e0a110405040f0b1021020309 78
    0xe0640e043c00e80c42c04e01d160807981207481e211b6a00c2000400c400450185214650140e21030a258000404803034040311098801c19401904a00f2009c05695020800054032804100c400050180d54a503101e80d07030059030035200b102004000f100041c40202c444074031901c612001c107408542e046411a00540d42e6907400b24120004100c0007100c0e5008259100000e440254101e40d02c25940d4540752050b8410740121b80c54480000401c4400c44407880c0403c180d141c01c0041c5600907130034288601038100020310310740c0400c45042c0b00340700400a981d55001b068048955400000800038081c02c503d1185134004d00c03031700c00d8070034069004002c914155290851041001c140c0388041003020822105060b402d956140195805030301c4000040c4143c9001c0d4001603942d6241c060f07000758110000300b1906a40b45450416030700f2801031001c440c100c600442c0c0128200c4603c0f40540010640c1d207000550140b01c1d08043e00b402a00206911035661001140c902102080e0940009070700c42102c1c00d16280d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 612343965 1250 612342715 612342719
    0xb0306010807110c120609010b03062a071709040e01050403082d0103080903060603071809060204080f0c040507030c0c39030516030816051002180405091204 69
    0x44503d90603400c07250701104581840e4641c1000c2130ba101c2c0c40400c040c07016000001046500c03d024000c2804801050300200b445243c580380c41d8090b8a503247d10903001100510401080400038801d4541e5190400103c190180071031100c011558088040300c0d010740d0408082450401042c0701d003a11458050b1261034040d07036141c80f000038010459108003405840035072424441d080300c0008038043d6120b180380c41d54a030740040c101880c151004203101d1090f446000180140c01c5d0644020703691000b00c540210310104685803032006030146400c241c07620300c2040d0180c45d000740005140003446070140e80401003611503980480c20398192180100208440583c8030300020304402442c40d002115403200e003126048104507100158035a043e50b001580e0080052007401001d20003035500d4980c40c0080401680b17984d41e0106c0f90300610340c028000c68400d43c80c1e04140007051000054820030000115550480409107412844c0d000c135881340101d03c0d00000491103a00010102a1307013840c0080142814 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 612345215 1250 612343965 612343967
    0x190909060b09010c0209090f010c0207090e0609071e120b041104060b0901050d240e0a090b0c090a0b130608010504060515031509100503100c0504090b0a0f06080f010b0306010807 78
    0x800517102010301c0c42313005044440404280310301903800e1826400f4203031151a01c0081c505403000340c004441c182d08000c0c140720181c00009500800c440644010200409009200d04425603290b402091110800515042080316481c441403065204150b0b0300c40d80100300c0188402c80b00203002e40300046404004400c42980074801500c40302869403404240c0142040c0034100c00c0d40a940745607007030900c445040c8518800602c0e425801494030804011164003612604550900940f8010040e20b00080c402c0740b0b6143c8181640146c02c0c40e000140d03072038441c046e4104819035948101c1c4005503c06001040a02c4c0902401003106d400030141c9000e10f41c011100d00040e40050000d9440d900320070020601d6456004c2140d100f64402d4000394070941c40c107024581809a2403c40940c1c04e450302200101e84c0d5000002d0b942034691103040026601c1000012525070740c070079001803998810342c1000265603039120050030b1080c2020b1079138040e40e0b603850a40b84e86502040c2d0324603020820920001d480a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 612346465 1250 612345215 612345229
    0xb090109081b19050d080a0203040507060311091f11070503030a080601090f0909020f04021201061b060204091b0c050307031202090405090c1207030308041205190909060b09010c02 79
    0xd282c01c1c1090314854142102890002e40c101802110f454001e018010b0b2010340040f28554420795001d0309515610740b5569143d212816030143d038090641da04d0008041c8031a030010b4034102040034007440307a841c0c44c95048802452018ad15000041c01060b580c0e144e100001c00c01d481103640150003507050280d11071060f03401010082149042096407600080d803022130039a818000c0050074000105030f07269005200013074104480507070080d80104141400310070030190703240c1100c06034a0281002422003400c00414a150303c4090080c500224011840000980c480c0d0f00ac1c2a802c0140b4140e25412003042d540e0b030304690000340040e041401351a010900648903080303000c085000c01403820080305c0004084a80940e6241815403041c8041e200e80d040103008104044518001007021500e16940280051f0000704002e00c5056942440041c01c0c0c0102c0541d0f409076103a0002a6442c503500800410380c0703010307110745c000e4a82000c41c0000c080380d111003241c140f580180d40321404850a6000c0c0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 612347715 1250 612346465 612346507
    0xb0d08030408160f0b0601080a0b0d113d0908030d1509050406020d0605041e1a03060405150c0f0304060e0f01020301090204170c010f260709030b09010908 68
    0x342880340340c05030000407070700f40742140d038103204400780d11741030901c1000108440710003402020801e25000300e007072003503030340b2260001c400b41c0c0200d158901e01f1000700803400314070703c03403040c82c08a0120361442c0099403400c0320307058948100f000000d1801c4651030011550030000e0b02c41c00c0c20039041008445d000031005d030030440000086403181c0c00c040355202d10b80e0f01260401c890503640f20364081218007200e095401140001e00c0304070340038043e10907140c0006504207042e00000d00c10503941c108815a07000711071a01103c0917802002c0d02c445285c241080c60311150056a80708440c0030500018140800140a443c2124143c00c29241180d0321550f80100400118520304118410950711555515003400154040e00500700c0168543d0f1a022080c2e520460301007044809400c1800c02d0f06542c1d0b441202e003010440185000b441c0480c2e0f0508000801201020399140824041c040000d016003200559040f02e1281c0c41c0005113550380709010313003260700c041001401000f0821030701c0e032075154013090000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 612348965 1250 612347715 612347737
    0x209090a080a082e05130e0a1214070c050d0203030c1e01321003150903080915010e09070b1305010206090d050f0f0f0c100b0d08030408 60
    0x381203840c6480d540381540040c00d140001072614000c0104542c0684483d585a44d100c03c140d240110740151540d0441401c0d0155900601c0b10b494985449045c3d50006181c00740c0703820540311f40b0400b50410030340310303000000070b280401c43c01206003102e0b4080000311038200e9040038150800d20308240c04c11226080d202001d90b40340c4414041081e0154050011400c00580c02e000c451100c4540c0e580c41e829140000701c5c120032240c0031700e900380c00b020b035501a5038003203100011800741c1ca81d600030152486e00c26540001d00440c00a100440c4001d1450707115400701030017a11445441c0d9280b100c0e442d40c8001c4c611406120102c0352004002040441e402190401c43e06000c0d1021280c41d40b5600703003240c0100041001c01c0340701c084204815601445a00e401410b8080989140502814003401d184034200d5500100d800c0043c241c40b04601c150141c940034807000741c1095480103450701841c0c0c6c2e0f54070090005201490134101086914100c0c3c10706249580c80718101341180d0300c1d92200d810941101400315 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 612350215 1250 612348965 612348973
    0x20030103170a0c02040203070c0b091506090402040207080f030103020f060c03070b0702011805100507030204080307110d020a031a061c0308040203071a0a030507020a02060f07030e1e0114031003020909 88
    0x340042c1d4581c000707188110040d036201070304003001c5e007071088070900050180039050f04933491005040448000095000e00e0070b8441402d103850b20310100d0003c5c410700c1c102401060001c05c030750040746400c10065048900072611001e480950b9001c20202e0310407000205103e9001300074400004690300e0203554440e40714000085d1202200da0036591110607060211001d4000095920140fa52441540d4201c0d459180441c02c00f800d180750b203076882c49002400383c07511851484424003070b96180c600101d0340e5800b41c0725000e4a07590389051491038a0000340480051500400a001ca04200401056005440954002d14130554034242d070305030805841a86c0501030804041060003940c400c40ca04500002216680c1d001105001411503034058410000c40d00108215809a554003042e10170480c20304021319640c0401d8501034500d500c4423001560001c0703501c2c00c12000050350442c2c040a0769000e0725801c040e04900d201000d854030085500084c1000c0170302092016040842c181580400b00340122 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 612351465 1250 612350215 612350237
    0x91a010f090302133905030414011b031b08070e120a050f060a09020d1502120901020d0b061201170a080310050a060806010f050c0304051320030103170a 67
    0x101e01090941240c4501d40713a2a04071585945c10f0309200c4485404d50350714100c1d44407080c60b0401200000008244080090120100b009e1241d03441c259945000000001c0103a001086103412a0303071542408000032074034010f440298a09100040c01100140c6d5550000340e0303603401c00550381020306100c0035400c440040d8050161181c1009040380e00c80c0610000c2441441d00f2100c0307464400001c00c40c00e5481d05201c0300100588815045000e0f0640c05011928814407010904000f4040c040d00100303502c0441003803111484040d401402c0007802c21a0521045c0301660600840c0d10034074456482103d900c80042100300300c01050458803031034450a031400b01540345c0700c0c0c0440d41c2013a10300c0c480d0440004001c118520303102c2c010b1302c01041641000c1001d8600b1034000b0b4050109901c100c4140308000a014034031030810b104513070191200034240000c810041000c0402441008080350400341c0c1541180a1900d02c0c5096a040313a41c00050b02c1d2524042a82c51650394204100c0c80d4140082c1e0512 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 612352715 1250 612351465 612351469
    0xa0e04110d05090334080d290405010902040509041b0b0d0212100612091b03150b0301021614010b120a0c0501110a1b15090e01091a010f090302 63
    0x200d500400d414001180c44070450240e505d002841d140042c3c0600c00010501d4041c0c202440b890f035886604090826201c0071101d4120000d8201c140e111350443c0320440104010103d17552000280c49030964040007160707213a0a00d50b00300c0c070583c00741d49d601c0115100024000340d51001003c4586054052440b589580c6003000c001c00e81202d50386441268010405e00311000c4450075090b80004e21400c103c1c0218a04080030701006c089020f64400c80b500c030030040e0240300e803401130601407071050040803428541d00d08100e0b10030082c0f040000385103420f00c8000021807505000361510506030442032103044090303903103c8108001610641c0060354079140b100c101c3d503407181d0740000083c0d80e4074007a020b000820b00d0819800071300d5822003414000060075030301c0c5440d00005d486030040d0b03101c550900d0b100884181e00070307034a0144e44023030090390400000000342540840c0d0042142c0310b03080b1101c401d980320040a4141c41681079171054510080c20b4010140d0700ca9071016030003280701c0c100140074036201c0d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 612353965 1250 612352715 612352721
    0x6090607060e0a120c0f03120603020a120b01140307060f022d010c0c170703050d0f0603170307080a0b1c050105060f010305060306040602210f04030906050a0e04110d 73
    0x1d403854490f0400004601031001d0642813650342403440ca482100c144060382c5d03200075480d400318080c007041644070751042003654581c864005507400900000070f041c1d9036060450000b41c02902258901d252070000210a0300d4020b01040421009010340310307050525800703c1e1401c000a180b50118852020081e443d120b550352024034480410280c5c0c0c0030420180724a600352107109244004000c22080054042201440c150f1120103101a56070340d648040c1c101107609000702d61142e0301d454604000c60f00521300300d500c42c0003141e11640c0281d0480e444822200c04a00048501c031010528040c005100700b1003d81c01011079820041c0807449021450100d900c2c130707282501013180c55a5441062000c5403800c03003800c140c0c40009203818071052812001081d200c0c031000d0801810707a50003150000841c10551181d18410b41c80004030701c034914180c0e09140007040709490540101d001d0400201d0070a10680c101d4004039490b840d5407290343c6190b01800002d101140205611030424002290781c540300340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 612355215 1250 612353965 612353981
    0x111c0b0f04021206060904080a030906061d0709060c060506121e12040303090311030c12031215011e05041205010f0c0c17030406090c0e15120c0609060706 68
    0x4a0300403145014810f02c4490034010f00c101e4101e511400400a19603142410749922075849012241c868405600c1a0082c03c80b4100040440703061000c00b182c80311003d80c4100051041109052a540312020300b580c1d102c174507000c2d000000b0b503194080b4000ca08950003090300450090f00940c2900c14401c41642401054104101c1c505040e600d00501d600f000c001143c045441ca00300c0603d041c0c599503016165002500c8002c000b4060b0040c0d40c042070340c1c04e000140b20f1007000380030108028001d82046807250300800d4200300640443d400f2070b070500d84035446802211010b85071010320001c101c00c200d103460380301c88980040000c10000403905041c40000b41e1a81c074842d000100d80d00008aa91400b40d0740303100071070020070180e8150680840c0340608036812600c41c5c0c0b4480c1e82e4a03101c41c1062009001c0c0900050a408e20b661000200b80140c5046c05103e003981e1059241d40310030340c000b0042c55039145a01c25aaa40c840c4400c040c9a240c81001030141500081846192075010f5603110240e80c03040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 612356465 1250 612355215 612355231
    0x70b0a03051005041a091009020a2a17181009050307050f0d03140408011e050f10051c0c1508070302040b0a0e0303120903040612020403111c0b 63
    0x214140442c00d00350000da070000c2e003802c90341400507041009045031900f101c0e0035154030811210011031000d0b842c0340c40d0400540340c0170b4425903494000860152488032902001440c4003601e61910b942003c44094200b02c0744da00c01c1c03485000400c0d00d00c068400350061884007540303002451110703106540d041121301c0b504940e61140b0100c6898071003014140398075a030196000b00c10410101c815980d440b4403440300f465150814402960142c5117034029406143c10081c4190b00e0810203c1c041d2042072250501e0200c180d4060000e0b80c0c4415002860b01000d44645040b5050201c06200c249400491052038480300100d464641015032a14204008581d20941e861403285c00301164186d4008409680151103041c250f1130140b4080e21191180b1501030f510017002811034001000360b80a004841c4600760940140d61103040c041c0e1082c2c0c60394000e01c291000b190203800e0745001041c1d280281e80c00c6136004074001d604d000c00c010501490080314691114400e10041d642c0e00001e2507030748100c1c0185c0b21 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 612357715 1250 612356465 612356471
    0x5040b060315092503050f0a06050a0902030703020f030c06041d090a030f0311070b0709080c1206060621090a031d03061b0c07081f0903050f03040203070b0a03 70
    0x2103001818202030a2448207001030080804011405078001562185500140c2206816001075030008668101c2500001e000f0301500c0464820f01d03800040000750a406040200829260302d40070604540c0c52240080d00768002950410140c9404202401008409405d0342d800a003807c001a00d02c1d441504100e003c031039542c0c0119402c405000d00310754000703c59002000303100007030380f00503117010f5001c0898020591900c110943e00c0410394182c5259070303400300c1c109485041811019080c141940150002445003050087c05031030f00d42c3c481c640602c50300020301803d4440c00244451507201548480c0007500040403200c116075401e004900c078a070244050036015000346002024954900090100f03c0b2410b441107881d43c3d000300d1071310740081450140903061620740402c03c605015200000340b4074080c4c0f0100007201c4a010901d030300075640c400342100f040c900c100c40360412212141b0000c0e002560901c103418010319803500454210780020b007181d0b03045548001155556025142c503d0001e40c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 612358965 1250 612357715 612357721
    0x60f0609060320030723060f0a030209010e1c03110c0a1215020301050f060a02120c0c0312040803030f130c060e01030b0d0203030910180b03010f061403010b07060f05040b 75
    0xc02407180012002d0132000340143c00d11305444200c8607020341c2021444030900d00710100c0a80d0360710049403902482c1500c91078503094481c902034002d400c00d9200501045240082940c0c500e0b08010b05415801120a0000c418000740c07030840e400c26090800040911819412451a07920090600c008103015002c0b00304d051028070702054240808515802c00c280103100610080d03460455210704000190348898132819450001c80c500f00042d980c80030720348800100d081c140c1c0c001184000d10302105904403001d03120035103180b0040d44101c3c420b25007982c1003400802c1c100890406101d40146c003035820040001415100c1400c2e400040d0721081c04643c03c01502c5006503014028100f0090085070203070030711030300e94011a440b0300c11207008900c81e080310400903940c2ca02440c01180c2030014071880101303ca44030541c800190b0300c00c1c0505148028050f030000b422511501c00083d00101504050382076034a0b00581c40141e410154080302d0340b076111007485040020621440780328074010841039140c0c5c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 612360215 1250 612358965 612359003
    0xb01080706080403020d080411090415060e2224060e070519050f0d140708101d0408251b1d061f0f1205060904060f06090603 55
    0x880550007102809100b10410010940100704290044194200804190b444d40341a0104a0300000140d0340034a025003800180f0541e041051802d9808901c20080c480d19404500b89006088443c8014403c042c200c1d504401c4095005194407071080203031086811020041d47c00c440036801d040c20000f81e80310b504003d185010400c894000c045828103a1030070704404000385804d51303000c0904c42480b030001441c0f040070a032901140c8130808004e0080000008100c07200e425a0340130740f1640c0002d80082c01040c117141e50102441b045550324812100c920344200c070081200140148203135138200c418007081c5004440c0030001c2000e0111903004a6605106140170f605150000c9407a40411401102c1030051255462000f822040c2c0c00d00031224550fa501c2c000f41c400c0110902075080b20100c0000200d03080d0700019000d40720a500c2d1510005c3c1d1804800c01400c44004030341982d4007071286004180411010340c000e0400c0401c117140401c103aa12541c4000a40d10300f0b6100715614550030214000310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 612361465 1250 612360215 612360223
    0xa030b01021c0807140904060f0801140105030a0f020607200109060201020c0d050c0708120715050601090311030a0b0c040503061509240a03080405040e010608060c090f06070b0108 79
    0x5508020382c011032080000c98000d090000084c070600c2031010400020000c90262402d481d6011001042400f035a5260510b1038240d0400e4405c0d8a076640c00e103c3d80c411720403414221281681c0c000f6000381071101c0d0b6505c500040c640251000c0c0c1e005a070410a440100d032480e405140b40c4081c100380240e030709240100040500c904d5502c0103085901c1804000d4a000c000708160003110502e14000d83c8500d0a0795101c0d00f403a45640c0503003614811f02d07980740d05c1807032140c0241500c14016204801d165050760240001d54104481d194001000c410040c0001081400070b50605003001d01160302c5040e5655903114a01ca056a07141207505012804204901d000c20400c0c0c0c0c00758401d0849101c8142110115004441c09070007a000d241845c0c102d61000866a014400d810300001c1400000d80e959042c030b09029807180c003420f401a402c14a12031401d4005001e108110340c24130300102240d54942c00b6083c041c0d0025108540e0103402021068195520b8901030006c0c030b409100044000e5142003499490 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 612362715 1250 612361465 612361483
    0xb220602121b090420070302061605090603010e0c0705070e1f0807141f1e030902090a0e01020702130e150c030105061c0f090b2a09150a030b0102 64
    0x1045000c0c40c1e00042c000006071000760340300382d07004580c9003104462a090b10700b5103c102d140100c03001c00c0c0c6c00c080c107a00064007170003107000098684524003140001c55140c816090700a8001000700010001d074030302e100609030310480e25000c041c00c2040a40d0341501703021465100d811512046402d2004088000c1202410300707c1948441060070f2800c4401d5841e440d00d0300c504000c40300c0341d0726000450380f02d04003d090b80c90410780f158014142003d1014203491400544041070240801944041e607000303215107281140c006198030001d0b0754000f40c2c0c2c00940305030802c0340c8181d5028410100182c94034002c05d60403582c0b118006c18900c0817110500d00d00000800340b44000741c4200305000903200c1c0803040781c2c107446080d54110340c0c038040903d4180207803844141c07103140c5500d0445c00d41c298030b0080c0e10158050f882082100303155192081c80c1128040b00e40348a20610221113144282c14860400901482c040500100c000c0c84a00007404800e41204540401003516820040401d40c1d041c080d070b02e2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 612363965 1250 612362715 612362731
    0x1060311062a150a0603050613050606090c130608061801120305090315091006170c01120e0607050c010e01050c0d150512071703160b22060212 63
    0x10a0402d554a054911041c803022410030000c181c0e0035a440c04000c0c807100b50040a6035404910b181802e1001c0e40040c01580320030b4a180c000d41010480c180d20180c0079610040d00207008100c81d881d404100f0041400190800202c038500b00031100b115459000c8000042c6156220f08065160840500040c00c00085070289800e01c100010f010b24070f10344e818040d42d10b4041c035001d511251581c001c00d1401c5800c0440b118248034000422011400018441903650340e500c0c1f00f0300110b40d491214000900d00803c00160a8020050000c0c4075480351100c0c040080740b0b8030010640481c1800e0550030301105a411500040d000a8034008070082401358102130b8400074001c105c075207030211861103280104150006055201e004a045481c81d000020014080050409248110a07510b5070360342e2042c0e1181c8240b0004e40042c5016080f03020080c1e8440c0c0c40002c0c00fa005840059540540400c0000c284109580d40300f1510000e00800d82030b18203199116440c0180c2c0c07580d0700901c5407440000103010305 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 612365215 1250 612363965 612363967
    0x20907020c0909030a02061e0c0a03021204080403030e0a27110c03130608010e060402070515160306080a05030403081e1306140a0e040f0e01020d02030709080f062212020106031106 79
    0xd4000002601550341c02707031020070580e0705c030b105070181203011303204594420f503050700300500b808140901c410082049921030748840703018401381424002c14500c203110f0b440c2407035007180340c159944c1207001040c65088040040000c5002e0b9015800000b600440001c200300c0d40081114500d00450826141c060161800c1c1a000b56150045c00e00810400a103c035000c0d98001c2003290410100f0030981085036000c170794400341c44c42c0c600300b60304224128005c1500043e04000303002a85100104000e048035030401c0c0610314040c00c40d01c030410f42d0b40c44144007007180c15100441581d0103100d48003600d184156010805c09242c50420000c0c28059509507107401651b0400030715107026001403400f80c4540003550003244450704112098000c000b1034031160703030550000031000e15140807035004521940c2c082c1caa441c2030b1919a441740ea45c603540b01401032840d0b402000802e003510040314508508402c18542c0fa02960a0b550f2130a981d00c9a0700c3c20b810240c0c0d1980d1062081105801c2c43c1d11084400355401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 612366465 1250 612365215 612365251
    0xd09050904050c1c021e090c0f03010e04022d030601060f0c02010e010504090c030203060a0906060c0312060506160605062403060a0506070c090c0302030403080103020907020c0909030a0206 83
    0x9503140c0a45052041c415000c0c081c4500d41d0135501da2182c0390068005003024080854800b4262411601c45005881920940e0014009440c440f003600c00c8560340d00304403070550f070a2030541040c403040a04140c2c0c4c01014001040c00c2c0c140189185007540e03000f6040c90344a452a41d06141c0b6001042c0c20007400d000d4130740110032020790701880e1130115540900e404058448c40c4c0b00180c03400d1041d034101c1c081550070001000590b5803d60015030148906441104c1c590b0390b15a55601240c1d41d0703000c1c0d000003c81e00812040840d11900100000d803566400028000e0341c2d036030004903a42d02030508001607000c26138480c0300f4000244201c0780c1c00081501d800e01d4902c0c07428100c0d070a0320441e2140c09036401e03020004c1012034803146e0610300a0400030b07008039a2000da81c00c0515880042c1d100e2031122904101c0c2503114644203000b0b03680103070390549a42da03140c2d00316820401d044200400c0c4000318410140e06d86220b94802824601405841024544da00255000241088001840180404203000310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 612367715 1250 612366465 612366473
    0x3190309020d020d0f080301060509031506010c08070c08031206040e0d12091b03110a060513030b040321051b07051b120d05130e1501030513080c0d09050904 69
    0x442d00c00294102c6288101001d01e00c0c0460280004002c042c0280c0c0700407002140c0c681d006402443c00c01c400305c040745c004141d201c443c962240001c0b0398140c00103400d56099400141c6200180421506c0b525070070a07900d480c0c1c52160b00e0350300030f88002c140c01c01501d01402400c2c2054801c03081c0d41250007000d03010304d5500321000b038170510b01c4100700388181d03075140000e00922420001546002c01d0440c04164865a2401d100f07000c0601c0203a5544900c40c2c40c280040d100b8010780481d00218050f000a5240500e1900c5900c06120014800d40500102d50300842200d00c000b100100d0704100354130005260f007800b560250a880400003403002c0400f0800000011a80008001503140710140c2c1ca22000c41031000451442c800f640e0142c641403050460b0780c0e19098000002e010044040c1c10780c0b82903280e960078003480002040d500003a405103501d0030303c1d00c0c070b51098110a50100071240c90030300c1c9070038540d01c1414030f5022300301054a5800030100c86d1490303580000307190010041181c00960f2414541c41d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 612368965 1250 612367715 612367729
    0x607020604030e0d0212100606050301060c060c031b09080c04020a140307090302060c0d080c030423030412210305091e1002040e09120c07050f061b0319030902 70
    0x880070b0140009541040d40c0d6550b071207a40710107103601501052800400c41034040d91004da01c40c0305103003541000c00218090f441001681e0480d00c00ba41c0b214024106622804024500c48036200101612840b44a03032214004840000c1494681e680b0f5445614005542d0700740703245103002910490040090f0100c0744d5200d80d51201704480a21219903945520700141e95840e01c540c0000d42080c404a282c0c0500400460248541121a02da9544950303402503546120f200490b401072045010103040000d4004035005e4004454031101180d281588800e43d50181c03444000c4c2c2156420701103143c400aa00c0d401110000346042c504090245003484a0001e8807131802c0541d044082c000130005180c03444c1c040002800d4405244c60455a4a0b140c80054007052002c45920400c5d20600c0d09000c0c403040300c401194544180e0b400905440c608140030070007000080c990241c4d00c40c0082c4021001d030041c84036907901400c81d0340c0046541e1400d04140c00c1c0104241d403004014149002c1c58000580c0301e001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 612370215 1250 612368965 612368971
    0x60c280203131e060e0a1518050d0f121215170303011a0c10110403061a01020715053013050304030201110102070f0605090c0a080c0904020a0312021e06070206 70
    0x20410354205851130010841b042015403001000140340f5181502c855000400c046081c41202a0781c04819162400d00605440550b001003006034100e0f403103804515482e10f1000703442240e1902142c044092095030040d4ad1300184403200c00386422000304444e501070301303418006200c40009503085614011001c10000c8420b5105101d900c40042c12026140c02840621414030129204100384901034100e20b1705030300140000c0352054641800f204e4000003030074072541c1007901640100341150404500b1180e240003c881c260030320105020221001c141040f0350042002c281a00040c100c5440d900b00c400c1e090042c1041c00710070088040500402e402004a5080d29020b08200500e1a000400c06009129140d0f019110801140542c42001143e030803e40c001c0811200321890ba08640c002c0080b034070300522585000382c3c00181d1100c0242810f0641a034800c0c0001c008a8100d50350351940b4404065803806d60700140c03c0f42d1005240b1480841952520741100c10050241d45407514002e5900d000103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 612371465 1250 612370215 612370217
    0x110f0705031c12180b06181f0f0b0c0114161d0904140c03011512110a0f08011803210b03010e0102030a0b0306060102060c280203131e06 60
    0x40c0962403011400f4048401c901099035008020074150226007031410258041e0441e0b1100045002c00c0c41c17450000c41c141050045110391115070340310b40c058030420b112001c12100b801e07054881c0019802041000381e1000305035480d0300c00c0e0b0f9450311549190854900f040319140680300c0005020400c1030044100400143e5410040401d86080c0c141040b030364000c84581e940400c2d00000c0008000d4003004044240420104039a40c8200d4841014240d032411030381044451860282040000d41a140c5482500d00601c2c404075210503410100d003560703909070042800d03103440701c0080090440900c40c1c42c0c1e0754080079109004170300c119039004200c0c0407444081c40110000c3c10a149000c0c00d26400b003035030300300000c2c020014100c00d24900b90203504200d500c10b1b56a0b150403208031190401081d020b215220580c0074110550341d041c2400344a070000e2150661000f01c418945040440d802100841542540c00a41d220f05c0040c502122442094000100032048980080300422241c10360409132115 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 612372715 1250 612371465 612371503
    0x30302070e041b080d030c081e06040608010c0f0e09010614090112020406030c020c0d211103030f15041e090809090f22080a030209010e030706110f070503 68
    0x2076080001c288455040e03600c1c1c0c0e031102c4000002d044c900000d1080400790f040e03101802401c0c203094064403180d104030358002d803040e0405001240b4560000305243d00850007880000c5440c0c84d803078182e0841340700d00300d20740100740c0b81c810403087c2941142c194001014125455962503040043c0200300c0c1486858920107000040f8495a181e802100210102c82988500b10b403620b564140090250181664107070260140780000145801d180e16801c080c01c0e04604070f082100001c541c41403003e096811207600300030716071400b907081303040a000a6006141d281020112800e20203c0e1360204041801e286100701d00d003e00044114440c0c040800c459504003000052800b03040c01e00ca4524490a00059440114403013040401150070240c103009820003105108018031001545621101120024006440a21906001900c2a00201484001854908048602c050101c0d20b40312994105c4004140c0300c5000030200c2100b008407082800310740d401032807101e2501004c02c2e202d158801c604108011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 612373965 1250 612372715 612372721
    0x16091413020f10020123070e19060f1b0f0c05010c0f033e010c110601090917030f07020105060f36010f0303170c16050705030109030c0615030302070e 66
    0x1000398000d0481c03a1000d80d541200380764100798180900e00c215103d1000c03800203405c0c45640c0c00e0401049c6960070b0f0b43c64013209001d00300442690b01d0345000501c03800b08981e4405d40300c09055510124503a261084c0f140320340c10700740f5192184400b201600304a040001c2c0310307120008a490200ba194005030142080d54503107040b0352080140b241219241c186242164007840c3c108402d10a4003a0340010450080090040003603044030581100065041c20340e0282c40180012082a404070310214442c0140326900440c0c0d88216000782c100302c1e0007011400c2a40100b0030107a03028041c482c1c0c81441202e2045a050080000400075010150500c1280c01e810080c04a0080c08165150074205d4050049a0960707403000c4010030b101d080c0c003041b40000c0f40c24060747d1031403003000c05a5001e6005602810304040c10442211201e02841000351001c3c0305801c800551a00c0030700c52000c00e80c0c02a55520078030a00303418a04d095992015042c0340441030b480341007010a03030100712502a02d0701c1401503506a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 612375215 1250 612373965 612373967
    0x60f032a0e1c0501060b1207080c070f03020609121c09060906050916050102010c080106030b01021501080c1206070503010302060a0302070c0e0a0e06220516091413020f10 75
    0x54a8001039412601a403071840c1508200007000301c005101d10024030115446403000350703035402a000407d50300d44100d000f1813460790146101a0b44541032440050800016454600d0b0002c41c0c510180d000d43c01000510502c490140256402d00c0b5032031400c0c41c9010050141c08a000d02c0350b1a11100c4c15640300318107410403207241c012403000c43d04040148151b0424030300e402d845090051084000c1c6400c80070004855006024031001d5800540300e5108a1f840c08a0903005000c0603a40705045000d2403140710502074409103043d000e0180040140300100c0f0b8074082c401c4000d003042c1e13009200e5004d24204010560301400f113030706407513060f25400d440b0f07800040150086c0c041c2c0f0030000e0074825080400301e81140405c40981c82411000b10510020f1051450561030f001c080c3c1c4c41c10a91520303209040d000407012400003405c40d108908444414401091007102e01155401c15550306444402d04040702c13411403159034000e2888407000d500c03020580c3c001000d8080f002201c42c01011482d12203c956 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 612376465 1250 612375215 612375227
    0x20309060c0115171005060d0b1503100b030d05090604031e060903020102070204050a14280e010f0b120309090411120a06181104050406150b04060f032a 67
    0x5005910f0304110016294a000ba800d900c902100152505c280481d95107400701c0c500626010300406002c01404c10344588540300a820010711b503180200760920380a9140d103041103181c03821080c4080000d43c0d014000105418640340e01c0845041200c148421880c60f81d5010444003240d62200e026100081e92030109140051152005401e841c680940e00f02030507010340081c60303824401c807002c220039501c02d22f20308111540b0210781d18080b804c0b00009140d180400c1c3c00c1d81d1500000812618001160701e0021007518122541014540d460312441802038a29000d04407540704110b81e10b0740244503100c0b44a5490050034049485a062400030500740f0000e6241001c6044003e020320800c8010002e032140e451240303500444680c0d140004544a1072070324448840e1843c0d0141e01c0c12503031001d40c0f04200107040d025005840c0303103030f81e0144001003c000603005401010f1618500d1346542c81c20001070404818001c0c0c920901d8104200005a40c0000e111845c800020001808420039410411280 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 612377715 1250 612376465 612376481
    0xb06010908250b0c0303090610080a120513030c03020f04111c060f030501021e0a020307061508010c1e02010507080106030207060b330708072303070c030b0a06030201020309060c01 79
    0x200000540c60007803c4e004402036104191501c21158103440b100c031b80c00700302500d80c0f04107c0590000c0440c040012101d0203000c1c03295181d0b2502e1810001c0c4041c103910100003962003103518036030145040045085c5a480c2c0c001c2c40300c0883c0c0c100082c810400042040c0e01c0b41603061000c1452240e0342000302d008a50010340a040030400304c040c0340c0c1e10303441d0440c000d50282c518141401414a1035210012506003200d500394130641c05541011115942e403009088042c21a20300c1100c03c182c0859464024420138621848035034904400f24624140300754109a02007040046904040c00c1084280d00103800314112490f61400580d1030360f071400c0c850020104100c045030321160750010000b40c0100d110300a1450030b401c60700311008800501d4502140c6c400c46070000d000460500036000840c0d0506c1820480000728a484000441d8100d001c138250b5110303100c00c64049062040a0051101042c05194001c140c0c0d18200040c0d421030700040c1d5a0300506100320701c00d00c40000c030324803840d03421741102c48 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 612378965 1250 612377715 612377729
    0xa02010f110f070b1209011b0c061b090314030405030a03210510180209090a020c07030b0a0f0b01110a080c07051f02010c0f1e26040b0601090825 64
    0xa10b244c5502d0b0a40c05070303021704940340c80ba140d2203011424104040c8100b00502c1c680c0001c2507489034104406a41c800f40710002aa03015a80700341d07004039004002e504803c00d455950710410020300358582900c02c0e13003000c04031100f2540b013400144035944000440d442280c1e018204091001ca8003005003c6010030890484010390400c4184031380c10784075040000a60304100c0780140c0c181c0403014110124020900c007554840050008202e801c0451b034001c1c851744d0340716000c1c1c6540300c0d02c0e900d5075030b036059054440c1e5030f2942d9200340007450740510b481065880314003480d1204010558202a0741d407441c031810041d103208000603c1402090007003005000410010b000e2032800c101103480c107808110a484480b025501780500480e00c10301c00c1500052003c020380741c4100d071503200740b20330030101d584c0c400040034015145610140b944e01c4040310001825005290103880c681403400c5c0480c0c00000e06018140400d0b1442400091004100c40400305055081070003010041c41c0a845642d5040e0f02060b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 612380215 1250 612378965 612378973
    0x120604020d0e1e0d020a0308011e03020a060503060901090606080a0e1e03030a061d01210602040306150b03010b16021512100807150f1701080d08090a02010f110f 71
    0x2410f07031020016040341d5505015568000400b580598544d10100380c0180011032020050280c0407950704100d402058062400e0301840d01ca0740420051806500001c0108070302004101c0305103000d01c1d90a0142030f402c10140a058070349000a08008800740a204945072920401201d000080200d2407000c070a43d00c1c0c42c10300364884086107861f9482914032546640c01c200d0042040c42090041c007204402202641142d0383c030b043d0701202070700c2c0303c40003401c40c440c046413003080881c2150010300091400f03144001944070b40403d1107100c8042c03991000380840428001008542c07202810342d600c404614660444259032440011703250b1503c0d502c649036101c8082540724000e0450491107100b42540204550302e943c0300ca8810343e842c0901d21600c050002c1b81c02e942c0134101d1007110781d095404224145002140c0c104115440105400d8004038202e0340802c100b40c213001d60104169801c00d041401500c0b24000c0c03600000e10541849055505100c5c0012108504610803c40f8080f0512000295 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 612381465 1250 612380215 612380233
    0x151401120203010f1a090406060b0d1d06010f0909021c03210b060712110f01020a0e010503190902010507050607020615030c01021f0f15050411120604020d0e 69
    0x19408400c500041a8040e40c03038944040007015443c8640090b4000001903103140080321810048030142c010130072141c16456040c00620190702e0300141c0041461401c0108400341c40f80c801604408840c1e41d044030350740c48100104030304a0455881c005444400f4404290a59140040b480c2034021003840121104446408820306a008110f0304455082d042c2c100c0d542e004110320003003034440d0828010750200b010007c071800200700315480d1000740440e00b45034580758001008182004600101c401c201d94001482c40c441d1030b4000c202402e04c20382402d2941c00e50410381c04642980c041d5003481c0c1445641d6008507015680207074186c906041e0311108481140c607008000a4881000355030503011046809800c078981e00e40403940390900f00c0d041e801080b0841d4040d03e40029031161a07941e42000741c0e42c5030781e03102966a601828500b0300c14120390040c61460320003072104841400c01041101e60050009041e201840c00c0540e03040a801c0714090b80703480c1c0c1d0811500c0141400e4110503858421038030743c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 612382715 1250 612381465 612381479
    0x1061505070b0714090904080d05060d0803060913052508010e0a1209030b010b040e100b1c110a02061905091005060f0a080f0c0402030c0717130816080309060403151401 74
    0x400e50312750440c1d41400309482d0401800307901000030000a1050105200040d4141403054100c0d0340015945140000d003c269101c0d5410b04003a00c04544911001240750003200c3e8404074054006d0141070000c01c4000e0300e88911544481141000520f10410b800140b0f030158842c041c00009985c110814107071951f51501502d0b4107078090700ca103410040e42d2000007030840c1e0340d002d0420308031a024640189865070703402d4140142c4030900350192905684031385081007100241c002d0704845c481c980084c02c980c241400c402c90078000a80c0d00004950070081089800013010803010742034030305900d020400b5100c020020701000a0480f04907080442c2d07020005485000107240c0c0c0c8034840aa068800c000054402d110681c8030490301c2a035a0041041400b00040c2105a01022001d0740d10b4061b040c80c40408440380c3d6491541c0c0b0400c01c9902481c450245031010602c520000c01c4000011840c000c2d4103030100303225016a100107042c1e01864281d001407860f15400044006801004d040c00b00e60716859 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 612383965 1250 612382715 612382717
    0x90b09060f040605070c0b0702010504030201051c110c06010e060d080d0b061c050a140c0c0705030f030903071e0608131401020c0c060304021c150e01061505070b071409090408 77
    0x4080d00d00c0b40141c86c00043c0305c200c0d4021111050b4040e0b48041c40d081c219001943c0715803081d08403007024555400c260014100702e200307101c009001c00d400300395120141441c991800c0c41c1a000351428040348001d0012a0f60b8410414600329480740605480e0720842e030703000f0001c009080300f0a40010300001c01c5141300b400e00c0f02c410300038101d0140400c29a01ca415590046400094102079013134154030100700610031f480003500e05000880108e40d9003d0700e402c003003428080047d00d114042d034800309040156103814000f58016000203800c0008101c5070585101c041ea84503c00c2005201000e4042610360390210100c2c01299041224200c8140b16802d459000f0350040c1300320b14140c0280e07101c1c510b051600b641142c0c040ca400504070000d140007503134011b003060700c01d1100b195800b011840b12034510f070302070007544c1202032114000107040f40f07403a0801040c2c050400c010b904202d010846000003402d020501600401c5c0382ca0500c1e07481080c00101c1c0c1c201e10034640203580c4600c07410100f04c00c010100c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 612385215 1250 612383965 612383977
    0x60b060c190b090303160302090303070203070f0503010c08130204052203080a0b011d0f0d140303010501020118031d010909093c17121305011b090b09060f040605 71
    0x9810030110760707030f2424055101c0c08242ca080c10700300010844100f500f803182e00980074454000f000d5034500080703a07001a00d481c1003a0f101000741a00110f04001c170703242c28030072502502001e0800075003518202c20385503c0e40400c0781c0003e1280b565074000c5480c00c103039460020101c0f070758061105161407860070041c104210440700c1a0303800341401c01c03244080d440341d00404004107120100800110700c510410104612242d403a40e00000e40054a00c0030403030b00031000918000f60406150381e5418000020b080d40e400110250030b0354108010303100004d42c808003c49411101c48400d00720100c901004840700c51030f9030700401c42e144c1086110b405001580c0c845c1142e00e605101401c0c1e1800031204c9000350444118810241403880000c0030f8042210040704c0304d2142c000c20480c5203445241744402d05855419a0050001d13402c030131107402007003401d1042442c11036844d680304400403101c410040201c4414011f50b808a10089290100c58540200759841c000c0ca07050720b030740ca45888820050003030300b0107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 612386465 1250 612385215 612385223
    0x1a0f071b050103150b0c01020915040e010b040b0f07060f0f0f0e152202060f040602010c140a1d0d2603010b12060118081b0609060304060b060c19 64
    0x185030002010b6010740b150902921140d4103000b100c03481d19000c400f29030041c03d0b103107246540802103c0c0c140c2c0d440e4403681c04040704402c62251a1400c0c10320820121005030491044803004000910610140030162191000d101089940e03411103850158040d001e020301c0d4072503039800c1040100192005400c088801c02d200c0301c080000c10f80040e00f0a1b9561061001c1c01c0c0e001541c03502150490300340030141030302c491a031203841410b00c0066000c2400b9521070f07102110003044c046003c5c010360390f0a00404111702910302e031082c000c4514100c10200b61040030720510038000e60784003803410300d0b041400103c03120030020160360740ca1407141800000c0000c100501004e070324508140005413158902568180c0b43c4100425060440b05100480e0600002e05950305110039582113480c3e0003c5400c10030040e11540000c1c041c0341084402c0c0411070080b0780c680a2140e442403046c1011501c403841541e522640181e40031880c42c90a0010030040c2c8a201c42c43d00b01c5000b4000141038400180c14030380503080c1310f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 612387715 1250 612386465 612386513
    0x1030c05040c03050c0d0203130c03030c0b15220f060b0702030c120304060804080706050a1a011b06020a030b09040602040612051e0901060b0a02160b131a0f07 70
    0x9190022012138004640ca03d200907024051602c103280705901541d80803280c04410500001c1580f1780b02e0b010102c50b030040300003548541d2584c0400c103041600580119006052159400114001421495501d412090741c0855004602e84000c40707504940585410040d08110040d180d0f40308403441d40c406ca000340e010b40b040f904d03000c4690030b012228424034281ea1002e103060030f051250031694a0700181041d200d810051010300080b800c070b4485c490140500c07c4000400702040d003014200b02004410641c180802100e0580484803400e0049056130f0740301000580d15043c0c1c150a40080031940b03101070300200c3d45410401000702d558001d01c192012500c568021080c0104454140d400403a000030002000307240b004420790072843d1168000244000100310700c0c6d1607040300141c2da044680382d2001603112003490a04580780c900b084015140742c45006217484803601c0400c3c0405400e02c6141c03540d0300303203003808013001a25505460442d100070444540ea22183d040c0300691000400c0311000f1034030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 612388965 1250 612387715 612387731
    0x3020a0602060105011209020109180f0501050906061c0e01090305070501060515090d11060a02390d0302030f0a0903020909010507090605181009031a07080c0a0509040501030c0504 79
    0x80000780c0380e81251300580d215000504e00104040140c007c000c8124140140e816021610456840c02c40254030803111700040e040030250000b2013a28810317442240030380300103028084591200400ca40008245909288454101d82c0310705000b8040303c0325085280d46484094002c2561040046c825180603d00074082642c45104000050b041c521074440610410030151005007003040c505000d5600500c0811400305880d00851050362040c0c2c00391005030414040507041031f2140c0381c45203904a13004280c2d0484102850b03400059285004010b2241904400703c00405208108030fa4004040010154445001040c044c0610050b03000883c0f24140c00d10006030004014840c0d144981641d0f82ea00103180d144c1a42039038240d2100c450b541221050308001c0e2034039143d04981d590301c58096a201c0c4a80b030714504044a5181c140000b1100c044942c0c01800074196101c0009600400320481c000ea5903517034050190750a1048260b035a0300141000000410b0201450303681741140e170195001c0c05030714 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 612390215 1250 612388965 612388967
    0xc0a15021b0307090f02070b090601150305040209060d1502040308280e01050f09040203040f0204050606070f3903140304030b010e0c04170f210a120f110403020a06 72
    0x6401c00541901940012810450100150030007030905a031a80d00611302113141d16906860107084900030410b50084004202160382c114050071440110b1404004908296002170200c41c1f000e05905d100301407000c2c4100500004070008060488041400c6554554074606421503420108a001d00410741083c0e018200c1906203c0e03040884280e135940a41d60300d20801542c15800440f81031225131010322042e000d6849910045010b20b014150040502650388100030580c0c00003846035001c3c400c14072440d400914184140d017001580142241d2000c62800c072a0300c190107607025070f4521403801011102035200990311034025a80a007815256110400464643e40e205500c00281416074072001040981204100281c11041d20382d86945030640d901d441001c0c0461056188056070400410300e40d807010304100c10489011030340e5242e0405440301c4801001070082c1201c000c28001d0041200100e6441c2d5407002c8441110070004014404400d409258580c00900080307008403102d01001ca001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 612391465 1250 612390215 612390253
    0x1051602040e0a113111090d0c090b010c0519150504060b0f100f030b0409050a03181401050d0f0e0f0c09011a0415030906230a0902031c020c0a1502 65
    0x204803c456180321488980120f000141b140d4100e004903050140084805a40d9030328001d50142d008540402d805800c004c04070044a59000a4074107000490000303200082004c510100c00605c00c003100c21900001d030900c61010000359170903076006840c0c04104010444181e001c00400700c0c0a07290400302d8400401482080c1c4015100e060210b0030f06505403552178031a404c580d59565010b071001c100122a90f4505151151404d0b045010903030107424152628481d0300180c0c003c007150206034894039100c600281440c45a40305000010f9240e02c3d8544207044c1075040703400c0d50038801045920300280b04100a40307a034042d041441c4600c0707104000040f845408040c078000e480c0080382d002d00d42072824080c070610500303c410420600d61500400301c007181d000d01c1264203010114000c800ca02050b1200d2140366040140022202c5140680d0000580c0b00040e400a01c5030300742d41e907140c2d1300d0551201030b0b20b01168200000d034400030480010594588103242d843d40c0000c02d400300c0b148800090f0201803d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 612392715 1250 612391465 612391519
    0x10b04090b1503030403060606170c120a05040f02102609150402030f060a0b10051e0309032a0c030f0c150903100c02060a0b01051602040e0a11 63
    0x440e088040818010300003811000d0004400401300d030300d080e0b030740d035a4507041c0d6805034461808070301d9140c07192846040100303031a548400240c072040e00c2c2542c91640b401001e0f40142441e06030550b10b900103010040c124428038502900142034202141c0c51000041030b540500d5400180c0740700101c00350b285a450000c0c0745001d9550000030b00048038141460401c41c0e200140240d0b030620907000019014101407002e20f01440003460049121003007002400641c040500e2040c04101040000d02c0c43e05144e040c20901050740f6403181c0d540d94031804051441c0d40980391440c100180b296a44081641038148242c5561011030b040e174100c4070a030b004160301c6280300650500d2070b4003c00e0504000b4134243c491410303080241c00e1911f00308054000403e150850a03241d2a058a41c2d54100c280c00c4c540410103d54400681d0f02c040c01050304c0d04000900c1400b40307151004142102966000c00c41d500c1e03401101004c2c125030116009844076052a0075072601280c6094001c5004040002d170a03041c001440305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 612393965 1250 612392715 612392723
    0x501120605092202100f0807090608060d0221070906080d021507030906051611010606050a0302070c1d010905150108041103010605031606020f0c01020a030f0212070c0602010b0409 79
    0x1280b9039450a01c2c1c041640c840c450190a0380c1c4140c101d40040e6100d03141000105d0055a0b40c0c2840c0b0819030025203030340006807405d802d010400030200704084c0c0c01404640d001009844000000c113841c4040f48092030100002c0383c0072001c500c9452038103c000142d003403c448804e20103210080d61a211039840d5010030344e01c000142c20202c14a0810b1171042c802940011030392500150f10703078843e00d0300070032a40c080e02c08020000f40da440681c8501da101c100c2d81c9000030013000030800e061030402e01500038400c1c5400c0308103040e000310340308092201022082c401070100d1840740d6030f02c0c0f0768200d81242a002c00d02400821901d0100495240f41c3c1c10080d290f641001078507281c480e41c88588481e400d4291102400781d1541d213480c40070806440c1402041c0c0180724007005a0066402c0880182c10907444071009210b030b90203119160307a82da9002850801c515014100603c0c40b000c80d4070128204401020171981a000006903030003049070701e030000022110143d008020404c3d0441c100f0003543e89059000d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 612395215 1250 612393965 612393979
    0x31e0403081608041a1b0601150c080c1b031507020a0201030e010209040920120a0b1f080a020a140f100c0203060c070c050d1203110f0d05010501120605 67
    0x141c18a10030102c0303000c0c80e50003400442e041c541d560400e0300c074080d1031012094001c2e00102c0e5410341c1140080011030940c1c22000500005d42c1001441044007040c918a0001c104c0780b01c15090501054070125481d1510b10390a6495082409004055800809015a000f88a4040800410302032440214028940c070b0707014115594084e001100548115070402049541c03c0201d0080f03582d6034400d00030403d2094002080321314020f2001c038803040303c2c00c4115004182c0405000c415010100d0b5030100d550b0b003c04154225102c290641501e491459034a9080240c444408949440c0028460401c80d101316200542c054036901c202d000c0500e5404140d0300050024041075007464140d2020a20004610b0b03c0348040c071281c2c0009181c22416503100c031074a440050814217214071040e0302d01c042c20080c0d40740080420260b46904615485c5d0250204144d07072241c40005040c1c45000729140510b2404280d40c507001040b034044010b01c0300303100b5207010a402c507902c16942c202c54001e600886800910750f07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 612396465 1250 612395215 612395227
    0x51014060f03011a0d0912091d0105041104080a0f0b07030204080d141603090e010b0309030a050d060b0d0f0614011b020609180703180c0501200708031e040308 70
    0x188008a48440b01c00361303048800c0c031109004107600d11542240c43d00505c104d2100c1c0e410b8072800740c2040d00c03642105603000c1322111000507081090354424110380c0c0586000031a082c03801074101c1d5901441d04044414003d0031659000e1001e04aa000300d80c9025002581568032510025801c0381300301d1150316420f810030505481e241f40581822112498098400e610f00385101d028412040780080c02100071a10704041801001c0b84507582c40e02400c021501140b46041c50107401d40e41c1e00500a00400300400021032480000b96500100c1c0140390004a4a07100c660400480c40507200e000c841c071490314074000000890f04440e981c0d500f00200c040e10344000030815001110075450203024203070f03080041088a080075403030b11045e02d40070403040c204411140c10034a0001f000c0e10150f04c03c441c00400306c50311450105503070161981c2240d2003402e0030308180c80700b02d01030164128103e882070014019014001a83c070804401003031904c6000005900d00004641d841440303004600003d0903140d024022 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 612397715 1250 612396465 612396479
    0x240c0c0a0f0b1605010e030c0709050106020a0b0a1b17071d060703090b0307020a03170402090c0c0a0b15010f0219060203060307080a06090c0b030f061012051014060f0301 75
    0x2c0070000f83c85030007800084490f8441c5802d54288070071085440d400061001411102404580050b1412200911070795240c848000d41c0d60400e60405480205810b0200c0c9829000307a1010104200b0408020350284040b41b0140c180030491411030050001900000d0380c052040d00900601c90b1120445402d00c036800083c002e444d04070803412004e00111540200c0c00d0b00e581c601440c841d880590003406088041d01d00148086820384e031000060682000b40070040e902c0800296111311070036122600c82c3d03420001c15292201c080c9010701540f208805000c000380280034010322040302030301c2d42d50080b2400c81080741c2e2034590751049002d55001c241c00c2d40c0001c00303d40055400103c010201c852440d2144801c908043e84810100c0b250390780c070103681c410007121a00f1003005118038400c260942c50080c03690700c40c2c0c4400416203807040b040c2c02c5083e40c01601449601071203c003501c1d81040689020072907001c14614034011114221410103541d001c0e4034010342100c075140b525071000390840e4a0151 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 612398965 1250 612397715 612397717
    0x6080307150c0c0209151f090315092a060c0f02100c0c0905070f11030d0504050106180902090606090307090b0303190f12200702240c0c0a0f0b 63
    0x80104200500503180703c0159a03003000381401010030081940905985404100c5130721003000003402d0040c40401890740740e580107500c200c100e917000400540c40c20341040000e00100310480004043c04401c801011031100860312a018604034406e0031b208543d1244010f036580143c810380204202d0301c4905403801402c048030300309400585818a00b0300401e896581d000c7e0a25650811107070159075004110303039035611440a01414445051524905d81e186989070384912503804218001a11103000c02c040040951009005281e1440341c04502100341040070080c102d101d00070b038850764a80740454040d07c0c2c150102c802e005c0000780104051882d02c90300f0303009400d1710170b0703e60391500040c42025240c01c50f035031103041240303003aa450b00c50100c0440c40c040c0c80200300082604030107240a1380081018511001c0c0d10108084201d56030f1143c020b480061550007807003000008940c0200540032a00c10000c01807c0b400503c11b0071344034218074003014031003c104548144800032030041c10400a04000394 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 612400215 1250 612398965 612398981
    0xa0b03032b0207051509010c080103020607060c11030c1b030303250e130603200a090213080a0f1e0c090504060e011419060f06080c0d0c050d0608030715 67
    0x4080581032070031030b031607585c1459001d0000d0080b04407044200810b01c2821b200d442c3e0900307803509011081e5411074001c074100b4011884010406696451008041402280300214002010781120754424248200d59141c06000180d8210407403050801c200e1450048282c3c2c0c411040c0103041c0603c0b042c800c2019600007038a2840d181400541d507120040c685505002c2880d000c820324011070304070700d50314100d10028003101c3c400d03180b61904607803140d440d640c01c00341d0022564203000158851550440103d480c1c01d640d848543c040c030441c0c0060b002c005840a0b42020035001d004050400c5020703401005050703407020801421034050441c01c2c442e00040d82e11603600a4040d03400001c403ca00c0f0022142110584940e03036a01c0389018080084070000f820700d503010b006400000b0300180c0c0ca0804421604000350003800c1c207010030703000020048080403065540c01507561005206003038403440003030510361141035000c0805007040008149080300204030f95040c0c0c5d220b0b0b280c3e48034003150829240103244d01d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 612401465 1250 612400215 612400297
    0xf0c06071b09050f060f010e0f04020a0201140108010c0f11030a35042102030d0c0e0d11010306050609030c3f0c01020d1b03020703060609050a0b0303 66
    0x400070110314458140f00343c9115a00d04082500c180c00c1a8040241044c0320713503102c41c104080c0c1c038003000307594032040f0007011a20405e5401607180e0317080e040140d02409192140c251440e4240c0f000240c591815002011104d805489842e140800302904903043c0b0b1100030780181c41d902c01c028680325075220704138403000150b04082404c1e00040080072600b5841c0c030012071400f00c0808406110901c100e00152011400451600e48806038001c1d401030741781c1c003a40451a0b10303130390340d425504103180c0030700003590000c600107094103140401850141283d03c0240c0c90540020b19081c800324032400c15104a9102c41b900034014486145030008000f21107540b464408048250304c8000c500e5a02e1503c10b103608001d030500e50035224004c008245e03240084c850700c1141194030694031900d495130004196081d0001191001c001c810150a0903403804220703a00090101d480c00702c0015543d540c40d8411030052900200500c103140b0081c003019541e005610800ca060031010321181405034202e012081c1580132 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 612402715 1250 612401465 612401513
    0xc0315170322090905030a0305150109050d020f090906070810120b090f07080718020f041203020a12090314151f09020c0729070209070c0f0302030c0f0c0607 69
    0x10344283d50155441060101e40c40d5001141140c802d0b900341c001d141e4403490030305030681e22058400008100d07442c2c0e841003030b00807000c600c001425515544580c036000500900071644505200340115a1030000312000000610b0081c08680001c030088240300031a20322401c007070820001626031302441000644028200d202da800c000d56180000c0c803031a0001d0604d41c01130301c051490301c602e459032811080b5003411201e2040140038682c560b0300003a01c065070501c60701400103003541d01c1c01364a0700d104d094001d0110026040b076161507540c080f58003c00d0345d201e00364107500050311703c1d100c698403151051745012803010b40e000507500c02408031b01440340c5000c4500c517407101d036030324403521089070300107802020745401200b024000c513500e080c01401c20804980107070101410f044258441030140220091141025802040020340710341c1c1c14461181d0091f1550084007002c0c034010790349500c40003c0041a018503030f003020341c401001c150039100002c050b11041c500202e03941c4800703007036094203140c560840d9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 612403965 1250 612402715 612402719
    0x100516020904060f0b040b0a15121e0f0b01080105010e01051209030a020d050705030403110d05190510200a0201061d1005040207030c140106090c0315170322 69
    0x20300d0152842c015406a5800640005800401020384004001043c01203050121008007502c03403c2020341101c1411360b1002000c07264410884001c504840e008001b1030912550101100c0400104801c11104d40360811410b0b030140e1510066442c9804890f01041115004100d6035001e40030b8049050380c14500245440510009003000010503940c00130705600101e411900142c04000d401501c0b02d80d820180c2c01c00760255101e179680d1081c4e02005008881d1051982e034035440b00c15a5160190b44081621440010409a074200b61700740841510a0304c122501e80e00003041a124644119145212012002c05d44010500e0b10742d104081c070400310340da1200d00203620120781e0743c24021141024211341050912503004808050590003983c400ca104100d4140025000034400d000151b00501000420754803c805500501150340260901410030203c0000c0070340c5680075a812030305000c0c602103155113541c1e04c0405001800010895980100300c2007400c40ca1222581003034091107201004046d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 612405215 1250 612403965 612403969
    0x2040915080c01170a0f06031e110105030105030703021c0605101805010b04171002040605070311060601170414010603030806010f1d04091407030305091504030210051602 75
    0x40e900400301520031005030000e21511106001c00264207009103002c4d921000c076400b000c0f80200002d48806003040d81c070040b0f40040c1107260056002990002001c0ca204800340417110000380503050704840441840c0f00141542d0300440650b030503104050014404c560846e0700b480141d00c0d88082841f1290490700d84400054054000c451140c950202c4c8010b0842c60500c0d0030301d03050b64100d00310007981d007001c0c01403144000c0d6209680494540d40808210280821712190821511005807410b4500001c2e0104a4036040001810380510a82d0350140606c41560710989803401a01c0090000703c03511020a220840a40619041401040014401c0016013351401c440340b42c0e01c2140480c14200411505681019a9030400c070454104503034601ca120707407400000c1b8010841c59200e1740c1c0d101000424052403040d551251502e800482c0c903107503180e040291072038100c11007640c8240302c1d03003800c211300034190310a07681101d0307003d42500c030420660181035805400011208401030a544003510150b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 612406465 1250 612405215 612405221
    0x212030c04170a03050a0c0305090a060503091905060c0721030b010305090a0b04021309060633081b07120c06051012150624022802090703020409 64
    0xc0c1140900e030303903580745031101220b000041d5162821458019000910109030404210b43c01402145000b003043c050602d402e6032203003d00400c0d90b40244440d10042811500500114090602c0c08203c8109500d00700c00e00e5a14810000001d01c02d40220b0b0100c2d48150941020300a020321403403800581c12072a038404584049444000070002c0c0c1c584406220307950309071160b0341d00a6051800391032212074035244c0303400400300580020b0103100e040703e0003100210547d200d15401d03a031202d02803080f1030303481c4c080603020703614040b6480c50300c4405046841498500c0794802d10030785003603c84205ca40d454880d003a01c1c2c0c00b4100041c030042c190070814000021040c00341d290510066480316940000360303080c4501200c400601900da81030280106200c0310082540440070180d004884070701c118078018000c2c005d82070f9540300140b00951103040380c048030051107000d040450a42d00f1500c10150380741003100180c81040284910603031002c013000140c00c1ca0098181c0c030802c0d9007405454542c0e518900c20031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 612407715 1250 612406465 612406471
    0x10e0d120e0c060f041409090c010e0613090603020a08010203041502090102010209130212101809021804030c0b09060c030601050a0e0604091409061e15091914190c021203 75
    0x20300000040900061b29030342c03403049022006441c90161860000401981c400300744999506102c00d943c18030b42640d80310300848040034041e4044090702a030340c2d050100500701c2800101d110f61400800451034090501c00c1e244550b80081800380840d1800320070100940c003540070141195020800c044854075a00e401010350111a42c0c01a0344182403041800d0000b4040e044501a00e600c0204100251007081581e03642240303940009503000c2c003440002c800440c2520b8155030003048008200c00c2c1078000030315030350190044070380d148160b0b2520385454a40700c04580d8100b008100b440450915440786000e02050007540c1001c2028445c8100006e0113500f1907805070031859103c10700300d0b0400203542c10321508081420000c060390b0500c10100141038080c04101c2c80c0b003112000006c2c40d519180081003100c000068405203107030174840094209040655900740100c3e051108117581c51030384003038072803040c02840f010411a9044c15044400383c440101200c003180f042a29120390402440b0007140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 612408965 1250 612407715 612407737
    0x6090708061909020403211e0f09030f11130905060106270b09130603020d080723030904050f04031707170124080c0d050c040312020c03010e0d120e0c06 67
    0x6500e8050101820b07a003542240702c02049030b0180400d0381d582080f9416230494181d42481c94000c146041c0c110360803500c070781c0080c050000950401c814403500b826420170307049040c0c4204004607000c00b81d43c0d056441c50301005100f07034071440c01041603030b1140c040715039010340c0304000001c03401e03055104282280198000150960000400ea040d900d031820605030b85820225050000601e950001292100c502101030640e55002640300e080000208210360510103103a804240d04070142402c1e40c1c0da4006c400c0c90750190f071409010400040c1c1c05200d140c070955240c0d0300c2e81c1005a800801401c413000190020007804145c00b0088040e00e100c0c1c05582c041d2800403ca4100380883c0b1808124050303034500b40c1c5041c00444428060511000d10480f071581e41d014002088640301c884c80c101251146500140c914500c003d01ca98a140d030220b400c4103030040440c001d001e5414000d10054950039110070b8140403521103d50064183d48503040600000ca02805450440d01403101040855001d0b0550302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 612410071 1106 612408965 612408983
    0x7063b0d020907050301060e040e1902011209080c010606091203050a021018051501120312111605010f060605040603091b1d06090708061909020403 65
    0x1080c0e41c06441c2c1e481c0c0c1e203044400140035030420f016002c0014000d44841d06e803468a805050f51212145002d0100b034103041030078407040ca96410b800c80c140052040412009001841203840c201c1c0500d8a1a03600e40c000d091007403c540d00b5403c180c1c10300c2a000000e101d0301f605480d171044a1a850304007250b880241c944140d180589403407005001c18100400c20010170394242c25904064070032802c071418801710280452030031009016400e40b01580700341d58008039100e8103008188101900d40001c10170b01580d0902002d500007078030103981e040c800d84001c0810900744900300050304000c00c100001030810314010b0141c4600d00c030300c100300343e110b0709a94244520141040059001a843c01b544165618411400b0a168090070b60300408444001552810301d004194442c3c4204d03602c21099a51748810071903003000121010100080d0688042041a20f0740700410166000c1d5080c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 612230215 612410071 := by
  have h0 := BRFrame.cov_init 612230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 612230215 ≤ n) (h2 : n < 612410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
