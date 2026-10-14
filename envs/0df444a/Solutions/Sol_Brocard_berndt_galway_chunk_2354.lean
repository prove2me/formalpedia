-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2354
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:27:11.313037+00:00
-- url     : https://prove2.me/submissions/9cc70de9-2471-4566-9a50-a127392a87bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 423201438 ≤ n < 423381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 423202688 1250 423201438 423201461
    0x1023032103010504020304060912030203060a140d140712060e100513080c15070e090a020307050901200105040503040e0a090c030f1505280204050306011203030f02030408030406 78
    0x11032840040380d80e906922050040c00d010310f0700030020504000d8260040000150b00402010003030010341d80041c02504219140c2c1e00c69846803000144c0e0404040103240710441c0980704e02e204158989030b003c0415000192041c50744034034040050740e04158002d00b42818400c0801140c05100d02d1801840c00340c01800d440001d500c0c200901140d00160b90b041c0e0704040c0c5c4000b01c80e480d9154440c0241c10062034041a4070340c450124100501303958001054800500202c5107400c054072070304615000c9000c21919040821401c100d164000d60107620310b51030a2000c05402404400601c402c2d5003910f005076000c80703483d4800301e8140310000c103440a40703500c1641c02c4810421148c45484400c4520b0151101500000161040205110a2210012841c1c1c0304007810f000504044410b000c80003135a0749100b0328081e9100e03c0b0545020b1034001c541c01c0b100d00500410b01039090a01490700c086d003009080341855507540758900c440d2245e002440c880d901601c0b6854591405042c070b6026101261000e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 423203938 1250 423202688 423202723
    0x60224090a03081f030b04051b01020c011112040f06020f0f0a0b040602130303021b0a030c05121e01051008010506210705060c010c180b07030503102303 67
    0x810128500000300c05007807a40601c0c0c00384040d1a83d4108074041c1c6100b20b210510100e0002d4080b003030111044a40340103900c203408481340b2090311400c00c010201201561401600f1800100d103540d1300c10810101c4080d408400e0702d00c502c84034569600c1c1540160311034210101c20403020841907406111502d04100d021010b40303500030000190f07945644c8640f20062204d181c0e503000c40c007480f4542c1d040e2403100481e0300d000602c0b00e0316400e0296a400d030801001c070700ca2880c0c590303400543c24003548003000c0300c2d489031f003c035074882c2450104401e080c24258101090b126030f400901c200f40544140c40c2c06845900000207142c14400aa4158800d03103404c040c0d00c0da8180340c14405251105288a210662403c1c0c1c20740e0002030f14815541080d020364016544040082050042ca0a041d4440700b001e40007511080d0501e0140e100c600100781c441d104e84e0460000910114000c680070708021640034003c80417455215440703d03d103603510048004000a00441140002500e05041040d9880c100c920800d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 423205188 1250 423203938 423203941
    0x10f0509060708010b0d0c03090f0b100b0c070e090a080a0c05060a02030411040c020309031f140606030403110114070f030e16061809020f03040b10180c090f060224 72
    0x745d129951056a42280c001a0b9803511241d18511a5100d080b10fa54002050701d80c0014a040c641c3c050801079504e00102e401204000504141800071521107681c540040c018240c07410782d00c0c080b046002020080140215886000080c000d40010640e11450303442e5502c810340b03a8244645044002031003618032900c10810310001c07405088040c031102108841c049000400c00d202282103000300d03c6282d0301841204040c5400e00700e801c03d00741c92072084150820090507a540c1119500100791501a00f2860400c08a00442c0c401c001d00d46284030290b0010884000c4d500040d158140111603030400aa00b2090201c1d01680c036005028501000d0401403d82c0b01042040e136411107031500c615014402e10714810310366009881c03002c03c000c4c413441c0b500310b441c2d1806540840003540210740c2241c244096000180e15050540c90a030155524982541c4903011107000a60080510840d141c040c44240d601c00904ca402a0175090050005540601003544828500a1000e10380c1d241c4080303910765510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 423206438 1250 423205188 423205199
    0x3051506061303020409050c032d0304030f0305070f1b0302130902090105061309020f0a02190804030b0402040f0f02091003050903090103050403170103060c12022106010908010f050906070801 84
    0x2520301d4203813501140c2c002100100740c50610b190141007089150180070b0400c1e40781c41c01420650101010b80e00100751224000c4a282158891017079000083c06201240340840220340300e00b0240000c0351003081d21080d0200ea5813200c07a129000d43c00e40086e0081c100d10107100318205581e0742c4150007041241441200156070000c1c8081c401405024040c20b000300f07904c6030100d5024484002400380d1407045540d003800c012070240c80d0f0321068000c805441741040c6218200125080c0c8050b03186c000010300e081c181142d071452080d800181090782e00c01d860304824181210248201084cc3c07080c10001a82d55900070248488026149a03403000d0524000410481c503801000306c90404400b40380004640e9660320b811348040100c815000c4d80380100034004410030803182d00c5a20034140e076841e607141d0090710701040c000760302c600084415045907404070300d4009100b94103c1c5800c20342c141040103c030380d00c5080ca070707084401020f03810035265112014002e01800600c28140c104c1030602d0a41d01c0c960411 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 423207688 1250 423206438 423206467
    0x110406140a05061c020c011d1c030209060906030708010e0108160509071716120203151002010f0f090605012c07021c0c030e0a1d1003020a0305150606 66
    0x148120b6028020003d0141920310141110b0300c018400e8800c21074803803408820f058000d00c062991560540e000c4074a840000d071000640c41e00000c004660f043c07a81029540803400f94116031100c640059092003511050354905000d5840f40115940f065503030340c0b41805a400007001030b40700f1600390f08009941c1d00911288162001580e0080e0b034110b12a4854a604903103030b0b070b994202d172020068403405126084a22001140f100f011581d03070081500e1881d00088101d1109441d4642080f110031150304050a0000301d24032042d100d4000001c2d08001d001410084d00d65031480c01103c0341c1c0d03c9030701400304961481503a02520a100a86480c80d0061301c0b5400600704958001c04400041000180014400c005501c28400032040b1546001039120b80a080b0303d11070741040b03000c1114205524070906010400004407081d50400d81c03030014402d00000d603403040150164800680c140713404809a261211a140258030400c010402210b801d41d10914084010341068070420b0100302400c40445070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 423208938 1250 423207688 423207709
    0xf190216150e0a05040207083112030c060c23090108010e0c09030d05180102011a06071403180a0e01030206030a0f0f0c090906050901030506010e061c11040614 70
    0x7281001c0030031140810005602140c903600442d44140005000f00030040a44040d0992070f1a01510a4655203070219181042c3d6204090203040f0110b004e01301700341200c01c4034a200341c1c0d0103410301100d5034503642c49107403c1d05c080c5915007000c5000d00740040808600d041180c43c070b44080720b8440381080e0445000810400043c40380c541d15580d07075404202c03240820070841e01601c100801322510440d80340409000f542004407012940c16411000312155401801001150180c5104015545201c08100405a00841c2003610806604c43d50703450441d40410090061990214401071400004400c0010f0000c403904030b0710701c000c1c20400410040e00d45d0001d40350054010400402d910800c0d584c000000c00020a80403039150800240e15192a08002168161032011609000700c90f115014080c0d400400e100003409548401c00401154103100b50b40c541024004008001017a43c0d009140304429481d117060304c0085201780c00c1200c0380741510a04000740203100351201e46960820000700480784 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 423210188 1250 423208938 423208979
    0xf02160b0409092a030c15020616120608061812160f020603070e090106030b1e0409080c010203010e070c1a04030e0a080109020301050f0f070c080f190216 68
    0x1c440030341e0400c00485099040c210340e034140c501e000042194114481c0313203003a41700589000104a50116000060007224004001d0329002400a07881d55038041c1c0c2e0702c040251040781040000d00e484081945035020f810020030a02c0000c0c481810f00106251007400c0003211310065500200c0320b040d045500009544c1040190908403d01d103249050503011b03482c404500940c0580c0000c20807580c0d0741c200103000000041070b2562062a030325420140c044030b4289980542c000c1c24000d801a50380c02048407217248120103070002c2180c401541d140246c681003c241c01e03106940110040c4011900c0180c3c0700e6000c2003c1c94041903070022a110600039140044e2100201d480480000c0c05060103985445000c2c00041c015010003555030148500800503003a0481c42035092201003010078a10406041c001c400700c3c80f00da921a143c0550907102c070031a0000480300701d402404076108901808025041e208a240c0610014103100c00d002401d20703d4619800c1c0c0141030001d0140600c0b04618070b142604413 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 423211438 1250 423210188 423210191
    0x2091c0501020d020c0a032307080304020d080a020307060f060b030705032733012903160e010c03051b01020c16050a0b0c0a02010e040b09070f02160b0409 68
    0x890404034060700c1a0300c0f004214500025078000001400078110300b8460081e512051142c41400040c0042040b40e450710b00380d0035003030003041c000c5a007400055420520090821884822580d50361186802022044004d604003084c090240001740c081d585540e0303e0100f0400050341040d071100e401c1e002c00f030481e10400030048001207419071500300041441c40044105003200076800500740d9110b0466039030302000c0b0a44218545241310000d070411601b0555407041481342c9c2091003106001d91418941810855030f4409801041c0350480218003803800c0b8a4000780e1070070400c1026007181014808e05040213410015000802e500809651210700340150b01e48030300c4480d20701c482c06405002503001d0f0700c3c0a103104580520000c80d2000044800c255108011541d580004030480d0040c40c03044040b503002940c44400640c4140c0610307400740c5c8018000104010f1503030105aa004040b80c45001180900b002061101e40412028a420020280c900403481c1801c1040c0c550303001d184985498503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 423212688 1250 423211438 423211489
    0x21e090121052b0305153114090c0d1b0506040801020309070f06141303210806040920030f2401050111030a0e040605040c090e07030209 60
    0x400e40d000409121600a801c883c00d06500d062a00a0300410b144010588101c10044840083c001d0080310b11460344c1c40c4030442508440340901c160820386e43c46519000c0321134018400789509a28079400340400d43c8200142e454032082d090040144041c200802d550300003c0000e18607500c01c280c401410f41d0040c140c1b540071019040a00c00c105072500140d074000b030b0104000c101035005602461080c5201c20880b0700460740c0c0d442c111103000c4103008450024941c80803c044014002008041c0d420b503e492608140750350313880b0030307200c00303d145e2403a003600030380401e601c6265500030f40c1d5640000742101d003004581d1540da200c5070f2420f0071148035400b18106841d4244140c1c0e080c0100700b0f0740400325058500d03481c1c0c4444851080465103510250700e070348060001c0343c0c0f5403240304103d54107601c00307008506e8002c011000751840070740c3c43d4486030320540380c0502050030b80751802403400c100483d03155030300c1d13050810038039841c000d5008000340308061050003001400d540d00b4000c10780b450841c803c8070514 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 423213938 1250 423212688 423212729
    0xf03070c0c32041b0c02090a050606070f080d0c020a21050711030304081e060c0f0d15091a1c081902191208070201050103230a0b010b07021e0901 64
    0xa0407100d101d98030441074030100014480c2c2c00241c21045d040c400c6440b0181603035195112422100141d601640101081c071101d000650a0f41d1001ca07a1030103076000381e06003c1000040809d0b2800c3c01404801604800011800c0180e003030000c10343c4084030720815901c0007079100024064000d8100140000700d1a44121506442c1401264081c0030b5210685051803280c1646054816560030a04e0a510070940000c10001070f0406440c03241c0c011419192900d4401003444c4003030104909188100ca5401d0000a6a2696441440c010310b075800003a001041d1200c041202c81000711403e920f801d03080911007400a1601011503582c8190000700c0b080003580c50034102c0c070b02148091850b491500030311004040c4041404807616070107444da01d0310802d0303841480c12800c0c0c0c2c000f03120060115203182c60f1801c2c09401443e00011600c40354045503051174071030300c41d40c030101c1c42a404030817a860b0002e0b071b20b425030038103010820440344882040c40c8141c01c8940072501d150070500c00e0074400309540a107580d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 423215188 1250 423213938 423213941
    0xc0108060402090f030d050c1b2d10021b04020301050d030503040f140a06050c0a0914010e1e032e0b060702060310140102161a0f03070c0c3204 63
    0x113001c001a0460b0640303050200c02501c194030642034132440744164002401004174041d100e200a403030207015854000403401c401d10f0985005c420111034119000000c0356161a24141c0204d56002136000302902410085203ca840c0307802081107020b14010001032200e61075500c20442c405034146490780d031f80d0b5294180010b003022070000040c504085074030400300100c0300068000b5164082c0c00100056152652540414401c00d03151a000c15100c00e010046c114080c0891091001c1c181014038001d001da6002603801d00e9852031890300d5448403030701d158542c101040a41544c0f0070408080c000c100c100c03000d02c400c90324200e1480c00c03010384420241c801034807240c040d81c0c2c01941c060309940e00c0f030410b0a980010640d15010381000400d000e681186035601c009010190b40f090350782d40f810750b81d04000c50303401d0a10003d4600060081d0801c4660915180e100085101c0c603515a00c06001c1d5a0307920b4004214001940704011805510b51180c041c0c1e050348590700b00d61422000401c40ca045610f01080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 423216438 1250 423215188 423215209
    0x60f07030b2107050609130f0e120c0609120304140a060e0a1205031b030a1104031b0803030c040e130b010f0501140a0c0201120603020901260c010806040209 69
    0x2508840d075140c4100c0d842500380b900c00d144520003016150255243c100b40700d0503000e03c9071442ea02501d0031000c0c111000007540420740e0000700e100c004c41c218811111044ca80b0000340d5805502a00004030000015014031046805c2910078002e4a4204c0034003080003410b01020b0005054a5190118803041c00e00402c56141c5d178561000702841001100740380d080c1c075909054003e403900f4007a0116000481d1003401202c1c820001d00c6100d422070100800d400c49a07800080c0f805011a0b900e04e60708441040013009000194440c070748401c201c900300b4404084181c0b180d40040b040341d009106100c1210008020b803400d07203000c1050f042c51503a81c0318910308848070344d445c090401e61aa0001007010820130340000300351030003a01c07000003804c011514040684030700112400002c540d9003101c0300542c441c1d0207418043d0300d4000c000c10401d89070b400090812600380c4c4420440103e07844412000141a40308034485917180010709035400703032800040d0400e8002812180320350341c00070302d0107180d9030303600c4413030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 423217688 1250 423216438 423216461
    0x7120605010801020c0d0810051c060e0610060509030c0612060a08010c0503070804030c12050a090816090b0619020304170a11060d020d02040906091b021b0d0501050901091b0305060f0703 82
    0x40444030010001cad204901c040e620103480c42170a00180b52a14200024441d01074240f104011901c3e9203080c1d0215015080750141c10740c94011030b030384201c0b01d80d5060050080c0000d41590320b640707410031008012480340d541d44014516414540c0554090390000e00740c0354014028144159135641c0e502c0c084401c00304114000303081e921029009035629a22038050b00c0384200b00d40700e204003143c40d01c540550f070740b810055560011082d10003d0001900725044259403800c058503640c14000b41694440001e119a004000181d102180800c8004c1c151400720f40304030401406040e06060315140c500e003600c83c1040c01402640001340c8040e044041e503044030b000141208003191100d0720350080d000504011310842c9a41401d1662306101c03144802c1d0700100302681c64000300700c1c05011425404100e10804000341d0710a80016491010680c2030040c64410514000000751158043c03920100310f015204402c0320440820b03205100040c4005080c3e07400040c5100310822560b14104203c2c003800000300340c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 423218938 1250 423217688 423217699
    0x140d0b130906150b03011707031403031902040302090a0b0112020d0e060c040e160201060e0c270a06050705030403120f1d0a031b0807120605010801020c0d081005 71
    0x90000e040036075803020004900c00c0d0701c1030103440c81e1000345090729409800f5003490190200010001c1103000c45030030007a03120880540340f40b9692503d6a15001c070240b44403407030070f400000c20080e007011041000b8410f41d9244404600745411600807800030300c0d004143c040c1c0c0c65560221148507070700170302c0303075001585205405565078111021564007504118841c075202d0300c40c50000c5408801000c050341d05880003010000c48a585200850a4410a000300b103000d5559800001c03400302000c04a80c0d1042c091a040155565010050b42100c2c2040c14070404030b0740c95910450f0300d980d4400b05a00100c40c1d0320700d0513944620446c1002030030740c03113150700007841c1441d40341c03d1900590f002107990701e0242e01d42d124070070810307107004c8241c2e6080c810300d2407154800440d003010700c005200548030401d0007400949890419403a0118540781104035001101e060303004601910821405014441c094900c4400030b5050440f6141840d81c1d03200d03200c08201c2801003a90004407500124004080107240044c40d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 423220188 1250 423218938 423218959
    0x1e0c0c080c0102120105150703080705160b0910060b040b0f040807031a0a09020109180f05090105090d09080316080d02190914030c01121524020706140d0b 68
    0x80c06070003035001d400301308400001c0c40d000142030300d80341840c101086c85041280d0310744091582d0498144200a0400050140c10311041075590380302201d48645c80d01c121180a0541444070b24540b508150101c40c20140b800d00800780203803490142981c0c04c07685102035072512220300e4517414001b4080d03038015200a101d0107100000340090f040324280d0080d100c030000764182e220200b108094a160b140040c0c04501c48040400200e405074806141c4a00207100025000491114290965000769a00c00e183da4482e020b00c901d94a041c070501c180b85a150800c0060395240a06460b168007407001155000400911034405001003101143c1d41d08103407200443d55154103221800d1003690030804200040d640b00004101e0300305151801500c214000e00805841e094400110340400c0340c02e192200464580446541c040000706010700980000c090b24011000c2c0c910361210450000d09550007151700c40c1d1000c000e250b400c201d04820b1084080003c1c2da444090b892214041d100701c0004e03581080d079424 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 423221438 1250 423220188 423220207
    0x60a080102160221030a050d020c01140f01080703170d1803090608060d020f0d020307050406060e0405070207060c030309020619030209090f070f080a140f0703050702011e0c0c08 78
    0x88000002600c21511411a0b0b41c0720524140c130344c00030a89420301139008021580060740110045e08481c183c82c403016140c0301e21140060b096941428840390180c541034284041c400c4542181030141411200800c83c10380b070343c2c1380c54110a41c0350603542403075400040d5552170390442da0000e80e080007641241c144807120510700102905402c0c0b00b020000b032143e0002c607480349080c5a803d000300350020854240304c03105c4420805400e030821022030b4548110200001e846d21075015841c01003280b82c41d104447d60b0756005010035940002e110008641081c40207000303d54005800840603034051500040704400b901c04580140308080c00030780310001003403c55561079410b40040c403455406440c00b4004c2c0d01e8414030751381442010341e039030004201604030700380346544103022250b84120034101c041002d000c105096000500180c1d20b003220142c0c1c001c1003019068050060b01d41081081c402080b03000c80402e2580d13a005814000e800049031120b0710728080521511540900c9078002c1c404980e5495840d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 423222688 1250 423221438 423221467
    0x180605040c151b06021606110406182106060b040e0901200d1a04020307020a0308010e13020d051e160e13060b1503070e1206070c0803060a080102 64
    0x38030407511407500402102031034520801c152100c1041c40000482e20f11250f81c0c612019410050030010b80b03606c07800c8900301103030440c0030700c011100141411079a01c0341404001400d4401c0c4003041002c0203001d06007001501070a80c001c510b00000b1280844d081102460518050002c9078009402c0e60b0020501155910341c07150f041c0d00511100d0020420802911000c841e000d40200c075035550814288407d07084100580c00030440600c64200d0030144001ca10000340481e001560608016072203e51180201504066114090606400c421400d85003004942a9001c1c50200c000e02958406846e0820050100302110707030140b004200c0c0d281040b01c0c075100c81e80e440713800e10030358001318040b64001018000c8000c028019070311810056056403550b22200040d100041c1c0e140d400c08501005100b43c008164080c500030b00705583c0e6801d5040c00380d82000710488040e4105c0100f508113105200ba0300350890130002c0c2130f41c0c1c800c03281912075031001e00044014000d58000b040950000030b83c5003840c40072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 423223938 1250 423222688 423222713
    0x1e0301060306060e030d0e060c070914010302191203031112070824130e0c030d081f05060a0804061107030203030405070f1802031512030a02120310060318060504 71
    0x12640c07088030701300f0700c2c0c010507607160700126010340440e68854000c0c074a030515000810301c440b210703401c4032442603513001d900003140c06001510184001c3c000c010310031890202540d54800401d038030400401410600b2494064050240c002d0074142d6400188402451110548040c020700d001d540c105464006401f0345200b100f10b071105d044040c004e4010b200c050443ea48003200301005028942841080c00b0600b00400100c00e018041c0d10982c6a20403259404010a6000c1c0b034160f80c1d00001410000009690447c0d200014204c0030b159610034402c6840300701c190b9119551394640030180c0c1c0c446050074001003c11015150040ca00042d403d424140c0010007175000b603104d202100c41d03069507001c00311003c10f000d014010084004034030103c2081d8060300a0740d040340720200340c820201d6403040010000e650360000c07198070f43c001080c4450718540522050071407071480c011091031481e004860b807030948414000e610a00d0754910410a0000320740c0281741203158001c0040281d8180360a110300360191 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 423225188 1250 423223938 423223949
    0xc021f0206070e03061005120102120106050406020c150a0302030a06050402040605180904110111460308060607050a050a060e07081c030e0c10030b01030b010813081e0301060306 78
    0x2800783c5540701508000070218030441c20380700c260341d1391401c180801074094440e101070301f1340750b409001502107940d10320b58080c0280050f0715015550341c90040c029050032120100300c0e10510000c40f170105c0b542d03480c8044654860340ca00d001652513540356018401404c2c980c0001c2d400520103e0003182e00b540100c0202801c560652001c0074001001c0100314004004071401030000745001d0075140e85500a1300c800003c11407902c1990385281c5401e0302900140c1d1404040e800d013007640010b00f2082e4102c0303500c6a0351184a040b9040a098698034041d2a075200078200502030080043c0703403c00c0c841c06111084404d5405020340305510154203006010746041078070030b100e501440c800098402000501581c8483ca00c81058048081c4140258000c0c0b140050301000b6025484c60400d107540c0300c1d41c80800c0021a9180060f60b010610b00040807510071802c1503050141e41828040c000f44500c0c50415126440a141070350b0340002508082d9640e41d4000c0013000e04ea02100105203d909500030106444 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 423226438 1250 423225188 423225197
    0xc0807090b1e0d140a030e0414060d030e0307050a0f0e1303020a03050a031d070311040902031903030207150204080d03020304112b05030405040e0d02030a0c021f020607 74
    0x2041c400812241c01c855054028100950030210703402810194410000a07000315114141581d0039040c075810011300040440000f40000b5440c0c4083c0b42c1482005080302807038a608049151844c00301d035400c1011000074080c0400400900c0c81e580c1c0400c50b5402900b40681081c591035502c0b07a0418a8103a540034201030300180700005103040c014540340b80c402941582c0140500b007115107058841e42d0064a524003090344a20714100707030b034110508a0303083e923001d50b005105c910710b141000c02d800072100e9511407180c1d05003502c0c000940e50019850121003000c0c42c4504100c4c551b490240d0081c401c03000003c100d02c01c1004021200110303540540111050181a25100c001e2480300714224842180c008008581c0c00c02e505444c0e00308428105401a0ce08445000a01040c2e440c5010b008404108035925840081c0c28030032810240203203045e115020004009003010701d600a904c0e80200c612490420207002420401c0d507840f520003400c0307042004d81405204c5401e00c0029150031044030b2000200703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 423227688 1250 423226438 423226451
    0x1050114010206071710030803090c01021605030d080c040806090a0b01060810030f03020a080d02040305070e130828080a20091212160c0609030b150402070c080709 72
    0x81d400410070301d11411180c3c0c0c4c3c214a81d140c6254225031600080c0805400241c20200400080e09200c020342c00380009100404040300a54002480c1158160712055185860b10040040c1d48000940041c0311100e8202890242c0c2c3d1200c09501c64011980f151a0901c00d040a00c0140d40c40441d0002e2054010842c4002070b031f0320f5540940d0b1804007a11401c807440310614041001c03400e400c850108041c0319105940366050b813511a20200d80018420741a4598002420400c00108201c030300000c10120b514600b240c94170b210881d10f51103483c0c0e03000d0100400000c0134410001091002c228005240303194602a80c0e0120000382504412551030001c6032900094021008503040000310600e1204e4500f0b20709000765050010b8550b03249560354040c8a00800d02507100da45002801000042e03080c6444401c005052103407201d0503070f6101d141844035000081c00450311940c4a180d01800002c00d2440d070500c00c2000c20005d12030218003410780ca84100e4081007000001c60b9920860f4030480041c0b100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 423228938 1250 423227688 423227729
    0xf16030507080d0203040b1b0a060b0f0d11010e1f080103060605041802150906070813050904050703030e0105192001110d050a02040f14040c090e18160602010501 71
    0x750038042510f80c0169005010400500383d24a008001221201c04110341090f011141103242690060040302c115840b40c61840c01802c000303083c5104081d0486a0000004554880720003c0441d540c03903038100402d2002c1020031b9190090918225003004081c007403510240940204185802e001c1100e41c2c0b820305d00006051701d040d000e580d901ca0342034803508080c034a40c4d0303080080650060301c041d100981d003848407003a5961060040e01703002e4000d004040d550401aa00199403020f0764000074400d080346418400800d200140c008140c95050401c07040305490600140c49074003900c42c00c07103028801c0e056845e0405600c09040013180204035008032a23a0940382c040740c2a01d030140c0c601961903500740100100505103400c035503002510000010700d0291910902000c00c55a034000d090600a01a281500e500303003840390241c07803051880d140c1c0e08103062548484e62100082c140000a07401840d00c200071340c3d01840b840040050300c03840211501d42d40e00f0302a0182800f44140008900646d501e0090f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 423230188 1250 423228938 423228943
    0xd0c20120a03050c1507172203030902040e121b011d1005150303121b0c031c060b03070c03020c1c0b0108031206091009050c070227060d03020f1603050708 68
    0x41d840c036841f10540200c5004004030510001050b804401280044d1000001400c0c030b062003540e8083c1e07030042000013a500611040c1e803c0d03000311820707552042c2c500c20b01e51203108017900c400941c41040e44c00c4409020121f603015100d441082c0c10440d0300c0035200d54502c1400100014410500174080c403c550740c00c1c800d51860100d00c0c081300e425820400420710640341d0440c4150340030654442034102101d48540144558003d0759141049a1002032041080c0007006906200034000700000d200f102d09013940c403203c0340000341c010000c1c0310701d100001c42014007c0c0040c1c051200050081c210903802c0c060300c811440c070015401c3d21303000142e00011503529000300440d130008194440151081d1584024403101010040007007008400c040340115400d02c2501030103000b00080d0034529150301c0a4010407000900340041d0101aa0404000d442e0609202c0102a0301101c101c1d080e81c00900e00d4203050b410304641c910740080c02d0050f0b0340c000c9001d94802070700104ad207000d0f00807034030340c40d4650200c990b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 423231438 1250 423230188 423230191
    0x41a1c0f0f0623120d080108160f0b070f14010c120209062505011a09060d020a0308030c1b0f120403050601030b0705040315050105030d0c20120a03050c15 68
    0x81d003100900c502c2d083c48011220181c040c0c14405464201018031030394405042204198200c800a450303d00100007009042180e00511038034003141301c0c1188e03d00b503075a40102d4018810070b00070002c046140c600713011840c10000160b81c0c00400f0840c1300111603041500034401d40c1c142d00089016481030480d105030030310030340700900ca0190001e49000b19515030111070f010201100700090f001e105840307000800c02e006100c000c004551000066440401c108039040d1002800940202e500f8112000540d070340c082c030030048a801c0b00140c0d89c2da464580d5100c0d014416150025290246000c00a1504400040003010b01c03480000381c4500001740100107186110f584006807841c0e00813001070011030000813050350041c42c5418640c4c5000d0380d0742e07070b003100b000928940164400d541b0070041001c0d0400340809001c5c0050741c9440c14407003400b1b030386002800e0407030106004401c910042c95500d64a410907484280d07513852003111500707091450000c10640c803144141c00d0300d02a122480e4000000b005045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 423232688 1250 423231438 423231449
    0x30d0902091e0f250504090b011412071803050f010f110d05061914010809071503150512060a060819030e0409020a0b0408010e0c0105041a1c0f0f06 65
    0x1801515031007540b00c01e1000103064226070229004282060644c640f0a1082150b401d8a40d00d80329072601c2c0340181225850717881181840054100c2d1040f042920044804c11610a050011144c0740c4640c1100e0031515054061543d41000d83c0c08401c0c03220001c0c0315441002110300030310003a000b4181010070b452003000001001c2d02c0602c079030384441003d03800c01d0360322140240451501180600180100605903481100800b00085144995591202c6015881000c4400401c103503850b220344e0800c12900d0b506041e04050742c5040711255035400040c1c01c03000b0703e00182840c810450f000202a11840207461080086248c600d0000c2c041c070300070030504401d8040c0c40c080d00000c0301a8030152081204d42076070301c0d8402c0e510948a00141d46214820018221010200e40c46034180140d1a086610010103007403607600120301c0e1601ca070380c80b00803201074809900645c03c0c4c0c0c0403620f43c851014096654004145035240b680c00c80011030b10b9110b2100e00c42c4207042404542d62058219045034154040d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 423233938 1250 423232688 423232741
    0xf1b041d0a0605010c0f0303140c0703080702010b010525140d0923041e0504050d1107210f06110702100f0c0201030e070801020c0d0825140c030d090209 67
    0x1742c004c80d002e40c01d440030090207428007040074035043d641041240800c40b54140d9641c00400c1020900da4484101076100c0410f000820404403040000303491409095071106540203900c200054401001407401026544a14543d49041184840d55140c5c8418405070b000500040c60009546c01d0075000105c0c0001e0070709599899405002c188030280c4814002107907048038500c24052007094902c9081c1c441d6000342c4c040e01c03201900142c01006259000b1410140307a1159106101910310110707241c408550701c9841101601d0a468450700b0540c140c9405420a480c0c50405220044038000608003d44200c80c1c2c14140c0707654542c00e890300c00d52003500e44000b81800703d003000154080d90000c00044510300440358440d0b82c4800c054203991054500038501d410200c10961040d802101c80368002a200e0002030080c540050f09801403d00c85000c030b01086081541244451800ea04590300090480c0940b0b5450b100b42c641e00010300381d0006d0803406008504006100c09141040700320701290020700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 423235188 1250 423233938 423233957
    0xc0612150a061713020d0303050103030f11070b090319050703030e0409030806040f0204090213091d0a24140702060f09070317040801060303080f07090501080f1b041d0a060501 77
    0x99441d683c80100046500d2040000980269580d102c40070580761003550003154641c1940b800515485503484020240408000c2107040307140046485019a0f090441203a154002a4002490a80d001200041c01403511450038140200441d240d404d4a0207511000a04403502c0d052008585480102900082051001c5002894990451502480d40351000b42c10944c5407403020040303911a9041c10459200540c04101800541c0584400c030f480401c6004c042c1004603651603200c8c15211070003000b2450f031070500c0404e598410300e4a0b4810402a00800642100807030244040c501039a6400c094400e420002d81c02c0d40100d800c49106440d070502401c0c0d00340c515611030700103d880551203201010140008a08058240b09980045000340d03070f82503942c1071180a0842010028040f01c08200010100f401741c3c0e60000201504404202c81228a580c1c0341e0610b10129800440d10600408000400082244003a01c0d0a2400740050100000940780c503a0b8820480380c4600c20319012804800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 423236438 1250 423235188 423235217
    0x6060503070f0c1110050909090102211e0109020c0c2409030a0b0f0105130207050304050105030604090b0a0b03010b010206060f2407050d030b0102150c03090c0612150a06 75
    0x22618800a40700e0b01c07070441c2c0f130181c403070015060707005049403100055008030b082d40d458a080d6107820703040b0340050001c61030032415905000120145001350241e85074500b01044402407580241e01d00c24824624243c8556103a900c810b000c0d501128101d0f11612454a801d5000c0c0f0f45014050486c0c1e40d00002c400c95290f0a81454440782c1040ea010b0340c0c140600b9034010003180034021103a03c2051000d65031000782d0b05140800850000c841810365040b8810710031100019000000c5409a03002400c00da41c696440c000014007030b0041180060011050400340a40d00c640381c3c01c00f452584d0124000e108005c0860012a035030103040f95001e5108141070442119400d1000000090000890361b140b0344109102c6045800c1e8020803080311143c0c0f1510070010740c9640751051b001e9011092000d030810b140d50b0044070040810142009050440000c0030500f460401c00071a1603540c4050f04c619200e80c90703044030700382d405400c5617850070391984003200604500c0c00f4034013042624003e0321850702240349070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 423237688 1250 423236438 423236447
    0x5010513061209051005010503160e01051c02131a040e190f0218041b150f0302090d200409031d0d08070f1202011506030906110f0403030306060503070f 67
    0x2500490003940d981c40c3c04004034030b00307110480c002d03041c5a20100340d40d450170301410b02e071801481e04100480021078042c4a400c44503041d10b070448108540e11482e00c5080000e008400802c0704c0029480030004904d60189016038120072151004c071360458150381000414801650181e40e01d80080b82c0050140759041407100c40d01804c401e0141d20b9000c45100c09030b0100d2030000c01c51040e502704e07010000800003040b031036030004010725100180143c020740c989048034403941c0c64000000140704904065401003403103a41503821070880180408814440d50034140320b00f940c1023240701800d84c1c0c0c0b48030b03e5072941400e002c1c00c0821941a680c441591106080c00d8070b81c6562005085d52191141c80b403080818001d030301800d00365001d0700140c1c8041003903141031500300c204000b6160959048c03100c200c0b030100400e101001141d0a03401c004c2640107403450300c50300610302d217803000700b0040c004503284100c900f20341c020b00b0a0303a2003510208a4140c4522003612a8042240c052000034141d01ca42c58056208 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 423238938 1250 423237688 423237707
    0x31e1c09050a052416051015030b040204090816150c0804170d0615021911120304050405070314010602210a05190201020a02160f14060c01020d0203100501051306 71
    0x20a540103030b92415400013090903481000c1c0b456000584d00103620034004c09010303040b020103140030200014403050108a100401e0f034800501500c950034001825900d071504580160359204045aa42c0c07001c0e07070004d015818140000f0b030382c41618000000803429191044000850355915803d0ac1c541d2295507007500c9125041401c034920300c1c00e014402c2c140c01d80b401008003401080d0a4154100a0030700001c0c034111206035000e8041c122140d82d41e020903031074103101450702801d071000b0007099020700710b0602e944661b511490f00603142c0810003000642c10360042a00b07090384035414110b030340c0e55501241c3d10549444041c11248124800c03c50121014000f400c0c3d200082c01c1079401e09412140c0049840d203039580440c0940d4000620a143c0e079170600c8003001c04404044071349070841c20310100c41310800040c01000380310529060180717516aa24810350300d00680200c0290364030880048410082d400580703c0c92400fa21015010880b0340c0200250f1701e881070f42070701c0c2e072a81601e000403c80e6007541 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 423240188 1250 423238938 423238969
    0x80d1107060c031a04050402210304030f050a0b0106140f1809040f15060b12060102120301060f030f050c1608040506120f070806010f0e031e1c09050a05 67
    0x1003095100003001c078010b030408003103180c40c0001e5404400807034100f05009040d010b80b0907441c1104000060342c8100700d4a810101b060400b60b0305070140d100306403541c412600007034140c5001403803d8040040001d440074401b841142e1000c1e06980c0c40100303590040c01503c100311408024004c1103d441d9261000d0034030250725019081900c18490042000d2000603602603420b15008040702c000e0001607080280d0003590f10408202d4a850010301000901540f1074040c0560004004180349070b108000c180802032200340466645e50f500c403805003450710302805d808040781c201044020056000d00c0b41d1031040368070000c000d00d06440e0540007043c0080360316040703030f02c45410700000c1100c2e1149806002001440d0000c8040da0905030b00209000030020441c00c10409179004202036668030000c00c2d203400086040486098510f080064141201144951171304442c201c0b405004800000d50102130070751111a0640d021000c18040301c07130034028082c480c0c210344400001c0149090000c454406040e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 423241438 1250 423240188 423240221
    0x320150903030714061005010e100507051509150a0c080c0c01060801060b090a050a0302010c022116091a0121020903030a0203120c03041104180209010305011a060403080d 75
    0x41c607a50780c600950603106004c04183d000742c0800201c5281040c2d010003909003402c108000d10f11202c006401802c06415200400101060f0901000410882000c03018000c1c902d000d001c0c54440c0601e0380d2022040351050b4000420b4010a0080d06a8403aa06407041d00359151000341d40e07140c1e1401c490f030b4802d1744009902d650b1950009035124080c410030000d0201091103a988407444403c0010b060f0058005511801c046241000141e0700a00d000c00d0641d070559002011024060055508d44070f1840c4500c824001d2500060751060707056042c4c420744200710000c010091011080341d003250b404003006c6012440d1420130213241104090080114400407030f0241c6001e81c00d40110707040d030708000c0014025074004184080207025090040f41c0c4581c0140301142035103465281c901c0c41c0124010400d00450b500c1200307007458440072095810242e00900100201d594900d480d0b4000c00c0070900105d0740340c0d01241c8850301c61402e141200c040766004012070f030814412010304401042500c0c400203120 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 423242688 1250 423241438 423241447
    0xc08120403094106220f09090f0204020903120706020a030c11070b070f020d051b060c0a060b0f22061a03070311130e01032015090303 59
    0x84109104052280d0722a682e680c91007880c04910707a400045107210345980748990101622034180c01d040c18a240b4042c08007920705900c540d400720b031480c03180c840301d45154198261074403403c4404120074011a0594010001003035503440b0010101d414800f8018450b181c00c220100152915030041c00c0c0d006002401d56280072201e03011042e195004520480f1151380210303100340d5041e054410000301102c80d082c1049042e040080c03660311420355001d40341c0c948501142910500101c060700700615540a4162810b003801820481da84401c50400850460160304115090b07041920588415178020802448240c00568403440500001501c0b650056803c1e406403006903249103145000c1400c40c007180c3d000030201c2030103c065039900d0300900518007903641101d94003102c0c00222540b1000d640381c005020a84020400744500c1207240300f82e210020b40314003081035460075406904891043c103080701c251041510000c111110307600c86617030040010445042082d00c080050540700b20050690f80341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 423243938 1250 423242688 423242707
    0xf06040f020408011b080f1303030f020d0f1a010c0b0a0e0303271501031202330618010b030403020f0307030801060e030f1b04060305061501140c0307030c08 69
    0x4a030003d50003901d480e910b64400314064500c0c00189006040140780c4004186407030121504c0b4030001404210454140150b448249440380e80038400410960030700703641d0340c41c2243c0040c0280c0a440300c0c0400151402e400800050902c52103204a040d068440f6260b00030b181c0c80341c10600030003e01c42407078146c64900d0802441002d100641c810350200c40e0100c4201c0052405819071400f00c0d101c1801a80441c25441000212940890460303500204030b92002980003422400c200c0340d201d801d1406100115201c1d1180b4221454090010b00d414500902d0b540e20020001108072a60212490552040060042c0c0d003000e0000d40e0b01034024012540240c10800c031a502d158440ca00580000d204c100042c070429502081100c1c8200e0110010305074042017012003622101e007080e00034503c1c0000540d8404a480303540200d001160000150748091070900400f1891100407450107001030615102c03085120000d40c00e550032041a000210b050889647d8269040a240c05094803210800e1210454 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 423245188 1250 423243938 423243941
    0xe0708070603052d040204051503060c03090d051804050c040e091e01020c2a0607080d050105010516060908190e040b0d0b0c0a03020705070803040f050a0605030f06040f 74
    0x245856600040c4929060070810f0400500d8600b40c0700c0030340d15500c210426020050080c5c1c02c640c0440740010b02c1c6d02c80c128200301a147c110442c0382c2500511040118907507804e0055031203144601d090b038241c054480d004803050b1041d544c9001ca60701b02141000c00500b06603000540c001e006070107003841c180c3c481e403914061070011580a5003940c00f20340220001c400d64200c0c80b41c14a51744000350708100c070001d0078075140c6400c214461251180c1f10180c0202c0c034420410000310a0018142a946108034141300485510025032140594100703000021a944a041142c1c80c0941c0740301340b4400c4000b65038905000d041c030307401c0642c0c2c588000d20040300030f120441002c418189090703c03070864a1500303c00307000a079042c00e007840303124100e1703682c501000c90341d01854250700039040b4062565a00c04910180c0082c080e000c0c01528a1040120214906000000800503100c100450000f45940c880410035410261700030180000c1083c808180310700c40042c401c0b0741207a8002c1001c51450b201d03003012030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 423246438 1250 423245188 423245203
    0x2070f0b0d06140d0212120a05090a060801230120010e06060f060405040b1201021201030506090a0305040e060a170705040f05010503030a0c0c120b04060c09060801090e0708 76
    0x2500128001141060080e40d03102d103000401c41d58403030111018102c40010b410403920302020f4015042012401e2040d04207014140c80032900c506201d0b01c654004c1e034004c0c010781140d0156801120018000710341c483c010079407281207e14038030340c0b040c0c20001948041d00030200c0c41c410070706001c88695004000d0321142d007000701c15400c0000019100f07458207440ca00d805005040b00c0e002c1d2030161400a140c0d29000c0c111416214107032004148940414003140d6100d0020b00c1e4504154404508030b031641580c9440d01d0b04032070103401203400c0c54440d10f070040c0c1c132141c032100d004001c035008200800c86100801c1d0f881e0342c426401880d919100d039a034140a100040300545902054000352004d122074030b05841042c600000d0108108240d6041c907020a40e40e06c90300d8461803c1c0498040f501741000603912500001d084680c2c4800302e1121685401c00842205590442e031042c20074103c004458454160341040319a10740d10f0f00c00c140d18107000007008184008448030702e40601c80001c1200c00040180a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 423247688 1250 423246438 423246449
    0x6130608060112060f0504020f0616020904060b013c11010608061012050703030c140d09050f011d010f020106081c021e0a080d090f0f03030e0a0206040b030702070f 72
    0xf580014120320388a412102c990114507139042c40c040605c400350b10380010485803020140c03461562182c02240307000f0008607081000358000804010401004940d800c0040180001e0704c3d4100c00d0f403869000c005048031110b0740620808844900b891103d46c056000ca5003103103981c00c120711a122000401c600750781c00d541003240240c0c008010700c10403200442407000101403101404240b0107860b91100d8070751841d8800901004929210401840030300d8025504500c10103089540046846001401c80d4440380704083c0b0417481c401c14840d03594012881100c00c1425030207400c030b03407401d40c0005442420107000000215960748030003127400302003044020305009216040c103e000e84140c0d8000d150000d9010701c80443c04e6012082c2d450702c50001940704c1400e0f8801d0038151640000400000104000d1601810b150684e88c0210140220078818001c0e99010750307414840008000085035032030351541002504044c00708420800e040c8500c0c041c40d081a4544103865203280d5403040e88010003840e8008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 423248938 1250 423247688 423247709
    0x30602030a1409030702010804080d0e030c0a0308060f030307030f0e060d060509100e01090f021207170108060c2205040606051903050105012a06020a0302042903061306080601 77
    0x2a5071060071450400741d00070540e000451405c0340030390001702030040240c80100020b00c0484c43c1134124440d03403c4040d0030038690b01180d0f00d440c2e061008568444284000390702084000d0302151007070414101c00036070140c01070011850000103550407142518540720720800c100001d24209859030b11640141401a544140890000c1c100000c01c107000c1d80103460808041a0420100825000a141b01d411500e41c00e400048004c1d9003182e032400780c0716128000d0795002c0948208000d07142c0021600c40650621440c0c2c03980c5030389a000083d0340307920907106070300795000921010f810344500e001c6010356003403c0c0c250404072070364403004142542c4140c1c1081000c641c0206400c401c084040c1c83d00c809140d5689428400c03940340600191020b81c040e10120f0300c04c40e03080c8000d1790b0003610391501b2104580c0917404540d6001a90f20050003034101e805110350908030b2601c40c0104c1a071800522401800d00318242e860b40e21003500700054000d100c0b061010280e160400021803280c2488024000d180d03c181 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 423250188 1250 423248938 423248951
    0x4060b030a060f05040905060112050f060106111009080904021b01050403020a02010f020c0114030726091506090c0304020a0b0708070309090e07060f09211b0e0c0f04030602030a 78
    0x8804403007000310307000135000f00e1130a4540004514001403050440b020501c0c088440c0c1c9250074a20304044d80b00c070004510b8400c140002035210350001c004400600d0080a60320303048034103600002540d59400010f8890780c41484126a6894154010880841e505480802088882d0461383c01d585040754140c0140c0c014a41c00d00075941c101c040d4440c41c4030981301401d4913141200c0081c0249281e140f05009103003000c00080c804030300880e03132002c0119800700c010320a4155020072070711210088907401c8050050309240c1c80c07482000c00910340a40c80c000c203140c5a551355618004080e402c010000d070303032150030410002400700e0502c00415016010b10241903413043c031401c0c040d04116039a400142a10315240394402c10620100c0c0ea00c0540724289042c0e003a480c2c0e9068212080743c82904096000d650503403800c0c05140700ba20300403121501c18501540a110a40b810f108020481d21500900d010800009103c088460009000c6680c0407542203080c9038481e200c00c02260011250410050369412 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 423251438 1250 423250188 423250199
    0x1205060402070f381603090803091c11060a2301030503450a0801150905010e06060a0c022b02030c0301020301080a1b1a0a0f0f0f080604060b030a06 65
    0x4584c050300040a400702c80103a058903041600099008201c202c915a0001001d80c5070351103500015082500032404030f45900340350155644401100c121100c1121032840a101c1d400d00a44c14506156940c1c006406596107160001d03000d080907413685144280005000751085100e1050369010314058801540c0712030300a12644c3c00800c2c41c0d2603100c2180c0320743c0613912000382c08480d01d81070811881701040c401d046c0d01c00810304800c107907081400954244100c42480000352500c03002203d01e030710781c02d0140340d03a21401c1c120b941d24203070785868008104000301c003111800340c44ca035a0a030744058410040d03c094135404030030103440c3d64002c1c0890502090b04000398078042000b00c2c0254400c400843c555458910411f5440d240c168008001000c562101d0840309451031480c0001d048805441d9200c2803151030020040d0711a2056802281c50b08000b850307031521460039101d1401c078a072510f0b44617145944060b02c0c1301900800e05a4010340b904000300308a040c0f00059030040441e1000441c0b5142081c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 423252688 1250 423251438 423251483
    0x7080708100c1d1309060c030b01030b0a030f0212030720030c01031e0e01110a03051909022101150305030a0311120c031008060916151205060402070f 66
    0x3004520b003003001c2410000d94114090b145289a404210742060741181c1c0d1841c03c102901301140e014040b20f142051844d000341e01500010f80154003603904205c940309440420541c2c02403400080e000301d031a00180f000500b0b11b448500c0000c100041120306003022551040003100030322030403040045070750010001a003001c000114042009003801d0220b2400180c624552083c412150441940c4422081b160840290704c0040d44000c480429541d9000301030010f00509015103080b1030803088165046c0240a5521400e030400e0ba00503c9001e5242c80529a905c65411203540c01c01079540c0c4140c002005404101c2444c001d5100310041c544580840c40c000d030859100f203031104500c0c40c00f00400c0c10340b004401c0341d680e40f04c441d03000b44c95200d846054030061034070352642207800148100d1b03003480001000011214200e4401c0250403000949a0340384805015015482c080410f04114117207980031480e4002d1036010340c0c050001824204c09403528903a0a02021064030482d40400c8241c01500b0340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 423253938 1250 423252688 423252701
    0xc01090504050910270b040c0503060f010b0711100e01030e010c020c1306050603010906141f0e01180b070c050301090218100f080303161b140708070810 67
    0x122001c118502d41071107210f44440044d80b4484e1026035400381040303e01d01070701180040328200d000300341a07220b5074a010480d50405584c2922030340701081c000122450001641c500c00d01c03103210004a82e918085404200303400001c400c40746174041c880c00640580f24220f0844502c64543e4402c400721700c011001400312425a24109101e074104208050301503000941140c0590094404200c3d0301f4160311400010400c91700001d0f071014000000244002082d0807400c160741a0f00d20391600380000404100310200400404100c0040303140030312078860b0146080345540304040c1001000000186010202001150081050100b010526000b40840c40070307020b0262405034000c001d20444c03600050449500f011080309428806d40014034804900900c001c024119034066003405502c3d4610307582c40e034204a41030030540030381a410f9210f840c800d006504014142220040b41c1036115200c00e0005090042030306414400e0120018011804004102c02440480081c01080d6a0480320342c064441 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 423255188 1250 423253938 423253949
    0x3111603030b2407060608120304060609150509151002150a0504080714030d0213140a03031b06021e03011a030105010926010912030b011806050f0f030106020c0109 72
    0x15010b020b400e08030940344421040011003d03003901d601080c9040380141c002034110400c140203450404118a80400245001e64820741050040503152044001110249180070542d44500a020013143c20704e520301c3c942040425201d200201030660210310a4041c601100006030b0240003c042031000480714907810000001c8188a41e007800d4a404142d070040060150404d072038a40440603d010130030403520610640c0c1c3c0259114a240843c02c0d8001c005446603c54041a85d09040120300d03207100d41209503581501d40c1c10084101401490f001c07410340c4405c860055082101c0c1e00c000070ba004200c030300c1c1e150300da040c40c1e40c03503043c81b0700c40074101b004051003c1c410b80e0620050055070b07000030b40d04007600c4803a54010718001ca105480c20071071400c0240f280705540b0b019500c200344890001200540313415510140840e030840d40044a40c054840000c51402c2100b440603c0254030800040c03c00e10042c0b242c180c140034040030402010b61080e441030016174046010302d0b595503000306000c0300402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 423256438 1250 423255188 423255199
    0x40903180515030c0a2309090a050907030816020411190c0f111512180d0e0f0301060f080a110603041a25090e1008070b070303111603030b 61
    0x40500c0c40b50040c0c3c003000d42901d5000d1004510040b07214442c004001c2c2034152500703061380400a89199141d10391000c40f095000704444000a8501141c2c0d014060244441c42e008013102451504e5210300383c3c00888803043c400711042c0b1408050b07a0f440c0a00c485400040c044242d84c2c1c8482540c00300340c1024480c111081c0690f801c01500411601200e2240458125144c44140c290100c00500d0804810b03400d11581e04000c0780b074180510107509072030721034040c0d1007070240c010b10021b0b51999210314030444070001458128003504103041480c0041020000540040b50340c92315004418013208440d040403c09502c001c03041c109118002c1400b4001d400c007a12100c0c518141515801c109101c04e840844180441e81d0100d25582200b140440030340c6210080c000c1b0308503100400400f8441c2c3c52240d40c14025104000ca480140000703003032400c0b249540e006050052400c51010380070740112001740e041c165a01e00a19540500744010b110a9090b0310b0301d4164071205240142c21103c80c0c010380c40c01030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 423257688 1250 423256438 423256459
    0x121605040c1110090c24020d0207050d06020c15181212180f060a0902181006141c0c02060f01030c120f02041a0909011e1107020409031805 61
    0x30404100780f860402d2680340410009550f041c6818840e00c144c3c01159404459400d9019002141d80321200280072542078804480c0d610504aa4400403030040980c812264442413000911a500402c0f01a910b881680c1d004030025810f00c0d40c1c3c9508560150301c60140c0c4090100c1e0034000d000c40f000c62034000300803a042c00e940d2560b500b41c04000904c00792003242e020124845c65042000402c40591001c0c040314401c0c0383c900490005803040c0d83d4220301540401828100100717002c84d8280c81500324a000079034140c5081c1048811003040080301c5450801000580c0c82454a21812522a4180c1102041454240c0c1d00245010401030841464820140c01400060285a6070800b00c8000e0200d510322400d042c01c01700c040d0340d244100254401d2401c51201980c00400102c03007500907040f141d1000303960743c003a0040d0984044a030148000c82880902d05882240340c0d000180300301d0b20f641c82c0c0342004556404901110341d00f6009401061003594490403a560300103541c8050981035070048cc00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 423258938 1250 423257688 423257717
    0x10329010f051c0f080c0c011103030a05060a0305070b0310050301050402030c040e10021b19030206060d0327140604030209010b090d05060a1e0c1d121605040c 70
    0x15640641032083d4010402850400c00030308444500642140000c2804156840c00f0181c650121400c4281c138001d4201d44142c03980608a600c82540c8031102641c91503444504280c0100320040c51190b1281a0f00008404110304001405c007600019410594a00b00b4580d586507800080d403161f4800d078100010000140c8001c211000307000b0081c0c8010501240b00d00b40542080b8140010440c250b20104080028910110480112001d42d0060b6031108540c01290220740c0440c000241c05644404086040c40c00d0080b8801c120500920b88200b8507942d0070400b800051144041c0709000200203000d010507010000711010b224401c6070614903140c616800310320010414807641015107404100d04405481d1100d90100095004040e40c1203498a400d42034000c0281042000e800c02e2110741200071040f5502c0b4075a1320300c0705ea0310f50110901980e110f2000800c0480301c26900450b43c0e4446803610b10007000001544620340f403044654070304282c06d00003182c41040403031003001180e4008420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 423260188 1250 423258938 423258959
    0xd0509060a0618050a06152703081905120702030306040c02030a020a030806040209041104080d0c0809120f01060f0503060f0705040510090b040b071e0203060705070501060503010501032901 83
    0x30b404160f480121303e954504200c20010146540030150034149401403c91056214030b030f0300598085220342c068104405046200c40c3c80b110300005110540402201003100c0c1c882c7c039000a80c00e12840c040c2e1401100c8280b05141070b40c240c0d040300140e0b002005200c8146032500900149a4251004600b80b11580100030741d1503144c100042d042c030035600d0101e02e40762107940403640e001c0c0b000741040c0641c1c0004204186543d0141c861392480d40216000403160503c0780707003032404484d0040350301802c1182d01c0302000f1201255401c081042e10134a038486c030b900710702801204001c103c00c0b2107491816182500b0b04d0b0810700d0081425140a00b00410440c45076080001e0390f0903070314240c90003c5c07480c0700d48a080c1c6000079076405c1250580300c046400103a810a0070000c0c07421601c1100352151100020043c402010703181c85000f90b01d030300003000207107203144035901412502d4000e03800032910341e0341e45010a00715502a0000e58447e0104050a0b009034207003070140503411640201440150b1401c9048072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 423261438 1250 423260188 423260219
    0x1e4d011115040b01031403041a03061309050c13020f030411010207030b04050c1e01080106081f090902010e1009181d0a1103031804200d0509060a06 65
    0x50601a00c681030260051040000d0a0079018860701048a400e0030304140c00a000c007440220750b51803001c000708801000100c241d90444400c0240f040c200c0102d03c0c41c078130745a00300504103a000138030007110300d00445003405224041030068020303042c0d41001006125104485250b2402c3c82c0b8010409614a051103400312980560032101070010340648000407400e001980c1d2000d0919941d640a00c010701070040382a642c82c2008503800350707103c0142c10610507000343c15a1010f0214007100d00402110b03001350450342d070010069400e28080c0050350b86481520415401a03010381d5543c00c0000708650304407034000304000046400501c264102c07100101541020f00901c2202004211403040880d01c582010b0300c0c08040b01500d1500018911486d0b643c0d00c00c2d080c05440c40c181c2000445141c0c1404411282e83e0f40001d4440740c10444074806000280c43e4580100048881046a20b00c5075a04400605415116102d010419041c0208030720f2900c0340c003030051503840d850584100030703820881e607202 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 423262688 1250 423261438 423261593
    0x60a0f05040504030c0b070e0a0e010e040b07030b040908180906090a09060207020604140a09020307020d050304170f04170705061801090f0f051806030a1e 68
    0x1051590f581d207021684902c070a0001000c40c2540c0e81842803031500f1000782040381200765103841c225503a90742c103e10448028030030010102484804180070803102c0e107440381d00032014140800d00704401d80105040b90050b402c2641c2e544004074000894528041407a41001700c00c80300142e00c2c0c01c0860004240c52005080032140550350180c01d400c10207150103a851a5400070000703034446170b481814080f5445140702c05482040490004103000c8000d1003a42d0040e1401d60081802c43c10f103210a50f956400078000381c5000d03c800c0e0308c010000942c24002d180c0c16480075203e940303c900c0c0140400081c4800300340c1d603195400200b8140111341368401039544243c020103030b0300103030000b2100584803901181c0000041c50124003010940300c1c01150110101c0b40c06864014000c00e0f585a018040c40058440076410f4204500b5480400d894883c5040c0e031703489400c40016080020394801c40c0d89006d080c031b500380b03007a0741081e051450150b0314206c0340d20f05401c0c404002e4016034040b01031000141030454 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 423263938 1250 423262688 423262691
    0x3090c050622170c01050a0e09100311150a0e03031c060e1b0901050a0c050109141501030c0b0304020604090c1e1b061503080301141207061407031e0c0605060a0f0504 73
    0x7c01c424500c14038400801070805000c9240604005000c07840b06000d50009840704500708800380014284178540c142c02402080a140c1020b01174031040322116040a84e441e0706220a100302502600501d009143c00d0366800c100140041c80c01002c2c101c038140040c00b2440010448c0800d02c2b8650041088039038825003481c2c582c0d66040410001c2d10b1003400200084d2183d8a0304034180c1c01c100700d28004506203120101214a204082d0300a0f100b0600709000040005811150400c80c9041d850040c41e001480202540d05141d150003000f8212580040c01d4400140c209035003900a154503014000740c0c0c05e9914161220b0030014000264044ca01e104c003c00a07035544c4410300c0b20600804140740515400b00b5819900c1d652480161400b41d00d001c20a4840c0d940f00d995032041820000d0a00100c5801d41c80c0c01308042c5945030005015040070030142d040c4881041010328403801c0f610380c0506200e182d1a02640000310b420400f04031171004284900074400b50700e086c80007150899845003294403c680 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 423265188 1250 423263938 423263947
    0x3050c070302120901052a0c151c1e091e080307111207030c061103060102060a0c02010b120a14010b060912010b180103110303091003090c050622170c0105 68
    0x4036124401e107c030403180d10005c1a0050155a014203500140c004014202c0381088030132401c10411108581d900041c1c1c0b40204908c200000301038203001c0c01540d90040000d000074860031880d04011807600c8144241d555031a0702020025003c8400c4000e56403200d00c10394203051695503c01c03c0c400a0142d40034840700703201928407040104984144984807081440d1100044e260141c41d103139081c40200e61180c101018090180020310a40703204a505900401607034440070344c1c0e600209040d02d0000115502c9601d2000d4545400c8170018101314070500411850481d07041c400340c4030b20301070548510ce0341404200c130310556940e02990041282110a07210780022090005c4c01001ca0000c8203400c01007203509040c0c8154171a40b403d04a0740140c204041040150081507140e1240708215a80421038080c454841f920070750010462920441000c400c46886000080c480e0704203800a0221407220034407601d85591552609008080b503084030b01a01004400d81034a030030200c1845810480040b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 423266438 1250 423265188 423265207
    0x503060d1b09020904110910050d0f0603080903011404170901020f101e090507090f0e0601091d150c2101060917030703080612031b030301050103050c07030212 70
    0xc2100d80c0025498800301c9081e076521600c8000c4e401c480c001500c02d43c5403114007141494100100c8481403001442c3d100420a4050152180d030131074216906026980c0c5103840c1c88a00b9803203030901030342c011000c16071a00d01900400d425110055a000740011000c003d00c13000822100e080c95148080b8080c894440021000407858185120501600e5108404240030820030300c0e8802d60400e28020501c2c000d009082c000c140540341403160040180d44200340c00c0140d0201507015881010740228081210f20107400d00c249030402c203800c00340000e80d8071304802e80c1c48552907026208c01d188072406441e80701c0d40180c640742c210100038282c0144401c00100240c2c49581d03c2d100010200542e00880b84030358456500030550740c840d0140d43c41c88007001c1c040c405814030010030380b541c555056a4003403845e41c800081c41086000040010701c144810b001100c4481d200000e02c1c00302400c903d00035500d0b0343c17514000400380c074800391070380245a030100030600110f580481e5410b044a084014180e8801d00b45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 423267688 1250 423266438 423266453
    0x705012106030f050706090f0e13050109060506040e0a080403020409030c050f0f0d1b030e190311130b030d0305041e031205060105090d060f1401030c03210503060d 72
    0x1100d518240c1841c01c000071041006800800356100c1c0500b013110340e0030780c0b02d68081e50303141f409000380090865010300402084031071049241d401000c44c0f04048221000f83d6440c0c1c2940c40450b411035623951118200f04040c10325101c0c2080e91003404000780f884413810780f2520351500c9680000781c05961512a580103150040c0c42c18014183c2c00307411100940b0903800c0d4191203072421901d2103298010350700034070091803050f5240f408904c0e5281039042000c01c5036405951800300c48901c6a0488040b01d210300418400f194618003c40c05551400340029200082046a03080210010b0000e07103051040102500c1c0005ca84000382901d040028840d15203080c48010041d50181d4000640c400d8084002050391161050051500890061005844040055440d8000c0c843c01581082d11030100f140400e00d140c1000c010b815003a000054091034142c4403d0410409030000d588656060000300b00300480d5064085040c0c1d1048a140010304c8088001489840301511983c42103088034100c105000c4078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 423268938 1250 423267688 423267737
    0x3190c11030f0703031205100b13090507020f010b030102070f0b1302130b310207060b10020f0d05090a0306020a0e1002010b040605010e0303071719030501030b010b0c070501 76
    0x781112888031002c001a6941c0495010850004411140f00700c000000c5000d01402045019508500c0ca81402801e941c503420617075401441d01021a80062001c001d80704140c0510307817640c0038040111140010070b0075180f00c0c00010307000b42c0c1704101c000d000c40c1030180354245040d8491a201515150050f85d80d07a4001c5011010b03602c0511042d070031407910119802034880c414185c1d0200100095140780000907881c4e43c0d1039942c070301420810100d01481580c020f0000c10700c1510006031000000700030502c0c007c8900e6060001d640800701403424000c017004002922112441c10764030f04005e0801045038100c25200c01001c082d000300e00d8000240c000d69a81e0800480134003403080150030000000c1c0a000310401d0303140140e01d004000b1415500c00c25500f8105000600250719000766a61000e1000c02400c610b034482000038012800030860b20b00d003150340c494a0366400300d0a0350450510303210392181a4410794040100f00404500d000b00841c41400b201c400342072520003018080e0f080e041e10b405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 423270188 1250 423268938 423268973
    0x3020a02070e0a09140606010804061d07120507150c02041119120501060f0c15060b07050a0507060c030e0d0804051216060309033608030306010e0303190c 68
    0xc2c82d00c20468100440d52004e0581c070b005004110340241c0340035505442d0308058540d1030008040200040100d540742d0086458224400587c86010340d01c280c501c0d05242c260740081640030703860082041442410400d8502900607800080548007281324090104120a000280a1912140c900000e690268240c803d000c1c0100d4460400c090745480c0104a210340303455500701d9514103800422000d02c2035074117000e03542c050385842d295846903480d4a8000b5015044061403d070f2604404142c0080240c00780842c42d10440080c4010b844031b00c2c2c45c50030800d1940059040142d041910004298030110380002c000d800d413101c2d45000c2007800c0c40d00d4140300f03d03080540c00c0340009441d1227036444001030351101100c21034100e8403801d485010031020f651582c0c2028001400340b0944620098400c12566038141c01e0402800f980b0b211040400d1003c10b017548104e5064101008001c1c0550300415500178000040b40514034103c0c0303005085001a02400c00401009044141c100030040d203150911491031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 423271438 1250 423270188 423270209
    0x40203091e01060e0126060601020a020d020604120302030706060510080f0403021507120f060f031e05010c08060414160e01110f031e04030b01030f150624170703020a0207 75
    0x182c441104521100b204800f603c1e100401b4641d2904035074000c5200c5024a01c160f0103404900855000c1010f200b8541d02c003664061803c110000b0100fa150b04081e442c90310a0300034541b12480c0c1d08ac1641190041e9100d98042d10f08031204900741540041a540e0044a61001595603100d81c00c00702e00c0c00b0140780c80703400114152801d00c03510a42201e00c2030020380c07514405118401c840100b800c00c1d248103101d44001ca00b003503502480092110b402110320020102c45030803070040b4070340303c1c2800d503220090303403002103160882840600c1c1020b000703104a0708d051302c40664650515060701c03c0d00810b84610801084540d084205080c7e00c1030a10890104400089800c01d200710f410540d04c80c0d0000f0400800400c0362481010b03901e1040050301e013107030b410000313005590780395846080d0340003040c03007017110301a400d002850102c03226481288003500f05506c0740c2d020100040711800c5c14080c003c0f60b1a05016001032110700684602030100d5000a2910f800742c0c40f01d13550031090f4581380d001e80100e403004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 423272688 1250 423271438 423271441
    0x9020310090f1b0f08070b0910020f01110720010e060a030603082208070305030403060c17090601061b050a0609050a02060a050a031b1d0f060a02011a040203091e01060e 74
    0x140424500f2800342c2d244a45440d0724190b6403000d490380c5000768480c0d1064030f9014444500e0500e45181d01c0c40b1200110b00540d045088091005421120700b100700c0609104042280c40c02e000f03c100031405c3c01c20716512100e44041c0d80c1c40018000c040c04400c80341c0710b26000030302107282503c40e0f00104010341e80040c3e00c58444c002c1c040302d0480e07039404112600c03140e44481030008100340000b1700303c42140e8001e400b8514081c11900c50b0300c05005a03c1e000c500340105c040c11041c1195040c92100c1c402c0103e90045c000345c1d410202c008006080400d0601001800360070a28003240020590f20744459005100040c10745c1c2d1850003604000f238000003c4d5000310301103603d0460a4002009050304210350f602049130010310001e0030f0b500c507070034000800007ca112904008141404035103401180005181148515000000600c00c1d1b21013030403000140d45aa10440012001c6c0d000c6500c100c00840d000d50030b44c60412181b507038800c2c00b069103241a8041482c070682000d420350004018000074a0180180d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 423273938 1250 423272688 423272723
    0x9010303020613240e010509010b0907111f09110f0a0b07060f150e0c0a050a1b080d0b03010f0912050d0f09030e1002060f0a1d03030a0b01090909020310090f 69
    0x30a1002ca00c0175040d4209000540004810700c14800c0109000b4500c4410381c4800303808403050314115210007400e03c02d40440c060100224146121050604a004151b2800b00d203495204000210221406040b40c40101c0219036a0020240709680b604603642c0d860f403280b41008400b4050144865441904d0b00c0303001460204114404804da4000c0500c0f4102619803400c10409840b17502d820600040c41400803980c4180300304a44c40c10380c480303040c02d46210344598498807070320791000307c1d00e0380880e58030440000c1d035007000e00940840f0040a030303080082c240b6035200c0001901c210440c3d0810044002400c1400b000207a00c1202400c0071b02c00c0420900c11185800380804007043c064a21a030081c2c48441840ca10000f4414071a1041d0801086a0385070050310030081c04440105592031851400c406401e07500420141d44660041e5001103218800c0000140c091a001d0300024130380340c145405400540c4001444444e20000c00c00300140000d500c1c280401800ca6030303203008010320544640e990a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 423275188 1250 423273938 423273941
    0x50c0418061d09061b0901080603010b0a090c1403100e0403091802040306050c0a1d011403090c15120f070e0409060501090c0302040e010302060f04080610140901030302061324 77
    0x20545031041120f01a85801440c55002007540c8041d407171403e020406912294403a114983e00040040d00120b65054428006032400c00903030403502995030b40e2642d02c1c0030107600060a0340092034403200c0600e181040354207081003002c07600626058680e0301c0040740c00c01d4810304112000b8a1a50ba064030f441d06803c260902030750003403000395401d038188408076580e400c0d91001c40d020312040d0303200d8406144100c1e01c41c090300d6801c0580b59050024040718070342e81c1039050000b14802e0324504060725512641a0401440c18400d0100082c0b09000380810850060701c81111600071041c200703840296512100c0490b104101914010341241c02c000c034071030400c45c03613411442c140c401c0c3c048284144098560210100d008512911010f00c040704010009410500010548500d034180e0003883c0641b5603074620301c0e007001902c120011005100040201407412710307400b51044004c0360301220551468400960b00c80e000f0309540d0354075102420100400199031080816010a0005102840203140b0700390b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 423276438 1250 423275188 423275191
    0x1a1201090b0a141c030e1503060901080f0a03051e04120b01061e0e2106070806090c0315010c05010e010b041104051005030a3c050c0418061d 62
    0x20b000382002e00000c2180385040c1400303801d0510280200c040c5920542120300b032802101c0b020b80038081d5000e46848192075980556800b00c40001d045541c900b4094144131100005034003682d1a07402100300c0c0b02c0501d41c08a01d883c85c4030741502d0026150100e17640c00082082540003100b0341c5002c0007070300040000c80c40c00d110440c0b601440c02c1e1403961380d035041e0076102e030149034210f21120510150182400d0303014402040001c0000b44c404002d4260340d01c40c810158407524040e081680c404020480c82c690b101c3d0300315a0140c4142d500641600b80404d14680070300019048080c07850300d5440d00d000ca0b920942c42d103144507421a00078041d03015240c08581c003d280b5071205a0250b41401c0400c40d854900800300c80480c1c0020380344101c0c14681030000c49080c2c1002d000b40303940d162a20000322080b0041c216410150101254003084450507480440f9584a03450032106010700340810000c100c1c1194040c1c1d4215841c8110941c40344500c0c180748002003102e508018403051501200f101c100c03100c804150b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 423277688 1250 423276438 423276461
    0xe0d0c080118050d180b070c030b1609030b1317040501120605152a011406010c120f02160e0601140301030f02010e04060e04050d030605010c0c1a120109 67
    0xb0003080418207040401c10080b40c1010b402e81c1d01c01c42c40b4020040c07113110701881060110010741c00580c1ca402c41580541d0103940b064070100701d208406e00900115002031500038068683c1110b55004809014064034083d10001d0407040c03000c6c1c009040f104060382520742d402d620106d00b031070900010000207002e4105005550028403840e000c9254032034580300309016600000c0000610445407854070603e644002c20401f9140f03115808211600d0130031056801c41076450380003284140308280001219000142401c0c10400c024054802103a19482404e041c2a440d03c0e091080d60781c1402d05138509114858542e00080451f040003440410400b804d90180350241d03a0906450720000400c03856001c00c2c000036020400c00b204c00d50056024249400100b00042c00224015603100c08140d60380300b04440030350701a003190b1000b810759a810300c51440986400d09100600400646518103170300d135203005403502c204c01041c0006a028500090301d100301c04207401c1c51003a43e140d000f020084c20001c070a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 423278938 1250 423277688 423277691
    0x1091a10121506080a020c010912091a19031d03040f05030c12030d1a060c060f090d0e04180c061716082a0414030c061e0a0e0d0c0801 59
    0x448a01e905801410103d4007541d480b40c032540c486510100007075010b140f0444c00d940d80da1542000003110fa280450707030452035840e0450320030301d08888503000e0084044072000c8940104544005046451007120004480386000a040d90081c0f01030204a1000704446030f9521000c680000c0c25150001d052003680c00503010758800f0b428141c00d200855a1080d101c075042e42043c090804c0d4800103600220b0001c030000083c01000c420100402c904d58840b801c0643d0a4021408001884820311106600254110000c0074140c174400801400b50b40401003040c402c90301e50240b2080b242b40740090a44440e0130074030440300b8607512603000e010b551126a006559480b10000290491410301c0560500300c1c042e00c80e42001c1d6200411042d4682c1000084242078461045c00860018018082c201800d0b0702112680728103d410100340c900139002c14000d10135503040200802a9900702d410021040315900e0103516100255070640320034071000c03049500208030303030051024460340d818040204e60f4460b00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 423280188 1250 423278938 423278951
    0x20616030201110f030402190b0d0f0c020c150a0504090e0606090a0204030f0b19050f100f08030d0b0303190206070f0c0507181409030c0105060105070b01091a1012 72
    0x201840341c0c00340201c0b445890201780001405800c3c060240360350a40481c0c01c21004a4880c440140e841d00081541075203203903a03900315140c207641403007071041c1c458180c0000e004070105a00000c0d014080c0c64983c8184101c0890301650803401b420a44024000c404400d1129100c80703402c059607250100ea542d0300c00d001d0080440d1802034244201da080d65004000030b01c5001840d00d8628003000c000d40148595500198000d04410142c450107000e0080740003081407904000508059a00d0700e900400040e240e00901089641400000c8400d21010341c072010070001e000b500020300314000e2807101c00d0010300340104208030300c0d80410704510840960700ca003607801c16900800c6403e0150700100510b164007280041c4000d1600b26601603600310f103460089020a4410f211001c058011394410046900200300100015000e0064942c000c0c4286045c03410b2001640740c001100c40184155240c0d540e40e803c09844102040d0800c203806240505080c0c1e0a00040714020144486824a86410362401c03c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 423281438 1250 423280188 423280211
    0x2092206020714070b0c12090d061a090c040e060f04090b0705090103050c0a0e040b0415030309050a0806070f03020702040209060720040b01051b010b09010f06090b0304020105040314010603020616030201 89
    0x109a900c6c58144400070640740040da100040d060b1300606609a20607906051b41000540034000d0301c00c078104a107081d8004080311010306c00c16100142c2030b803001113814803050140c800d80e64040e5174898802c80d003002030310202102090080101e0b0402405c03800074081040310458209004000c000002c2e60200301ca5a50001c03880001d000d103242420000780548034800d80b074071301a00a10305000b0300520000d28407001c03023028401021140d000320045140107004000d00d180224030480103006510182101d03241c1020000e2408c0d040d880548107242d4003040050a544807581a20000840a003a1903551380c0b5609017040e802480313a65940c8016101500807441d82018000c8040105040c1c44441c24482c0c80c00202c3c40d0191000c4c01e03040b266581c0c0354803003415550314511034020162031446d026040c2c2030560040540750180c028040700d080800c14400141d038044202c9080340e4100c44844134820b444151180500001c1d0f02c06544004085440320120070070b621424103c0e071103600204518010407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 423282688 1250 423281438 423281459
    0x12030309031306140d05061504060c0302060915010e04030216240e0f0f0f030105070c050d0804051903050d06060f0207050906130b011707030506011103070209220602071407 76
    0x240480503034480d0a105c0180d02d000c0503040700c0d802c4540180f01c140c1c003021401d5106c94507005a4066000500014168001d25806022440d005a0508050804031943d0702c03131800c5084041c841e11a0402d444000a001c2c14403d000c8042d00d5441813400a00d210fa40f01144040b0081031462607160f07414580e811415203000f00c038207030000c5001030035917022071250b001008122a6000113058021040c4941c52803587d8081c03107007030f100c0c1c03d0544403004041110f00348985407240010404c0700344124601403001284000440358100f207045814400702d0b440d2441c046030300d402280e6610800c181001c1000c240c00b030b0400c000d101d05070504c2d8204c541d01946ca40403c00004000d441080c0c1107a4000b45c48603211906800c91201030f4818100142c010058031007016046004592000c0040c2d5942d041c00001c1d030380000ea0a0240000f800250b0030000f0b142c00140c40d03e44003030300c5002015900103900000014054041e002607400c190119202c0410741050310b82444101e10829aa000c3c6c88004034805031076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 423283938 1250 423282688 423282707
    0x5010f0215070e0f0402120a1b02120901030207051504051002090a05060f070c030b01031b060816031d0105041a070c1203140115030b010f020a060b12030309031306 72
    0x1520034a08592100c0d4400e4562018036078601340c1240c50340c0004090b54507240001c1c9285030441403005036615184071705400711015110b0300920080074089004c0e03803070781c00a095840d2111410b0340554a541e9000160020300c24600000d00e14060449032068445001d403149209034080c0041e115070321a2007159500701c0c03154004c0c60b5030105440c101070101d824103901600d10840c0b1405124504032088e01c0b03d1000402e66403048800b074158400510420002001050824009020b00002c060900314040d1003c40024505030200e2507075202c2c01e1030b180c821b81210702c4d00b50000b03291a2044100d540c0752070181000301c40035544045601d030841020422154514413421455540080c14070342541c40350420248482c03810308045d01c600d89940c0d103203100c1c034000d03000b070058400c681030b505440400513042d41e070f0012016040c000e41c4450800003e80208003101a2944400d00080650035980003452a1034040d000c9001d604c4040100072200c0340020040c00b41c4c2d0031740d14469122903075403c4100c0d100e050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 423285188 1250 423283938 423283963
    0x1509090b06270c0d141506031003060203190e1e06010f0308070809060307120b04090201051e070506040516120507030b0919080d0c08010311120f030a080105010f02 72
    0x6007444070304002c1041c4500310303030000c4414000525100c1d1302e01801c019a81d9540b419502003001c5018000c00c9041e0118207042c13404241ca0460540c0f81c8401c514501d86c1252001130002d940010016049103025207a544034402c0c0c80b40200100007030f1140c4103982d4254420405403002c801c00c3c0e1141800000a50706048980b441c44c00001c070303400c55139040d009402407002110f0246040c0b10301c3c20039070362b414051481107032517940b04141c0081290f40e10058400440603640a10319094864001d030340d0007400c45d010000f40a0790242002228696800203219004003e0320310b000d0581800304000e800700d0507000107800460b4504000f5180c0c0211b03030505940c040014002d901c40c0004000080d42c6850780740d42b268000c415a9a0140c0e103010680107d580d480045401c528002402c00560040e8803418411071081d2400710900e60555032091080030324010803c1c03086502c01d40c10078010f00c0400c444840000b00c81c051700d80303c0134100c4c0090000c050070b000e40c0c1d000c901e958400e100401c1c07001668800d2440e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 423286438 1250 423285188 423285229
    0xc0d050319020403020d020f010c052e05131b050301022814070308151306090e0c0d06091719031419050606160506160903051002030601031509090b06 66
    0x1b034540c20000e032040d4032a4024103001400d0104000304400f8091044500c00f40c0075200e43c200882001d82464070b64409101c0c0780545000f040c080b07a02245130109003580d9000400703409006d901105805200c0789544110f50543c0006200408046c461342d07148580b01d1084240f60f0000c52800303007900c8509850105440c0031400b8000000071a1041e40f415800461b40d024400a290b042c501180c8080d504003505003c4645401c1c0801c5066550700c40c1c0c412901042c009400ca5880b0b03100012002000703018080d10541d240c00c44203003407081444220b02c025505120380f690b900340000b4001d41c030041408410020928190b00d84c0c00b001d42c41003842d032103408280d0500c00c0030712075035401a0040cc400b90441d038100809105070410000541c0100c08030901440042c100b92403e04484403881d50b907103090702e042200b510820030000e000096400648101c0040c00350f184c0d074605004034010660328182c031001c4d4500d04000280000203603c504001801800d003802542d4644040c00400d0042c2c00e134245410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 423287688 1250 423286438 423286459
    0x705070512120d020405041a03070603150618080105090f0105071803020402070f02060f041a0a050a0503070203130b040914160c03030e0a0507180e1c02030c0d05031902040302 77
    0x100310060180900d07500005090030781b140c3c0800c0841e094100e11501c8540070741c0004100c1d203002c2121100500706481c05018010340c10124590f003c0751403280006000050000c04100000b2100700009440c000f002041a0718100c40005d58910030403200580c107510b041c0200300c1c0c02e803084510801e848032120740004a00e283d070382440002e40c00b248081d140c1500840440b80183d58460060070420049000191038505110210f075aa440340807030b500140100f001070030307038460b0441c4c00c0e20482440717410119103070f0361088816400c521564584e0005140e0404010501141000150003130b500c094600704a003250740e02d0004a1100141c070440e200440300b01e9801c90803803044514815551080c5000300310310034140d44051402045440882c1e140d0083d810a100d26010b000b00864088039140040c400d8542c00b202107500d4075a6044c401020844201210305810300800c121840c5e6040301d400c480c14450b03071030b10082060300140d17501c1000c1040107040c0c44e000c031000e00944043d60380082160318035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 423288938 1250 423287688 423287713
    0x20303061914060f0c010507110721020d021203071b12150c050d06030c0303030e0d0905012313050102010f0b03030d0c141306020606010926010f060b0705070512 71
    0x2c0b0b422020090058a07410045d00e010313200e0a004642c040c8c2d005441d01c00c0104118540301d400e100c496003000c0c501c00104511542c600c03070242d84940c032046d01a13481c8021800f103400418036010310004034140394840010310800300a10006e003200340752140c400102d5180d031550841e00c40940700d2200540040d101c914442500704c4c0607844604ca5062905001d4940b2100c64006015207503d54015264010480c00800074550140162540d18868802038107a100c0700b201c002e41a40c00901800e07040102c03107094031400c121000c8241001c407020015880d10b51411802c1c00d000b15240b030180d9401035080125081480c0c241b802400c6842c00020f001e14140018a94984014000c100d0300d201000100ca45030950750b000e507001041d20b48908000d440c1802d0611401a242103406080c0e5410010a82c0d81004042c044c80500700344040e8255859810103014180c0d54050f1403815048290685461000141c40c0d140d071004202c5a44070300c0c10f4840c07050b600d000b00701c20f6042c04c400c10707036540c2c120001c411030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 423290188 1250 423288938 423288949
    0x902030606011805100504090e0312011e0b070609050114241c0c330f17010602150c0304080a120f020d05040303200a050c01020c0d020303061914 64
    0xb160b20040d400e4481541c2d43e80005401c4080e00c038021020400c0003601740700c8e1010300d01a0304031803c4c03034400841c84d1200d40d1b064403030001e505100b855100c00d18080c0d90741c4071081c5810a8001004200700198403542d00d42403040007000c03104000c030340d2903280019078030458000c0358015105903441c08181000a0301080b41c581c513001110f03d02984016010602c04005810310b04031070310130b03008040201c10b075420701d030070310b8100201246140e0302c41c11682214000002140c84141e5440c88074646090081c543d00d90543c0c00034070001000b110704603000008500b1950000d1103000c0000c0b180808540354688003006080c900c0b00362009050b0308010003051124074043d44140c01041c241604c0002d030141c104640108036004501c600308540c2d100c0040c41300b4581e05000d52a030000e01907003070400202c450f0072880310720702c00c0002c9003003400004691546e041d40c0a6040e00c0c00c180d0a4000d548440304055802501c1f82e0040b20141e20880d060851600381d041d01d8142d03c030039070301c0d00d810403074074040003008004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 423291438 1250 423290188 423290207
    0x6080c0105090109050303120f07112a0405041514040803040f0510060e0a06060302270d02191a0309070501050f0c01020a0206061f0804060906020c0a080d0609090203060601 76
    0x741449104c1c100060291002c0004000c2e040082c20101d0060502510f030305030044010303012808101c0c022210600710900403e51840402c0d08144010501038820350000c806807000c0c44441d40189130608100601c44600e0740091603902c4590b040121030300c2510410900c070820f0382c014010007010b01c0080c001528080c40d000100c0e002d81c040b03031050564806004151081500581d400034048418045180c0c460301491028000a0130150305003185c0040301d02818640813a1203a054500d400740808070344540c200d081c01143c002e480342d841100255640c0001c5952442154881d4003290200012041c0080c00d82c0c0c00b031403205015050980c030300340044445d81c100c0002d09000d0b40040203500d031300c044244014120315045402508407850300301c08009a566080c05103000c0324000c03064018920340d100610a90050380b103100000c0a1403d0b040c800c00900506001c21036910840248405000250028202c1c8116001c3c00b48031483c3c580d0106800e54901ca08000d42652000001c40d43c00e6008541d0032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 423292688 1250 423291438 423291457
    0x21c05180a0309060305130f0303050c16050304030c05040b060f25030c0b0901021e13090509100f0b131a0a060903020918030415020102070606061d0406080c0105 71
    0x55162400300035498184848036204034041144040100130b42034040c05540d600440c480030284e448407458035880405a5282c20003820990381d0f00000c1c2040c5104810f490110b0000168001180c103e440c003569a580580010707588000b042c00005264a014010200c85180190034642404003030490081c194200e00020b90a8411024551941c444a80c0704d8407180341c001e03658000312506d3f600303289060708006084041c1590041141c80f00e002420b204140c08400322141e416940c0708031516a400d080e1003500081640707801e000900036142d4002609041c800101c010410011078500c890030210b40052a606800c0b2000501c012010300700359001c030203c00c0980800207d41c254620001741c20340302ca60080408900c410a0601c29801d000301125404560540c82c5440010500c58255680c0542d1044107000080111000d0020b40b00f074040d5004103501100a01c9015220301014001e0940d01424004c60100a00424528903041c051301c070865400c41c001e0420400d60000445940c3c0c09241c81 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 423293938 1250 423292688 423292711
    0x8240610021e1911040e0a03020606011805030f2b08070e0423190203010305060103020913080408010204060f0e2b021f080106020a0305040501030519021b070801021c05 74
    0xb0403144450a1029020303d403042e51410400a503080401040b5941000e4880007030b4040380b50030340081d800040705500700c8001d0901982d46282880f00310350080040d085190140601058204030446c0012148046443c41c9880305080d0408000301801c2c3c810302044100190035080070441180c010f2244c8454040b000d400400c102142107680c089812103988610684241d540c10803040c03903401590546070006200e0b0962440d49181c480c04e50703540c41030002910030310a480c00300b055412101a46401d065101100c0e0351915a00c4110500075045442118082480400c642c900c00b48a00e034a0030180d0703c004c0c00101e0003004800c14440340640d4001e10304080700c83c0643c000240e80c51014a000b920b9415000304440c28a1210003001c00006912000030b550040c0300410003e03400c00c0c15182030300d80a02e40002d013941c51425001840100032440c1601d0303403002075224000040a4060b028102d4004111a03006540f044500c0c201c0c8a2b84005000158070118a0310906030aa00699004400c2560 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 423295188 1250 423293938 423293953
    0x30513150f0f0921111506060c0609060603070609060516150908031f03020105030712090f05060603070f0f091d010606110706020705131508240610021e 67
    0x310080341d000100a569111150078030140031000c0c4803104c942c0041a14000309814444030b0304a581e080c84003c14810108141e0004100f51030340e105940800310510101c641c0b6040c440e240e10303100d107425540907000b401046800f00701d05005e540340c9401c0307a01c195209172410307001100368520140a07860455090104854515024620f4050300c11824054541c5a9a90520036105150310b10858100c000c241c21613601080580c3e040010713203a0000081c1480ca5916490201c510024009050020030021303210ba103520500c000050705603c10030051382202c0031551a50031850403408640310307001d10405195028401420340d40c0128060646400c2412001503500351001e003501c8158001d4800141348040c0d1380c4412000700f00e544000c00c91400600354007420034000c1401e0b5a04460005000c40e01e0701d0400c0400c3c04807140c41001881514141d6860800d0b5210310101030040c072107641031100d140307404184e651408988400340380d21150000d02000c0f032030030902c41d20f00c0f0a802d00b14039035000314507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 423296438 1250 423295188 423295211
    0x30411030f0d0302040906050d030c080706200702120c100f03090b01120201021b0918100c030c0e04270c0f0b07021302070f1403091906030513150f 65
    0x12102e00500c1c2c030b015813654200040c83c0212980ca50110748100600310040d000709401840b80206160007071b5410380e480b8103600b00314024003a09404080260501d160000a20355840054100b00d0702c200c03105540b6607244824981e440340c1c4003182c039a11044100011750624010000340c484101c941c00c011501c528a03407603104034800268460b12013140e158054104569040c80300890600b9042440132000c0142001b00b07003001c0e07009204000c00c82d141014071001102c10880c3c82d00384651103000340220560843e000b0041c02441841c03a0108146ca28039040f503241a01a00c0d040d0507003d05883c46c1c0340400c1d03d220a24030340802040c0c1c4d400d109110b010424021403c000405051545e0410307582d85058410f01c140b80c2d0400398030a00040c410b10000e0300084090134000e040301e0308070429500803040c42d081d19086110f0b206600b0303130140c0e403c0000c981c3d00d042c0c491003500311540b80d1010043c568a540e603400a422120000030006818888120115001c0da40203a10309004020001125075084 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 423297688 1250 423296438 423296443
    0x41a0306180c04051e010503120904050a09020d0c0e01080703030203160f0506010e070f03060e15120a030c0203010606032a0201180819030209180c071b031101020a08030411030f 78
    0xe94049202400800010070200710f14503901c1e0060206400800076840c0f002500c4027280640d00d09076110380c2e00c61020501c607142170741100d80b07202c0d0001d28801c02e0030310701c2c5032500d0a03440394410029146203082c00000c0c1c000c0007040350401c40340c058000d5403801c00065511110011000000c64081d4004448040031540400c2002c1c06040c031300900c05902d0401348005002c8145820310300d4105820101c0070b000c0e1900c000a03a0341c001c4c1001a605070400503110000b0121102228420318900c1040d003160141607105020050300790080e002088002d0b1580f404034265080100c180c1c2c44111542130000304000850f000c101282c800d4400002c5110075500601101800c0c9201511106030100d00300c4000300032054080402c0a45003411460042401c01043c00114032030a000440228000011900440801210f900c25807144881c00700f92a1301084051500c464002560101403040c1215255400003449900c0765820003103040c1103560316610b144500c0e4240c907090b0b425001c0c0c0c03000e0038880c0504 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 423298938 1250 423297688 423297691
    0x60203090304083c0120042102090117010204030b0f09012405121002040603060f060c0b0103111c0b07030b03060c030f0c040314010902041a0306180c0405 68
    0x32038000c0c60792189400c80301071400840d48800c400e0503a1000301d1514265049a41c01c0b003149040640fa08991042c070a0140107240d0f45181001c11418110100d5001d00300070000e2003550360182c1c111654550310880e2010720009076100940006260005004070f0b18034400040e9a0003403e400945480d03142c0e030304c1c50030032407055410104104004060080040080c01170700c00d02c2d2a103450301e0075888034141e13803450403482c6e91041c14024180700d41d08101c02c060a022140046052800540d506d0783e076041c1c001c00401c80340c8610421944003000c041750300da01c21039140c16060341000060540c1c2e421034403107120a00b03100c080c0540c401d5150480300c00904e44803000c20191800707100d02022074505148060180d40196580a200790050f02c204543e018800d019a60803004e400a000026070307861520034014400c0d0f400250201e614040e13100030400d0150007100c1d21600c2914140f02c0c420301242403a0b545424540c8855042e0804400500d9401c40510b01124411403203003100c4035804140007103812a40c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 423300188 1250 423298938 423298951
    0x161e0b0d0e0f030c0615190e070c051603030201150b1e04151206060507050a0f0f0804080a0512030712050712021c05060d0812040807020411030a0e0c010905090a09060203 75
    0x16010800f20512003100c803046e5040960700b082010000b00a400803007400d5010380384c129404400460080c82c419001980080d52203011605065580e0002d103c3c0b03445e040c07000310700540c20b202c18151030303500800c078900881ea405e40501e420040140510403180d44041010503c032030303092000186180c50400c503c0a09003103034032656a9040701459490584225800c80c40a10000b00010400100001058200b00b80c0008290155140c1458861480001e4080142c4480004a404506541d020801004691007081101ea06807202034407a0118007040703c03d2030109030101d4004042495076006540c1c45180751070200c65059240e00703404101e80000c0c482e90b864203012048400c03a40c060307200d070303681000041341d988070807841c6039a941c0e0140c4a600018400303103100d2400700f02001209020303600040e500074424061055078584030b6400b50070803114010083d040980b12401e43c180407032010302c608010307516000242d08240501c1030040c400b42c46d20a1845c1c1d0703450a41c000c81c001d44065401840c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 423301438 1250 423300188 423300193
    0x130f0203070f09080c010810030203010603150e010908032404060902070c0b030121050a121e090302060414030c0d05010b0306010e06090604050702030c161e0b0d0e0f030c 75
    0x286168000d04030724008455806110f4107100a0000303580c0000c1d2004001000d1900780309641ea0b00c10306a11200d1503a00c000d415608000c0d001c0204507400b1841041e44c001d0040070002c075400c440400f802d0325100c01024003900e05c10000b2540e4a803245242030340958420360b1410007030b41c244c00441d049070701640c088607079180d0103c9d99204000107010144010103143c6442411541401402e08a28003240c1c04070241d00b4189020b0802c0020621451004130f030007540c030100c81c0b40400800380c010500c0100a41346118100144100c1354041d002c1c840c16290007814860401d030a2182c11000115402c80a07a4144140c5280100307075921181c05030b00c8184100d0012907480282028545030a0040c1c00c1800030b0321280c0d04004207515a45c2c0101d6101204650100352619101e03004d078114496400d001141d40070b2400345e041c81210060314681240d140c0c021642a252078810080300c21078103406484200f5204200b5038140d03003010b41240c071044075110140c8000a104c192000e1442c0e07c0140f0300c04498 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 423302688 1250 423301438 423301441
    0xf12040f0b0f2e05040b0d0f11120318041503080409060611070602100c030212130209060402121518040312291003150e06130e060c09130f0203 63
    0x5a40b442050881404a081c1c1070341c0e600c82c1082c2d624610503000f028016682e91186e142e1307036560700d0600d2003001c1d0880318100090145007040c104010804603810b0083c081001104140c010000c22580c2400412000c080c13009401c1c000c10024103400700800164001151011021404020040c002402c15007000504103241c4840941503c0c1d400c0d4003d40540c100c080c081100e15008a200f03800c0403103043e0000f0710540440415070007402107103041001c2a40d840300700030180400002a44209000700c0720081e007640c0b560100710170380c07107075450040040302158045403c0001f0030442c032042e080010100703140c811042d4080e10742000116019000035940c2d12600c2000c9910348110b0900c00541040e00b00121000e481e100005c030248501c0c2406098213000007170a25110350300841001e510074924512044c0d5071281e031031002a06503016403042c1c9041c08008180c20444c0700301c0080061a9010701032aa5500f6140c1405410042d030315034114071440d80c41c0c0301c01d513240d1080c030307214180c11403006807603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 423303938 1250 423302688 423302701
    0x507050a02090a0f180b250809030f0301060c030e190506070501020405040207080301141005071b050a2c100e040f0606030f0308060a0b03011401111b12030f12040f0b0f 74
    0x15540141008441c1754020f0300d400038611500c00c1f26400c46941d03007400205038a407a034240b031640c45400707040d0b01140300200011800c00da000810003942402503a8103620113a4003c1004003c02035003480301c49516211500300708500f042c1d005089918001c5000508043d990360218042e030b07000f054115002880080103102c0d41d103918a41d8014a0070076030708031a407a10740300301c0548940706925000e007400d070800c407100010f8200b46038018040d040c040d00506e96547c1c3c618007102e44420780040c0b0101e2000d09565000301103a4601d110340314071480d28003e0100c07450030b1007429580304054002d03a6107020380c100c100c5c0440c2e070b9070041100840c032940c4141000c0e085070800426032180640300034802d280c001002c002d0100c5c14010703203064402109056022490020041e10000790b001c5400d03a1070300816491100701c22100c1c805145030101610303180e800d608030114181d164841c07210100c511800c18008101e070055a2455558014400c07010410040c015840e1340811140c200e40720440c28415000b000203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 423305188 1250 423303938 423303953
    0x2100f050609010b07051527030a1d1c05030d06141302030609150f03010f0b01030c090b0a140c030c0d0f02010204080a0f080403080d15060507050a02090a0f18 70
    0x4004c5a00c071141042e900c0e9803080c1d207400341c42ca1001500340410300810032002021081d1210020b01d00500c03c2c1d00800b03650041d499400c100050404a952141c6004501070b2410090f424482c00410301c6d405088066071940390203c403d0f106982e5440b0901140081c100944640c0d00a03240b00f40d000005c1d00f40c44c02c00c201c44c07519050a20b0105a00500620810362244400c041e001f1200d40300031a11b52440101190740d2034a508195949076092070b80c00446c08507582d202c1c1c501160b0a80c1c09200c0403034031078004d8944000500c04c40150b070a042002d0312500d4454100301115421510780765140841d030303040c4035141d40c00c042c00f98445600200b8079040ba0f2500801e1403032040c41a40000d6041514110980751038610041d400f401160041603a02c08100ca44400c0320080c0d40e1090099880e141d0328198000103003c2c1d5040c52001254010001c5920b0b40148191f9804640c00b60042c80c41c0070959003880894040a401d01041540751019a1200040b0780105020394019208828000145091400c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 423306438 1250 423305188 423305191
    0x10501090b090904020616080912060402010c030809101d010b0a05060a080613020703090806010905040b06012102180a0504020f090120061e07140a0c020102100f050609 74
    0x9051000e01802080a00d04507030540b90101d8048600c2c05aa694074008201d06104448454481d407a8005505081001c01c0c0041c000240d8262005d060284507a51031035540c40b0140c2c1d029021440080d40c42000a1003801e82c41d500401e8070044d078105c44da004281c03a068400382c407a0300101850f095032100214000344910035000710122210007000d850000844c03403e1181640303480030070051900140c52030b115880c1062840c1d6070300780110346d0740925040082840d41b0714058840340c1c1c00b07880000101d907040c07401064001c2d5000303100c1c0002601c6d42c2005583e0803508014400341d01840518052100c4154405800c180d040a8500134a03035800008002a990b0a80c06c1203228a1060180c800800c4c1004151001d46000b800c2601d0a9a802c050703044200300303140010905486920708018800030303282072891140b611541c1110003510b44480c191901c1111030b408074410340c0d05010003a4050312540c00107281c0307030040c01900d00d03a004c40e07072166080c0da031800b0102808940315001e01071617003005035549 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 423307688 1250 423306438 423306449
    0xd2d0308060a1a0c03040f08030408150c04090b010e130c1b0b0408070c030f080a140901020c090604020c0601120c051903020402031e090a0219061b061d0f010501 71
    0xc2c012504002d4400060116907400c504502e00c0411001900842002140c0145c42c00040c603505d5540d031b130000142d0b01d40c800d000744140307401404644d02552075800404e500801000101c1e07420203003880c0d07505c0e001b041070950884c10040130b0882e00c5519185d000c407185151401c5500031030003d40c401806000c81000c1c1c405104411002c01d000804140127411182e0050303406503900b0382d14407150410301c42090044e000a440c54074100d84000801c100100101100b43c07080d290000d6241010b10385207410700600888a0140e040300c0302e290024509005680d5100a000344014117058600407428030b4400700349c00012018049811b01410f00030349071203110041c03c08840b840c4c0c8420000c08407d9100340d05201c002e01403034001c0041515690500f0500540b0b1740c4500c016192850314883d001c0e03685007002d00507405088561241c50803003001204000a9400c661200c1040d59207214204060510400051300c50316519640c5291145240742e5400b15281c0350001401011075642d40d0b83d08680069100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 423308938 1250 423307688 423307699
    0x80702010c05090d1101090513050601020709060815040219141801030804091a06030403050901090e0105030c1e030a050304060908010506210a231006050f0d2d030806 73
    0x401c036075582c0d0041c80d9904141e11140c0007071705102d001c1c016202c6d84400c1d00260f50281c0351401c0b6031080e018039440584074000903401c5420442c0d40d03541090850704036004200c1e894005800d038003601c00f103407418a50490b10207850002c0080280510b41c01c100c1041d00800000495a10a40002c0c907021003070704021040444a002d4652441e80c3d031020521a0313104a00340c10351550500c41c10202400c9030042c0e040006003d840e81c07850300b803900034240d6000c6003581d40030809104003c0340181d0418000e506031040640240556074036902004036002c0226520b1840da418130b08a400d16441c14425108568803e60003143c0344d9080441c0600080780503005800542c1c9840c04001443c0e42d811107065102c0920001d01901c103008081840c10065650340140c45965071818800d2241080c14035000744a0720300b01540c03e14106c45c0d81010546074117101c0c50740c4c00304c1c512007024034a2400c802c0e2402014450f0301c1c03000c0300070088440b0b0380c1c06800319520f04c24040000c88070007040c143c220a040354004422600d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 423310188 1250 423308938 423308947
    0x6081216022110020306040509070e0a022b0504021c0209072601060206010609090b06030a02090a0e01030b100608040317071b1b052b0c050907080702010c05 69
    0x146038019020000020703101da01ca0a0500c0781c418008110802c80c1c2145105803600c1540403410140694002d0b950140228680000a00002c030045124801e41d0050110f4020341e45400d591000a50001c08620788160500c2c55402150201e8840200a10041c440c010a00c0e151a0040110b85c107110041a41002c041c1c030b11844c01a6a41c0503855032003c04d45c24490612074044000403c00e80d10b118281d030602e0a29000400d502e5000102da41c1210a144c0e50a00641d8884005000381d0b000c009140d5044442072012414040c0030360080d24a04001412031145181d5900011510050a0380182c0e04c04507100180444030659114000260403c1d090003801c0b0301f000c0c0d4004294038545204a1169144200490080e82c424031071440c0d20180707030061001e00e9119007052499102c0810710007a520034485130001e10742c1040b240805450300e5104101d6061b412143c00190b400c0303120380c82200c00c1080d10f80041415955114281d0155089548600b441d01d4070440c06800c40780714051200600a0510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 423311438 1250 423310188 423310207
    0x9140f0112061d060a0b120a110f040e0601180605090702060a090c0807060917060c0301030f05010b0904030503061809030d20040e070215040201090302060304051609060812 76
    0x440701600254040400904811403046109580c03038150702940c42d40c024601448803101403070b00070039040a4121204400c495100c0c0d21940c0d0354503204001048000310341e10131811440d00442d40c42c0b120344007400104500e070130720300210f080960903001114100c107484002c1141540e0b80c804c0b1000f401096500080380c1c105804003a40d24100206101200ba498076000e500b04600c80038040001d16901c1c2c11604800c0c1c03540e00140203003d803801001e41010340a401806550400a4040d00074000448200e1859081d5155002060160201903605640340c41942c11251140000a8401d9000b980c603241c59090030010000013f0410328044d0380c1041c4001840300e07241011040380da030030346400c81c0020070315145a1860781d480800b0840310200d0324042130010791017000300f402902c40c041382e500765510401a540c01445201d025940640000e50f40c500500050422000660b0414040c0c0e040f02c480030100c5070741c0300b11601c464009602c03d54a50104000c10b2808028440800c1c50f0b451520b400c000380171 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 423312688 1250 423311438 423311459
    0x201050405210f01140a02120105091b0d050a180302121b03070503091009140108090c030105071e0305371802010917060c0d021309140f01 61
    0x1070164034071403031601950003000030031089555090340318101030780c84261201500a00030201a0215400414240002148219240308450030446036094813401642410300f88001d500000304480400c6003c4201d00f000381c10340344003070401da0060840100c1c80f0b1030300d04203480640d00c014000007040140c1484120000350007040703010f0b140c44030115040c0c4402104010307416003411101100b031381d80000201d1200b27218002c0002c1c113005e5410760300252070000e400d1080b15680c0e0380d88901d444030000b1050840c00c96210321a00d0390001c040604079841c2c4c00500c800a0b085403c261082c0b400701e035030704e84103208041c00441850003a550030709041200746400b8954220900c540098040c10101d020b01c4076602da84025820040002810006c0021000c0091200381414032020309a000c6110f1620015880c80c0c0d44d5500392621101001401207038030703540d1100c0f40c0c540081043c0743d4225024040c84030440c001c2540d17a40205100c04001c1440342c9051103010030610040c2960900901d008010b01084190 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 423313938 1250 423312688 423312697
    0x6051008090607110c12101104030308010513020904140901060b0a120c170109060503011d030702010c0501181a070c05030a080a090f05031305031606031a0402031e13020105 76
    0xc0c04d000c0031403030740320700b8180c00e001200c030b800b6501104000c41d4003105031000902400d04100090104284072007034001ca0610b0080d484020001003004006000d5810001d20780c0010107032248016081c80810300008054421286891041c003d00004111001000340141c50080c22030014242c9409040305005102c644080c43c1ca1001742d0f1102d01500086126203458410b2051240d09100344c0c1d6100c1584102505251140038440c0d800d102001170803400c000a08030740b241d0264025841c000740c40d40151030050130510103450075540c035061911300009504c04107181600c03400c000203100c4d12084410b561448090310300e09c01c100d018069000040c00010458140c0c2026051a8036290703104a44034002c0c0c81800300003010345d00c1c0c2c01d00440401034004003400840b501d16008808264988091680d1008101c60361441a0400751040110341d009900103202080b2040986007114469070105007a6803041d07607400181a114071040c9150082d5904840d002035041700030840c400a2500000c065000303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 423315188 1250 423313938 423313951
    0x807080a140d0c1e0c1b08061303030c0206100e06120f0d02070f080a0803040c08030a03020d0b0f060d0b040e0a05060103020a0803130b09130606050421120e031f060510080906 77
    0x1482d012402c2c801106006d401001b012040b00d80d24a00f29122451103001400210042030410104500c2c640c0042810382c81601124001801586030980444500d140078015a420a64801c20070040003010311980000c640c00d035000b00a09166a0002460328155501c08400d104c603001c2e040c458403102046081d03c40740c0001c00c0c243c0301e4480381040ea2444031290f01100d50381c4000511468202d804d42c002c0c0c52400d120300820081c42000f502400300241c081c0c02d44d603038049400c1010501e003040e0390b484411307081d50141000800024906025290007400703038041d21503074400c01c010011898100480e00c05080c40b00f01550a00950600f8001007450a0107920001c03500801d6900b61500c0c3d441341c00c08155a562410700c0400d0b90741d4405001035100340244211842001c81845d2902d00c040c2c404034110341e00043c084910003200f981190304920825004c4c0d458080c4400c41c5454442d6a1820040e0911031200066000c4ca800204500d00450007502c0f014048040c1c100070445c4030204189a2010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 423316438 1250 423315188 423315203
    0xf090b030d140d1a0405010e06090c130b21070207030519020f130c1d0d021315090b011b050d080403050c01090809030d0c0807080a140d0c1e0c 63
    0x841c1500d02035414054000c8010300303d441c04a0035400744c00c00070034400300014240c0f000c005590b00c504400784001411148a81c119081401243c003c00314040105600c7c912100c1603600d49860300c0b0410a10744c0211800310b440020642c41003104504442c1094004025000821850303285a03540c17525910783c18100d091140d00203100800b9912880300007009080f0003021880118600299a0000c3ca8807500110001e02140082035498104904100800c07000414001d00001035034200860760700710070000e41072039445540e800c41c04040b680c04c0c0800390042610100b01c1c400c42c0000108a8481d80843c011a803200b403944038040f50307020441d03a10301903851600d035249698504042e1a10303c01c0400e04021903107420345040a100185010f02409a0100d00b038030100448006d0486d14804010f50142041c0380c1000703800000740d981001407408190b40d0030304a420b0800b440103200c46801c51401e60b60200d494001f00741c01e0503404012600c003142101e000540e1480c5000c0c005142902c002002010310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 423317688 1250 423316438 423316457
    0xf0b030406180210140d020403030314061e0409140109030c05010e0105240d021f0305090f060f070c0507090b091e0601050c030f03040c080706030608121605070305070f090b030d 78
    0x1040c05170100ca00b085086081503544550300d14009000f082c150300241941403020020800b186407042110400c188806240001d419001007040000c0c00e03010001c80c0c51044d0780c140504a00c0d820300422040c64000c0d2140480d81a1904019095484003155807a01c0d9150000708002c6005180d04014220f21130040307000350380c401c0c801040301c0c0705030000c01a40c0305160140d442c80c14038000f201d45558072500d6405000e541c4400c08c0d110307900c01c3d0f41d4407102c0440e00580c00051a40351400c022a41c07280d075a1515070380000542c6c80340c0b418031f0f540750400401c0726200d040a001c14203009124940190703412000c1944c695076541d4903810040d0140c000d504200000440d0800b0310001c1007501d40e070542d4410314540d281843d151505d1034507500e00c41c449031400b451340b002451601a1085408031041c031400f81c03428000744490407010364000607540012400880d04800031850030495500038601c030b40b00030000181807000005030150300c0d44c0221146418038800f00340a8601140c014411482802c001031740 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 423318938 1250 423317688 423317717
    0x509060319020d06090605121b0d170f070303051303210f020c070602011118042a0306050901051215060d08030709031205070b0f0c040f0b030406180210 67
    0x1030312402500006690034004c0215145200d079200300c0031200c0880e8a294410400840103846150002c82c04032903004000d601404e504114081c035400ca441800030910284811707421030401d40010a220744191310225550b0105a0140f040b0b64020500d2a000746207091207543c000c1c0014a88090390440c03140080040c0c40a1005811030102106030003015904c03840c0458440340d44290703501c070b02c2d030040d0300b8540840300700314030780b022101c20b103000524851007200c01d142800050f1001018416900da001380075a5048990001c1e25001a800c2c0e0b43c0c0441c0141c40c28080011654042e04071a11551080c1d00c1c64904c4880000d5010346d860807482002026550100002c5c0001c840c20f0000d41884800000c010003158410800420b8922401038240c00f0b840d600d004032200c0c015141d006120003400804220148401c08105921031420001a07281c2601d40d403410711000c2c250340c8140b4440d4008001c3c4410031107107010314544802800103a1107443c240350009802101c01e07403e04c100b8400103c90591a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 423320188 1250 423318938 423318941
    0xa0b1e1003020f0a0c02100e090c28020f0105060a06020d030b0a030804030c09051e061e0a12021815240412020f0d031e09090c08160509060319 63
    0xc103d4020141949401112401402c5088810000c078400c01d8a4810050010b0107924040054140901400840d980c0d952551950b03a10000200d600c1106115a00071141c0c4a601c0320110f618982d030203484142c1001603c0d40c2034400281480d0310520306c0ba07800303010320750380010350031001e5519280c0810200302e10760111719201b6590300702601040740068080280300c0c03012002e87c1107c031860300030862503641d03604a50f0381540d00845281710b51072040c0411107501c3c2c032407444211001c01c200c4032183c4200040014134403120b0340d840010b0f0440c0703a00c044403d500d01804615841d0314912400d01562800c005030701000341e102d5401a01c01c209050f44000704800b245042d1703141e842d041d03d196039980c0c0c40341480d07010101d01d5801288100001d9000d040136051851035071440710fa08d0307110900c22840043c041d0001900c100d0742c0f00104036142b039002481880034042d980e404a1181c40d41d03581d50414000d0b26000b03d103503058440503c00d00b046a41190b888040480e90b01c00798101c091482440c48041303160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 423321438 1250 423320188 423320197
    0x906040c090321020601060e03030d0203190f0b01110c030d080c120405010f1a0a0b090103090827120d0c021f0906180509011701090c030602030a0b1e100302 69
    0x3011410b607070341c1020f04500300d441041c66580c20781d0200c1e800c585c0c1c0c0d0030040707424010b030b8035001da0103401c1800842e15841080e006990440303c4107403004000d410220351320045850b2031216462154503040352503000e5030000d0191045600060143c0440a000408643e039802240301c4101008210130002d90241442010341c1c0a04c0183c0703000401c2800c01d406d0443c041d06000400d940a545091000846208107070511210751001410400c100d5140c06809080d64010b08045414161103403100c000054008004151801400f0030b10b034a00c2030b01d40d0380180c02c490694400c9000b1201e01c01c0e01c000720303440016540100b2000c3c0c90102c3c4000c01c01c0c400315010b203008001d4a014440c04081010f4403540190754042502c500b5a643c0300c00342107120241c04034545a20403140c10041501c010f020361a22940c0c2e0804043c0742d01c00101e060482c668a00703030708500b0b03a441a24141c2c0d010080c0101c42086e0302808111200c100d0303503501c40154112824454200f2540464400da14844801610b2030085e0183c0e03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 423322688 1250 423321438 423321443
    0x1150e0901091a04050105100302180a02132c010803030406090f140114070f0e09040c1a1308030909010909020a090e0d0206100e010b0705160f03020306150906040c0903 74
    0x141200318502c0200b034401e0013035408841d2035080170006058050007484c0704089980041c0f80c03506d400d460790003d20a403113000d01403092107070302045400700241442600d01300511a0400590104100881070507120410103c000b07c802c440c000104540d040000030b981e0403503000703400001c0c003042510f0700b0744100c04104401444040d10003a558820481907100b00c402280350003034803d20399502801128520010092000400d103603018401c064200420965481481605043c9510345c17a1060b000781200d1940e40c40101460008403000c069031106450340c010700b0140e0055051483c4000040e103407a1341400340c1170000d55690074010035595204c0d0703900e00416206a0400010404081d060b441e200d041c0180c4000d4443c82000c901416141007644085682c0f004c00d036140c690806281040661140c0c03010b907054460800178035280000340308501d00800c2404166452a451481854104400185001d0100c5105400b0a800c0d48580d256a540110100c40c0020b08003050b0303a007507442c7d0440380c001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 423323938 1250 423322688 423322703
    0x14070305031c06180207060506010e01051e0d11040f1d0105010c0305070b0903090f060301050307030809010c0c08210a090e06040608010504060f06050316050d14030c0a021201150e090109 82
    0x2a1216080c0340d174020040d09000390414042d541e01c1d440152284440300d0300c010f000450402c603862060450700d08030750840003101000e43c9401d03c40b1180c10300791441c8203411800c080001404004071065941e1070360090241c4001d9803048440034444611003041407044071f05010210380c0b080c003010b1040048400b819803008401c416410309002d06660b0760007a201440c002c1c41c1d0720a40311320614060081d81c0c100e03103005006003071a40c15596003450942000d0702c01814031510103042d80c0040d1440341910f026098440003480880c0c100c0e41d1410620000a0318280d66001c03c2005583d10b981c40440c0c48282e403400a1007000c1c0e0344841c00400c0080019502c681c44030b520b81030074042000b1098000c010340d5400c80d80207200c00c540341c108060301c942c000041d001c40400e01090800030760400b20140382260707000d03260030101c0c00340380d88420f41507a202c084101069045040b5040031840c10115400d194040c0100820600d5a244034103d94141140980c404c0503d00c0c2e000100010001d402c1103142d550711410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 423325188 1250 423323938 423323969
    0xb010e180712110313020f09150a0f03030e012f060f0105030c011d0607140f010609020f070f1403070b0a0e0d051213050601060c14070305031c06 64
    0x100410140c4161000400503100660380410140c02e809080c03c1084403e245918503102c9620050170000a103c0898000442c240b0b4020542c0c1d0351b5005610403131000f890b207081c50600701c0c1008442c210942065503018000c800520204e540003000c0d484071402030909600010762080351084800041180c44241c0405189105000101085243c003400031f0400351445a40ca0f00704160301c8038003003091035002072011100e03003a000b180b000c10140d4008024007014541132064407004a0301548a204a0307140e0301402505014030024801c1c840180b80000b001c45c244040e482c00c002c0d0768803800c54040c14840000c0807070810700c06c00c85c4d504480948044100c90b07075030303440f0319081c4e840c507104551515400d440d040344200840004504100340100542d1034618040f1103000002810304081e10f4400001c0aa512a40000f4020060103010f404e0507211007071244000c1c501158508030001d02c61889030040c060030000143c0000a94420050020340442c811210404030001003040f6448120841d04004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 423326438 1250 423325188 423325219
    0x907120c05040812250f050d080708070e030d0f27061d0d0807050307020a170118020a092a0302130504180209070c0512040f0f0b07060b010e 62
    0x510440d400031003031300e07800e401000000d0650300500030504031180d0f1000024a40c42003810001512601c550346440e048925502c50303c1ca400c00b004901e8001c40d16400074052156080264154040e00c645000d10002009074082501c5a080e041032000348640c100008005501540c55101000e60320a10450407092032141110345c209184603440106601494529201d1480c8509090300790000d0800d00082d800c3d584c03030040c154807225066032140018049000103946808110000701a25130f60030020f110b4508480c0c0c216a41440c081d103924043c00200d0005803200c0c0900c2c4202c0701b09240006100084580c1401904110321041d1100007249403c003015942560240042c00e12900000f004642c80b00180400c503811140c040142c0410603030424010f19203090901d5025059181500ea40d0441d55201464400f9a410b10007014002050070b010401c1103e032118004c180c0d84070006c054510b030800c0d49056214602000e854580c450b04800a030b0f90203059500c1c60400701a21000f00e1001c2403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 423327688 1250 423326438 423326447
    0x1a09031c060303180305061308040b0d0506090604020a020a060f15081f050c090f0a0f0902070b0708160c05070302060f13081204060507021813050601060c110907120c 73
    0x40c00201c010442c13141900d4a00c441500001c1c05a9510000a1003103848001c001055200f028008444214080001203101c041003400790a00614105012907541451020400f4100f4000d00b00c034047e81c8103010b1000707940da0006182d041c07550818000a0360204020041003e0715006c4607104061814203400500d80c20b0008421500c1c00215900c0c0e4400d216410111050b20b2055a040d11050000d0001d0300151400d10340b0102c0000300140482c00d10342d583d4003800b841d030a0302d0348140000c80c1d01003482c078240b29040403900c3c1e10a40d14904030141e0710380320091004402d4144070480820051620280412100300124409903030002d00300354461900c0700c11020294415810365001542074400091030800c00a200203541044031034550070701c0d042c0307a81211660230114090380e0141f00c26210603402c00c0708250050141540c9072042c5a24400d605199242c0f0790182e221104000340e102407540810740d004000c00109800300c0d103000d02500ca0b5507040720071060150b04100e10394500300382c690323034a40c21 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 423328938 1250 423327688 423327701
    0x6030325060902150714061e0a1d1b03010209100516060f0911120706110c09090307030f05250311060a0203060f150d0b01090305070e0402010306050d1a09031c 70
    0x141004065040c6c0c5042161345650080c0e40d200722041d1390301e00b400c2c1c109400d00d20117036000b504200002030041310111803150075660000d103485980c02c43d07103c1d001e4080400e17481900f00d140541c001d500d17020307a070400305e06401440701561081001c049440c40f00340c104805003100c125002401401920b810b01e21b11801440043c5088500d102c40c142109424103100350b0b0000d6111580e400703000d6140c9015410754002d0b40d0380612040d02e01030006409030554803408018050546140116181e040c149005442401c0041200302801b01c00e2011007c980450b40003400300803824803640740700207041e18003603a04084001d100d001c10b00943c0104070002c175055010350f1054100302c4245900060b00d03400d00140800030b0304000040c0710100300c480120840d6400c250014070040c58a0140715a50361101c900386070245e006858403403441420700080d9a49401070f00003800c01200c80d01c64800c0c0a55408001100c80c0501255080840c400144459400e00982d1002021941080100880002c2c020000d100e03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 423330188 1250 423328938 423328943
    0xd0f1a0f09060f0a0c05040e010e01080d05030f0109200a110705060c120903160b0304120318150f020f070501050f0405030d0b03070914070206060303250609021507 72
    0x420300c001003900500064180c058000c9441e80b0b502e03516000900c4002c0c1a41c2c03030703e0f242440390800001a4004013404018020140140c0783c0050b035041c4100c072400c0c40404449441002270501c14088034100050f00e450448511210000f03009185d0600382c0c0c0f101c0007521503520501e002080120440390004401000d03c0b00718000d8401c3d498590080000b903005110081416034041220301d41ca0310840c50003005d00344402001c446111005442c01d40c040203103034200603518807001c414001000500c851111030143c980c2028803011100030903c4d034610281d00009080600462103a820b021169440044100c801e00420b5541c1e03060856031150300c4d80705900440740ca61803c0d0003e12042000c613000c038043c40d4420301030741c40d1039440c900040c081c1c4a00080c07603a050048000020300021a84241f0310009110100070680e45014400a410b001000700390a00a802c100003070035002d50031120300c0d216103140e000d04010fa09010b0a00d04003d0514401c001d412404103000104050340c3c000180400c1403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 423331438 1250 423330188 423330211
    0x2040c02030f0d05090c04090f140d0e0103022209090c120b040b0c0d151e08071509080d0201060f09090209010302010509190e16020f0303060d0f1a 65
    0x8080000481e03880c414114810850901803285507010f1000e500030320313088211032040350700501d46000090122003055504a603011540303e4010200000700c0800003c008445015000c8800c4a400c0a01600e820081c06410903600107480500207088400c40300041a00d9920b2403134040d200c03101d5034020040c811050710340d10f0401d1400905000c10720b030740020050f0300c84610402501d940da00c0c00c8103140054104460500248070100c403200c8644100154245119a0030003400d26200d45410001141114141c143c420f01c1e80c20b01030304200140d03100444528480c0d000791260304440446450b54030750445a032038011800700c404000c0d8150801001d58940d43d6400c4003195556a0810440d50543c5d070094100030030038010409903020b140500581031010300740041c00042d5100c1c0ca46150120b80084000e13420b0f107428002c100c404007600c101d8960b1140000c4c148074032043da6690752070100502592040701c1320000c8000b003040030010041e0711640a0641042c0c0684804140341da40c6c1e0071507000c0c2425 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 423332688 1250 423331438 423331451
    0x3110f0a240b030c12070312030b120303160e010201091509030e030607090306050714070c0e0a1a0405060a08030f04083306060906040e04050c030a120c0c180203040204 74
    0x2400b07101c0d21410000040081c0800d100768002d0155580300711000044130b0145400000c0400d2070007000d441d5001c82540d0001e01100c444040141410060808040540c0103104121210308191075603450a03070701d418002c80003c0c00340d004034050b1080040c02005126406081c00780e11041d500070350b0085100f5225036000c0840e50092507035601c0308444041c0080c80d1440c003000800c4503641301a40203400780c0740c01044d06c181c1080030b208139400b0b00e100300c0319801c2030f09081002040f40b40380c0941095440c1005d00c041103502030510441c8489040092040340c0d204003042c01c82d03590b0044000244140b00590f6200c400d1000c030100603802600c901c075014000d09100d004050003110042045541c0c500085980c03003540f07440b51100c000002c010b1600141c080116402542e101c6000d8030040041c01c4001d0203628042c544503003460340135035503e070090307104c4108100080c081169402940da124034018a9078801824903081180e0103601c42a091b0088050042c1e2110302c580043d88514000d50342031011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 423333938 1250 423332688 423332753
    0x5030a060e06030307030c050c0a0b0a02070e0c04030213061208030403020d020309130203131407030516122d0c2c06010e010302131508010e0c040303110f0a 69
    0xa690003100c82c940c3c590000c0168500090103214003410040c052800c5461004020000c0303644e1308240c0d0855030000b00049119001c06904125540103402c10745101256814640281c400c7c0d0701035408000e10400020388640d4100d0341c958007500060a83e1500384502c103400741001c0b40b0701e80c0b0a07101a801401490a22122a40000200c0f0070802c00641055011031013803460900035000a05501e00c061407171148480890240c0060801d030103485406843c4841c41d51920310b207011044500d40e622000801010072002e10f0616a216020760840103851b044101c0504081459000301201d082a101010f9034100740310109410310f05481c1306000c007800005019a100b1040048841d110f41005050740010342c882d445401a03400030b442c181809420b001c0d0714003203100c1070300150300301c00d0101a040f549901d0481d4401081da004155451280209083c02104407110348118040501889031409080c0001d01041000b42d82c420416003d40303981000d249045001c400050500f80790428854440104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 423335188 1250 423333938 423333959
    0x30e031005010e04020f0111100e010b092202190f030326010621050a020a0f091206020a0504080109050a03020d030606020a1506080328030204050904110a0801060605030a06 76
    0x140c0b41c00c0f184000d01d0f40e4941d400c0107065141000e07490704000382c6021700102d40c9810041207002ca104c4c0074000c2035521920440f98211003030544010b1141401c2428441042e000000b01c070801103500100048510300ca00120f0082207a109101040c1010b0f1980041c1100307400c03a802d001c0c0c900c41c1d80c3c1d0485c400000b56807900d8512000300c40c6410b0884140c0100020341c005c0c290500d00d0b81c480840a05401c20480d201800c655045520105083d000115946110344c04201c155209125051605420f07040c03110605148403108002082540c2c0042e030904054002c030159001810003100900c107504192400700d40300c4065403400c90140c030692180011482c001d010b030303106a40d20b03031b4010210390f003403520317a031089c0150341043e2446141e803503401040b800818001803100c081444802e071544200c0c800d0f0b0586070003d003c1848101441400b042c0a02e9030b0f1607440030b8210750004500c41e01100c03c03100040700b5502d1540121210340c03a150b400241260480003551094240f03050030022103a48000c400e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 423336438 1250 423335188 423335191
    0x40308210a090b190e031306030c081e042901050f010804120f021204080c030105012c060d0503030702070f060c12030c03060504240801380315062806050d0e0604030e031005 76
    0x703003501010450800b05031000c80ce41d55100380121500280b00700c1611509601d1034000b001c1e8800d5141c03a400620960401088060700042e081c81c1891407803030540c603400464050356595004000d4a003d006004a01c2008a031010640b1401c0c81c139500c81e50f0f036158070342d218501907200d8083d500309400000c282440e1541c107080310030118140801c1c8005920b403032054080c020b00c89a400b64581c01c80c0004500c00304050f512680c0e8940007800c2e4a420071400f132084859940c080000c101001e2a4000003c00b0499040c2c080890b500f00804c0d03101c1c5480341074000d40901c2d00816003061401c540b003c0280000031184003100e2501c0318000300c8a4443d04010301f0307141c0502c226402e0100607482d850340180b0403040300b81d1000c00d410025040301c4603400001d090402c07245440624000d83d4041c4031541c9801c0c0d800d504811055001c0750060310000428040b040240c3c0700d14400e100000c40d0481811095400108800410034240c3d03140340303014034015003154a41d40b58680a4424031281102c036200b1031140a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 423337688 1250 423336438 423336451
    0x6080f1305100b01050f04030c080f010903020a2306072001090f0b04020109080601030b01060f020a11060f04083a1b08040308210a090b190e031306030c08 68
    0x40c1000e03100e0100d1000a080710030303000d1307042000030001c0b143c2140002d8080d00c007552085140c8038981e803a114046180015060401c24207914044076500081c3d0002150048658003010a2046070b2050010480180c00c4205d40c0060b03008010030083c480d94040801181034148145e0b0f942001c2507520360a0032a41450030080c07020801c0007030000490100801a84d1180c414074142400c01e445012a9080c42000e91045844400f1100180030b2190041401200c4a001c1c2c4010446220300b61900c1000343e41d400ca802e40101400180b043d20481c03854119000f804601080b05c061030725000100c0b210100400c48000f5040d03030a1489841b0400111400b16510300c1581e0b41c0387e44062541c00301120340e0616000f00c48040c0300304400000a030000000d4036000d5880c0c0c3d2201c01c00c0c04140106200100c006148184283c9003000440c000360440076240d80060a18480c4c5c620b2000030030581006003042d01107040e441c8030105401c614080000821001d840c600d60b401d2000e0018030005945040c1e094030746 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 423338938 1250 423337688 423337693
    0x201060614041d0901110a020a02031212070c06110703020f07090905030301090c02030d0c2304050307091104050a08060702101a01030b01030908040924030218070212030106080f1305 80
    0x1030001c0c503c080981d240c0004080c400060205500d08401c5c1059124007041800368020414040652400340031464581202401e090302d84114008140c1e01c0d604000c4c845014001d444498009014695014080a0014800043d0b83c0c54950070080d42c0c80030014407040252007103440205101155024181d011a03004000394110b03400c20b001c110103813607800c480500b140b00600410107175507881c2c05440c014450a407035080b01004003070050100060513025900c00356100b00010003807074400081040c22201701c082c002907103602c840c80402084c40b5590095a02c00301152000c104e000f008500140140d8680c2c0072184101160341c11101680c14041d401085004c480c0d40e101e21550280d000000c20f000c05140c000344800303165455420070b4109400c000c0095076074496a02580403d007605041c0c52102e503403406079003495680094181d440d82c1c004480d20b00c0c461000b14454038000c001d0403040b5440e2a08150300c2c3e6071070303040080c10b25600f21000c15403004e818020519518221800c0300125400901 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 423340188 1250 423338938 423338969
    0xa0503151b07150515010207031e030e0907081608150d021f110d021501031b0b0414091323030c0102070c05030d2d051603020106061404 60
    0x2880100c0c00307094240301406440400c00d5034006038a80d244030000c41c10039900002c250400c04040e45503407255081050555100c403906002082580f4025006601800b0141144803030901d0111aa030840c090ba8641001140c0e082c0310301c3c550072106c454404c0030003030b8103294a5007041b041100d00c00390a4660703603075500075005281c8590070038662128006002415081d0311046001200001e00120f10490b000070382001d980c218440014013402c41700441d90f100034964000030001307600e006101031000400500c00b402010900400e2080d44000800c26050541e417500c4e03035000e460340070381c0b40c0c0c940303251040744800b0018480806014087c802150080f9000140316448812042c60460003205020035120901c207a40040b07109000078a85030340704120008401d454103050600e410308400300c10b0b00f40484112000c640e44d440071480a02034200c403280b00d80322161003001381d4041c4191034004500c1300b80c8480400506030150041005c03a8610b40d5194544e00c2800d0b10705000d80240d000c1c0100c1b5441950 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 423341438 1250 423340188 423340201
    0x91308040b030a0b1002150703090c0909060b130605010306230904020f120f010c230a050904050a0516020106210501060803040f06230d0c02010f05010b07020a050315 73
    0x51940803e00c01000070f1541c402100040048610319240401039000a65210503a1031141015400c007245040c217021904159039611030440041c050f5280b00d030b56811010301400b800d80c2111001c48005003c422031000a0322503440a402140a000e0100c0d0810b00001100344440c2c41c400e1201291800d09907804021004111044001900582c2d011410b065100100d668031031038041c84440950092480244510115080d10410000070050100210b00c8200c5031000300000c078441d2014103e12541d0300760142c0c040e034940c016010516001880e000400c446034207194009400381d072006120f0300c540c03051030804900303036401801014071030040601000c000e1006030008a2006201c1c4c8008103039a6100c1035054510341195020950512420204009143e0001d10302c001c1342e03070b8580718240085141500300081b071199462942049070307503e0010401510039445259607d11540d000d0081c0d5071b4410300c201c0a9080f07017001746c1c4134050003080015107180009441c0075102600d000b01d0180c8d40e410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 423342688 1250 423341438 423341459
    0x30c020c01090303180e07050a03050c070b01030201050f07081303060b041509090f0227010e091e030d0504082101030b0109090f060507050a030e030c0709110409090503070209130804 80
    0x12403845003112a1702601241c0c134002c030640c003817017442603989154848a9040e0024151030019202d0b081c074540402403e0003003030b604000c0d24192a02800d003150b94140e0640301c0c502ea0310071841e000d0445100407840d50740b01c5440030324410407617000e080241b10b43c5c0c2c0e4400410049030700c4510343c0700f040501050704104030743c003d80160042c03501400341410045903a801161405214500412014488003803140c1a40084c80c10782e070240212844a516504d448a189681c42030001c1d8401586054081e80d020805403c0007140c855040c00c250910090415181c000c031940c004004100302540140200c0e03005106aa00c0075040343c1c0c21090501c29a4a40b0f04203800a08200000351800094100c246d03000c0b400a000721030003902ca030303581e1503601c0c0c1d0034440040841d422103201076031a8100300300070400180d00080030002e4400c0003100003030500765102158080d200360340c02002c0e080d0521f42c100c1c0a008000c0043d017622802520320340c2241d51040800540410358440003890f0369028041445284042c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 423343938 1250 423342688 423342707
    0x71502060f16020f06010801090c0e0c0a05131706010f09020f04051023031b0f07060b03250e070201020c1f0b060408010509010b0306060a050906030c0a03080a030c020c01090303 78
    0x3030055402130841403509a0500100740c000442681d10307103414008010215403800300500701c0004280c241e0500b0080c1050500c41d116074401080000f040c0211801040c0c2503007002441c0c50a80c5040b08800c1d20500da0300c2e07138400d20605500c0d12001b180015401841d00880e0600e079400c412103440c1c1402c00080150f00d18036948500c00f0080310181c50a050303a45024014148264800c0d080e840e450304520b03900a0194800903c183d00704288000007800c643d2100303544005600c030364089081080720700070034a080c800c4422400c08000d514000e111408a6440f114155034000308150307620f540e402c1d402c1e400d038841c0b40c0000a895209100d54040050304488040038064a1140861920008000940d140e081500f0040d0b240e5520070500c58028000d20404042c0401500600049c2c507189002440b038170510b01c2201e015400740000601e05e60360038048450801070040c40803d102e030f00c078100140180c00010410b030200745002e40407050310b800090b4401c0680c0b0160740d02c0e16102e055075021922a442c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 423345188 1250 423343938 423343981
    0x2120c030714280c090207050f0106170c0901031703040305090918150c1c110307030903020615031b010302130315060608010e0601200609071502060f 66
    0x600c1103000049503089803914044050008000c100fa00103400918880c04019040001c18015403640004422005110444101c00310040e1101c40380e0600341d0801c41c8000007481927501c1c260380131810401d94408102d0f620141d804680d10f0140c00702c140922041c080c00b01400b079150074801ca021080881d0b008540c031600c245005424620b411010840584082ea4002440418489000c40e4410200548040c04450b13080080c01c5082c030010b1000c80d48181c1c07821100b00f428044103a4604112134002c0090f000010210035960b10300918002d00500301000201c0040c000c040c040307100000110b50420320349100502610500d071503e201c40754881c43e500381450501d9001e01400555040e01103543d0300850082c503021000101c5a414101103c1540d00010148441074005200203a04c018040381d01407020300303014409481030105496099200c8008200b90b11580c000c01c43ca5000c007090071021900d4804056110b00c0c0c9181d01aa00ea1703000300c07039080d046c0258400088182c842c00350555988030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 423346438 1250 423345188 423345193
    0x30312090a0c1212031e0e030915090306060307060f050a14071406012705060a12050a170f090f010e03071d090d052d0705010f0509010b0102120c 64
    0x1006580d260a0b2500c550b0005001c541c5148043c02841020310b40c0d0b243c00c4446103070400c20360041c00c19480035810a0f8500000b400d0f6079122801d0120802c00c110703011040020111609121941803501240c1d000760301c2c181c024000c41001c5511424005100300c01d440711501d03450302030103001d441140c190300180b03500c204101c41240c1c12021000403400602d12a40210000031115441641e094544801039122030f00107408845220400c00740403041e1030000444090100d000d4842030001a407114080d0008120004807401041c1007110010304600c0c45445008101300005003902c2d00201c0d80601c40c2d5032411407000b0804101745140401c0d5040016005061682012400f00b0202e4503103581d41d00309515040e80440c2072154030200c0d00c612070740442e001c2c000b001084805807004001c1d000d0507551131080c160b020310409685c0400640010036042d80b862198a66855041a5029204054100f1181c510385800b0403801d11060080c1c100154040e002018516146640300c055030380000042d040e60f0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 423347688 1250 423346438 423346453
    0x30c0d0207020a030803040b01080d0c0b0c0f130e090604080d020921010921020a120e0301020d0501031101090f050d0809040507092d0909060902090405070f120203031209 75
    0x41c1e983d03442d07000145005204043e242e150618181d0903040044e00840c415900c0b03030710b0543c50140e1100403004429031041c6405810340f0b078192101040d021303103a4001940710010400702480002001520300700c030309010000141c0c1e100c14950686a06041d5006400c5a100704281041e43c1c540c3d4004202200e409820441c25006010a40c071003110b4100c52202d50303035115100042400008140058034000d603c03c000ae11030410003002c0e503540e144103c0240547c500c190000c81351401a000051001030203002995039203883c28041000340000d0000303d81d1100c1d01c0000c180c0d5940f15204070000d5035100004c554816003400204154159070240844101004000c240c885445901030940200390948030740f100b40c2d050034040003551210120121207064a43d0041d058000101d24100c01c41b400c0c04400200020300c1c1c200400071703014a12000e90405280b0007807000300711002480804a685a000c07080c4c1840e100c410012503c52070085c0694958010b04c078605280501510203504080f0300003c0f9000c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 423348938 1250 423347688 423347693
    0x406050301061d04111b0714010f14122202280302040906140c1204020405060d0209090d0306060c05070b031e01080a0204050601030b031902040e07090603150b010203030c0d0207 78
    0x2e03200ca17070134107880d051404140703901e01c04d0b510f40c800c101003038401e00a800c000c0d051110360b00703001244800460401c6009050134140c540152014040c1d4061a21503540c0c80c130240228a6401609076449030782801080d6196290003041600c1020740ca034000c00350340c202010406151501d0070f2104581044812403034000006942d00d1041c240501e104010100c0c482e032010340f401d10300d240d0003804505030000402903c440c0491100b0542e0340646d0440e000140d41d2140c4001c2940c18021000094010802c4410300c0147c0e6000500c1c0301082c0c141307940a01046440300011160407032040002082540500d00c01d001450241015641c0596140d444001460081c5029030103403d080e03014130056007005c07004000790b041c18080c0e50340c040780030b08051099038001008a035a651030b07003151135019940845844115aa540c2000c45000200f1046031400743d1511180d0000302228801144c0380003041c841d03403580c0701d010300074010301d0b4805170041c40c190340c0d4a64486d1050b501c400c50386051203500b040364900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 423350188 1250 423348938 423348941
    0xa0c1413091e1b0b0a081605070807150b01050c0a080c0c0612010f33170a141311060a030917030708090a051213090608210406050301061d04 62
    0x200ba80648101200e40a407580001421a80c80e00030406500e020409224400c0e0084109038114a544861004c95000c14a048541d40500c960080c80c08400240d0740b0f080c4291200140080e5500000401c40c080e605001510180b00700040e850498115154190106040303501825a1a02d003005a498408400c00091820b900040c44041e2032400c00340103001041016810034050036003110550414000180e015a0b92403a44550f20070400160840c841613911a610000a04c0c8003622000d0460829845000141040d0020f0320f41c2150b60710b00148840620003880421243c001040c548040444400d10401c4d030300010020f414103450706801d1000400c03084d18060014a051070103900c07810030341e10041060304007405d0310401d075204c12a808007261002c40c4900c0000800c0c1d82e0244e45203500710040a100615900c280c100034030f48000001c52a078003040c3e065040d5941842d9a80414410003d031540b0b018034060b907000035030140300504c0054001c5041031140303d09120003413604640400040c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 423351438 1250 423350188 423350243
    0x7030908030c0105100e060102071a13180b040209100c0507030b0108030a0912050c04020d11032d0708010324020c0c0112061802090d08030103050a0c141309 69
    0x440340d0b136645007001050504d13114500c1c043c2210783e0b54200b0034146000003d65a01c60360087c881000218042d100d810368805007100c007c0980d010800086a40c2c41000002c00c08070a0030b80b4005505006400c00e0920703240c42200c0b100f0000508030703056071500744411909000301c19800c59140c0f103003602c084040341081345c50a000f8441c00009581d121701240c0c0c010b0601c14a40d201c2110100300b00682d0001480200d402c00c910b80742618016100e249546032034001d0404420401d007405000407d04c2201100405002c00b003803000b00c0544036a4010848a12041030120351440c005003030b800043c400148600c0c1d20781340e814071014055003692513018076402242d005824a40559010516140300395801c0254403045181d981410042c030391402e03110552a896010140b81a20390000e2500e80940d40c0142070400260010b401d1358580da120300c5c14903a10b0903c0d2005403030320580d0341800101e211114602c942c062b10090303e14580c20b003102801202a0a4204040740d868400a14801e074000c881345408 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 423352688 1250 423351438 423351457
    0x23030403020d061b0c030206040303050c090d150c1437030902010f031104050d050703120c0b06091003020d020117070e0405010e0601080601110a0602030103080d0b03010606140703090803 82
    0x512440c902c0741c130041c1c0802a664501c1031210328680b01022031b03004a111540305416040c04112643c901c0c0d01800d05116806405500c070101004807024044821628182c000c00c80700c0401c400d1440d4481519000100903241c1d049500c03c02010000c200484c0862000005910070b2081d89403422949a0540d0400350603d80040e40c0e8220381c2d015581e1200c0c071080f014001c0d00381000071000716800d001031440b4034002c56018140380c6d28804104070003040b0150003141c0250780d10202c05000a002000003548030810365202105c54040755403490500300c45800f42c01b1403100807001c903140d035081c401c2d43d03420b21758180d05001d8a1000c40007070100740f000203403144042e50f8540c0a21002c000402c0300b224010f81200c0b101c8000c281c2008150b0344c01c07090306604000c00b42030612039014002c08007450311100d154014461307030020000008101480c4054011b640000c0000e2090808940516080302d02c40d1040d200081c0d044101c42c0c601e191090007c20b007031400303860440781c001e49130b100c05d515650001088 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 423353938 1250 423352688 423352691
    0x30c050309151207140a0c02010c0f0b010f0812030403030c11010f0f0e0606030703080f1b01060f0e040f02040f0f021b06060a030b0105011805120d0801080a23030403020d06 76
    0x14420b1040d2602c0800e070f001d13441381000358210800c070407042da480c010401d60409000c04e240144082da80181f01403901756030710401c901d003244114907154444190038443d07904030045065010401001c0440d241c010800b8040c003503401c42c0d46a4400f1405014084000c10920002200540b6511000c1c080c1e900348030f031660400303e010b1003406281400c0351000b06287d02c01e40c0181060108076600803941a048079000013440d074581d25a14580d403124890103a0342a0000350003104c0c17402c01135043d0009022103900900c9007000c140c0d54040070114403800c540007005200c40020010051626500c403811040300800005621400e1450b1030003280d010440c852500b2042d402c40041c0c0400402030340380d100d0b006440710311445e841c550b01ca03060384106001355030601600d0208004071580b409440801000c005260024030309500120507218031000000c0d60000e0010000494118400600c031003139141e10109540d03d004a1010000c42c07400c0110601c0d015000820000000d42d56012a20381d846004110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 423355188 1250 423353938 423353947
    0x50301091406070c0f110f030a030c1a0c03072f03030615040e0406050604181505010b04121401090c0605040806010801060308030f090a080c0304090e0c0d030c05030915 74
    0x300d5510b850750040104080010580386000018003841c961042280d011008003a900001c000040408281400d400e81500c18010035100b495031156000d51003e00500f501520030003070000345061180c044400c1c1903400c404101007408180305001c40d40380b8900d480070014000c41e51800b4401540d54180002186500120034030840d440c0c074580c9010302030030303000e4003900d00b5141c90880705031150024009800310395294001240ea80341e030707004004a0300e08101e002c0c17400201450640c43d00c2c590b50001d428410300c2d00d000806c0000c002c004070340907280d044018651110190b602e40b4403c588038440d030b089035506c0d1040140050300b22181000606120b40b96a91a0380c00d160a0070b180c00c005078003034116a0b0404070104042074004080342e40007040310b01c18400594034110310340d00c0c00300d2040d0010041040000c03900704801001c0040c009454240c801485540782c000c5000d5a515180303014103a200b0001c0502e800024001d055000a1a10810a5078140003158000820925400300106903603e80000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 423356438 1250 423355188 423355223
    0x30f03090312070c0509150a06090923010506220b0304150204140f0d0b07030c0e0906100305041a150f06161205091926032205030109 59
    0x650b03848020011a2a003002490b448007035103981d003446618010706042c0081901c88003c840800d0100c3d001a00c0104416134403000200100c8851059000940c60400d4020b2080031614082080d80e0003400c180c00d050b400c02042148582c00b0740d05040303884407445000010f0320a04c4c1003043c01400c20031a4141c4030f10f0a42840740c000101c0d804114200341c41000700380414865000654900182030f01c100f00c0000100340441c9040004080141600d5107000802085681c160810795460300c040d0348035442049900103000d10b081c01500c1c102d5000003a1000c940980e4440e501060784140140350360341e4084000b10100031101001d03076040081c010450a0241703641841038024610302030666210f40b0300b6484074502103e08084850013003540c000311881a90b003601c070f81c05680d02d0a40082944045141c83c448580035518103100e401184540125100812518903115001c910072840146141403220000300506501da102e000c15030040040d80400c071520b0034424649807520030302c00d0405d2600c010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 423357688 1250 423356438 423356443
    0xa0c05030f030f0a1404080a11040614060d02210906011d09030711060c12030415110f090117010e0a0b030606011202090d1b0e010b07110f030c030f030903 68
    0x84407407015442041014680207408040b641d9540a07450401802154091002c29604c01c45d4040d00b1140b2403040b0791028480e200c012000c4120040780c04006080c0d68549540a1084d0707000019884142801aa8420002c0350014a4500c006900003420820080283c1c06078100c141c4141d03105511490040c4003800098000c1010100035070283c1080740340116885950f031180301c4c8001c0026030485440c0100391610401e40381410382c913806440b42c0008080c071071101608101c0e41911500c160703c9070041d142d0724610800c060754215180d05840c094034078080c29499440104002d041045040e6030b0200100e80001e524041d0000c405061a1401d10314803000a4607180d000381e41c40390b0444014410310780e0700300e1140491000307013501c00b507221406800015040a50000041c012803541300300e064a2528514607182035a030800d51103419640ca07402c0d15042801064002441c0e804002e00d044120302c0c000d080019240340040c100d0f4581ca6040012a05042031702c800501c15070701c042070200d09403030203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 423358938 1250 423357688 423357703
    0x203040c060f2f010e0106060201021c11070209041505040f050d0e0f120114041a070503060603060603150d0c050103060e060306010911040312120c2d050c0a0c0503 72
    0x40b40b901000c1d002030103200000c0a01200f01e03155003c074040000c0401e00380f00b908261018500341e4020084a90758000280c042d5101541607915070307000001d078802c640500d1040b405095041603529080c09240d80c04d00250120241054881552403811404c0403125401140d202d0741c419003406050101504e441d80c81c1c00e441d04035110270b02c051041c2084043e150b050070304001340d01c101d03280440d69400702d400b2401094041d11601036628903900b00800c0c46140d00d10f001b100c0d00d20b4500d43d02c40340c0e506c680449941c001541d5036a80110200007040d420718002020b113801c1480c402c12441c10464040008500f038600080807104120601410030980d80c051084800900c1b91010b08800e0b40352900010740c1341d010501600300b0f500e9541440c2c629211001060b2000382d54002c0a88e081a114210007074100300e02454004a07050608600d030049a00c2161281d8000c2e10032401464046851001d05a550304045542401c001c001c0c17188000281c0d04020404895004003469280305041109244c1071164 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 423360188 1250 423358938 423358967
    0x612010b07030e0603040b0c0d02091c05070b03011401141210180603051f110a0201020c0c06040605120703110f0318012a0509040f0e0d03060609060518040203040c06 73
    0x424800c01c001f0030054600d0720790000c0b004141039920689440701000a0154504c41504118041c1441000076108640d40e44454054021107190f140e4039013148640e032009002d408040c510080c1d0004080d405002000c191640c1a4021401c0c444020b074400d0b07042108444200030b42e000c0c40340800c84200002120f0759000980d1005000c0320b8110313207407035590304852840610b841d0865920010446015400a03000e0003071401400e0744d601d042c01c0024081d4100d142c20800b5406008040411482c10804a4003241d42c4d036264182410900c4440808000c8000d2869040c10f44a03409500c2505400c0001c000c02c03817001c4180354490a1220018071a0b41c6146203000c407580c03500c007030740d52280306201e50301d0070842d044041d1001c1c00401d0081214240940050241c0090502d21008200007858000c5030264000104075507000740204800c40c03d03038207140300b00404104e0007a41448500d1044c8010011910655000030300c03443c208001c5822a4801c0358141c1340305030a44811311042da44036040354203507003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 423361438 1250 423360188 423360199
    0x21110a0f020c0609130f05160305090a0f080c01060b040b07060f110f0c150703050702010506090c0d0c030605100e100302031e181b010905011e0e0612010b07030e 71
    0x7189002003a1507118610701944503640000740020b105210340c00c1b603038a158641d5801d11990400e00c4035880260040e92007403010070b05000c0059400f080000d5514086904410703940d40c0064191140f0b101940300b9808140255201c250101d10309e40b00700c1c002c10003842c800c00c0c41c03035907003a2038103140d81103032040c00b003079541c2074103120fa103c04c00d5034000e01342d40440d0140c542141d52a45c155004074500400d16546034080f004a4041085c030b260075511091089606400a2000340c1d01c1c5001c0020b0408100d4032181d05203400d000e0076202d00400e60090f8402100d07800e001071503648500001d40c0d140c450344007001c0022080ca03012041401e200d080030032036810600f411341c00e41c1090340e0082880089044240750108164000a1024440b0b80c0303414078429426054542405007040026140821225000c3c0801c1d00c080000410354400c0307000704003401d0106010306107002d1681c0211940c0b65854070701680514140424049001801c0145000b0848034102641c3d907001460060001903000c00300a1158 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 423362688 1250 423361438 423361453
    0x80d0606030b030a0320010911090112170903010e030304050d0306080303040f0b13020415172b05070203030406120c0e0108070c030909020f120a061521110a0f02 71
    0x2d8600240d02c450304c6500d0306000b0013550072204100068440c00c0e000328811742c00c1c025000c007401302d8040b20b0300034004152107d45090f81c9452a240d0b6242c00400e0080441c607241ca2021009400d8002038038640c0001000800c1951101d5091031642e00140c8069850b42c0010600b01d40079909407003004001e1454402550840c07820303458140500c5a0098003401d1150341c000009c9003942d5442034102242c0d801401044450f00c1c03504100e04180c000e01a2041b4400c03840d84003a6480000128100074a0f03808007140c881c070000644004656180148000a200060200c2c00060303a044c000b03040501015a5040c00c1c5018441050b820b43d02c4c080960350a200c010714076407600e030764002e50715540f064080c203207008004454607084401c004151b05c408201480851082c640c0c00c40180209001030340351034464880e48941603000110341b070780c0c070845480044c91941e0308446400381209102c1d02d01c0402600000403100f080c4c038010b031103042c81d4900080c000050303a4114140c001c100c9002a0310b8920042048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 423363938 1250 423362688 423362711
    0x60305240a06030203041106210f15040b0a120302060403090e010e160c02030d050d0b040506030a02151306030501061e080a021303060c02060103031d010206041e02030604080d060603 80
    0x181c9100340601d908040d00000000d060242009621074622406054a036407001f60000c51001e120000e5183c2c00030004810105900003989994ac6008544107070400290364005410040105662041aa04054500030010744000c0c1c507078a10003541d010340c016103204e00c0c1c0740c0340c010240300d0035030003285010342481c005000d442d0040034031075840886031044078042d00307041d401910f42d10600140250b252091110030302d1101e034444050540000400000e07c0411a008100b00954031704655483d00740c1c3c010242d010162401d003001060010114840390302d04901c8222501040f00b81d0b401c0180440d0329900100301c40d6502c50341c0c103c00000a0130003001000c0c21352400400032030307002e42001d0120343c000c61952002c1c0c14581c2800c0c021039110804210340f000f41d80010352141001d1000b07601244c18400702c8c0c01545110038450007401030590103800d09a8540d40d070804211414440d802ea1081e91401080058800700b01e2540510b01075600503803503039140c1c864003064030040d80200040604007030640e044d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 423365188 1250 423363938 423363949
    0xe2208070f03032004091802180705250210050306091b040509090c031213061b0f030c02030c12060114180f06040c030608030706200406030524 63
    0x22450352041c000c140d59059800c080f0060b15a000220002c011004058010610200700510407620201c00511102c0000e02c0c2c256908080180301070340201e803124807401c600102d85401584292a41095420981e500c40c0d11014a100e0010404e00d6400540200b010b528042d9503070a07d0640d1b40c605285035142000100e804000d0203016042e40c2090a4030b0700700b000868a090b00d001c0e28014144c0f90385482d00b01d81d02030751559030140c458028001c2072091642600b07a00105e580d0b000105c02800071141c6019001c03a860101100114801d04007210900002030a0107041c0d007110b030281c1e456424507891401010b0600c0d690703001d010320030801074503840c3e41240081001811140b2044044080c5114800820741c1032150600807100d84e400f4170b04005800d55110300c0c241c00781030280c80806c082141c01d24141d040360b15a000e900701030790082c0400e40c00510035810480030350214408030401000943e090341c002d40c000750460350201340c84004002900a0b4280c0340340c406160b0302a0b0700d05455100d00070a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 423366438 1250 423365188 423365197
    0x1090e01060e041e0e030405090105060702220609111926040f0b010608070e0402040608150109080303072a02100f05090d08040602101a010c06060806010e2208 70
    0x1800b45480e00340c80040e109030604d502c3e041400102c42484510031541c0102d03101d50240c080c0501c0b075440b55001044604000c404d80d0082640680f40e00d00302c60b06c5d90800f64924038100034410030541c079000c0100d90701c4010f004440d103900101e01000c0c2c89902e810040a006c5400100303c804001040e4072051488030b40b8184c240c40c3c8104500c4042042d243d03410701b00603009810720050134090048000040d81c2e64090b4901d880b8500380d81d10070101d03e01c2c03542000144e118034801e01d8002600c4170013280c0c1e580a64060500d071400705042c4101029645c00c031250842d0011600c10001c55141c12942d00082c80810208400c0d40f034a184031007080070658009000382a1603a1030321f0401002d00310035894240075408840700024010880e0a41410914003241c5681c03150007074800500400601180c0700c2007900a5004600301c108824040740e5100d001114401440102612400d0b1542c0c00081d019405200f0b00340a05a054450841e0b4500584138203003805154080f55907a40901c05a0b00114503000b0640c1c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 423367688 1250 423366438 423366467
    0x90a15091109010803070314030906010e06060c07062115060f11070906050f09040b010b0c1501150e0109030506070c0204090206030a09060b100c0b1e07050901090e0106 74
    0xe14000c490a08034014a600410a604031402c1e4002284500000029102462003951031082d420b00142c040041c5010569031010164000001800030303007801e85080c0e6100c0000303816141044000302900d840e00103140e0003003010611240402c4001c0c07125002c034850b50804d040b020302c00c0403c40384224501400f24840c40b400c010241ca05446c07450721521002103171b80c2440040321003d50712143c3c0c2d10010482403068510908000513440031a041140e8042e108903080f810b14206680381c00421002640000c0d040c12950040380c2e0f250101c800e01c064014040c1003804500140042c800c03001500f0134004089490600c0039031b090420000740000b03401903101d440f500e041030f44c4589a00c049000380ca40000000d500003c00305c00c202c0144140e0b44080d00c410701a200a000641c1e003107040c8100000d1412039403000400c44004140401e4504182ca5004104100000c800340c81c02c060080814205641080000d00700158014007503901c080c6802c0070700401c40200845500d00040a4040a80c000f02d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 423368938 1250 423367688 423367691
    0xf01050f0c010b120309190e1b0f0c1b0d150b21010c0e040506030c01080c0903060907090c08060607061505060412170c06070c060e1c0206090a15 64
    0x841c1e03100d0300c080d08401c2c0300d89406481c001001c005580c00c142c6035000484082e020725074004c4190380840001400b80200c0345042c410800d261200f00c4010410044440c81100441d420000e9204c1101c90100520b404c200f440054104000001030a00b4046481800381c1d1060120360209408110b90310000d061200d441c8400040c080301078004107051100088000c40083c0c0e0364034020700344900642062613603010558400d403480040504100403110282c481e42e0700b584c02500204c07020350084030180d4000d500302060a082c4180000002d1820900b1110f21100d500802d004020016890107011035074039050400281d1450440d000c03940a000d04100a8900c0d5115628100c0c0109004d41080c003034000a000c00756144c2e198980064200c9202c2000c8810140c0407825141d5054035200f501c2c03039085e11501074003454881f9001112007045660080d1400c550303940000001c000d04002c0350075032039941d0180201c2c17180721480180c10302d000184601001d800c10b03e0380d080004c0316803940d402e040050000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 423370188 1250 423368938 423368947
    0x11d16050421050d080916080c040b0f0a060302070b070c261b070f0e04110d0507080718050603010b09010902130902040803040504110403081c0f090b060f0f01050f 72
    0x20b10703012204682c041c0a9000344030320b200d030465010007100c1c4104070140072102c40c9003007160303080b10b000030324403411160345c100c00c40384900c1e40341c079812031341c06208004c0580c00000890800200305410701c0e0302071740c00b003a030000e003840400c150071050380e6002e4000e041c106050000c3d6140c0300c62641400b004000fa07401d181c10b40c0d200e104040400c1ea90041148c2c107400d44030010001e210f0342d03a1020f034040c28099500889002403002c1d81017030000d2249900110300040d14400304144280940b180c1411505070041800104900c501000908002d04800482c610a8201c4480880840f1030280030a8080e0341450a070b110603803240380000d0f04482c045d800060740c400e20301c1c415901110543e0019001c0c0d600008000074003420000103003040d50001c4400f000800c42440d80c00106100b94800140300c04018084460003411491510130081050a004280060f070340c200c0c1401c0799074071401102c845510320240075040c1405031046d0b541600503107900050001020019081d40641114107a00744400039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 423371438 1250 423370188 423370229
    0x1a04061112160c0b070e0a0821030604180f06141e070221030f011d0703090807080703050c010b032a030c1206010303031b05090108091203011d160504 66
    0x7942c00f1003907400c00442122801c000100412a01040b40c01e02e204048510b030100342c0c000d001c02c002208042444100c10440c00545a0b076496400c01006641d00030380d64808081012074500204204a21038030302d10321141901e24100c4100d0b00505410f003c100070400c10899907044c3e00b411070381c6480b640c0581c0042503444010480c549048132070301a0503d4490480c90130550590006180106000030f402401c80e80c03a5a5030050940c5802c01130340300c40480401248100d070080e03200302032403402a003040345001c40a4403691810752204000310f000403000107040c2c011040a00c21011302210880292122410f0101d026413107802c10036141c6260808030301400c02c2546d0801880040f04005800d82a100c0030708071a0a403226001d1100b940401d0034420b0400440911f04444441d4030802e8441a0821b841040111004d040082507080c80388111043d854150040702c1c051402024580b00c800d00c803a007c072180300c1c01c01794060022801d040c550507425202c1c40e044000d450940e8a203003910030314100001b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 423372688 1250 423371438 423371447
    0x106080a030e24040807051507030206060616062c0106030503030106110f0d260112060504081b0d09050d1a040206040b0307020c04050115080403050c07031a0406111216 74
    0x700803000c1040f0b000074000446000c003041c65400c4450131520340b1840444480d18114078881d43c040100141c211400050152400c80c1c042d000e000d0046944c28510035440c1d4920045802c2007003680b00160070304860307200040d1400c4d0810382a204c243c000340107203480c0d5560140c0da408180101010b1000a00300c4903003458041010040382c620b00300458802d007000b080d0144c8912080081b685c245010304200565114110412904840e500f0031110a01003607516508001c0c00094070450305508100980384404113500e6400c3e04107414440500b54503e40c0d031902800d020410362000c2d000d20001000c035008070713401d006506624500d2580e50003403541c561000030282d105036040300c009440044240300d85240d00040c100301c01035007a6401c022513602ca0814446000311402c2c9400082c25030000100084c0c03054014043c4a000d110480310b140e6141e03a610355458541400310015003120030100001c0c00741a001d40884a0f40201d055481d00381140219010404014a50400315004200480f54944034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 423373938 1250 423372688 423372739
    0xa09032001110f04030b01290901090e09070e0a06051f02030903120c06240409030e0303070b1006090302310501030605040303060501020f15100e0403110106080a030e 73
    0x812485666452604541042c04d8100303000a603030b468928000030640c1240c00018000b10790b41200f80d400301122900c8264090f511076101e0904001c80881c0002d1945e03c40d0a20600840d050000781859909100400f41000001040c205d1010704202c001c02440e2681044a00c10103400e002e809000c09141509914610454010507018480e501c0300c8485600c2090207411008514010780c0c50b591215090051040000600d030b0300400325010720380c03a403403425901c00ca205134483d08125440c80e82c00c0c0c00184c00c50304006400d80306819410104940d0003d4280c044015000c41c1c181210384505540115071000e501030a0804010340817190002c500541004007000d407411048140055a164a0503c02600e41614200d010904001000c07881e5030010900c0310281d88000000d00d031113060301c0500b560310381d00500301001c5143c1402c0c0103c0c00e1040c0c0242c1c50310660180d00d1780c00030380002509140c02c4450310352103444540c000020070340000e0b600060b5841f591404403511560b181d24090f01c120070244 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 423375188 1250 423373938 423373961
    0x607090b0c12031611281b15021603170307030e0303040f051515040f09080a03240605042d030c05010e01090b070b070c05011a090a09032001 62
    0xc001c0044001c07115010722144c0043ea943d002140d81070b10a11940d0310175035240c081558900403901141c850305040010042e501402e80d140d040f00d420b1240c556151081d41002c4c1012000d140c0c41600150104004440405004140d4200c00c1c959114214402241426142c0c1090008082500d0310302c02d81280501450500541c0d5903410541303414460f800b03480908481d44d008640380100c5170050a50341a2050100010303200c0e8022541c0c0401c40200070140099980d295980ca400012502400c044c15800da255200001e0515044841c1d00d4101102c141e40321411202101c1446030035400b038103482c1100c00d4251a911085203d4029000034040303080341c0b100881c0c10301400814406000440d008685082e00d88903000b4000388011910040c49008003020035404000000010b4229075900341d101c2a10724001c0c42c00c44050b5241c50954400715807a118401076046400c4046c501076401981040004008000c03d1900350ba0207490380c85041ea85210000d212a07800b1070061013900101203441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 423376438 1250 423375188 423375223
    0x22030b060409080706061e090b031e030d05040f060506060f09010507030e0310060608090a02030304170102040b0f0d05070318030c030e0d05071401021216020607020d061d0607090b0c 80
    0x11f49071480d000d812040c40c01203d003039a2901c0000034044041c5d21035080702c0d541c050041c281c192400085030000c41d055491210300d52204000c43c44030303001c1611034640980c0c4a40300040c9244218240101512405044580300c3c000c108150707612100300d50b0441d04d4021081c03c1580d11036466003000e6510007490482c00380c15015140304071203600090380c0860203590164a030360000740c544401541d60303031246000017501a0b00812007885582091b0341c0261030910b1100000d450244ca480c1c2d50340340381e0080c4043c01d084050214000241c0201030281c60b070311070340380c0c03408000d081482c1498001c002070620703000d001e02c014850568281031240480344444007000e04000c0d0020041e1510654402c2c50344207521016114811509440d0300c0410201d03407000f02500150700709059101f842648401c0640d007241d00c01000c00c41400181ca4403a6074908850007103400045010406500c01c021480c0f4180018864006070208050740c1d800201a00036a41e05044181c2c903a9010f03c0080d14004040341c0d4035500c4e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 423377688 1250 423376438 423376451
    0xa030e1804050123060102030406030e01060b0a1d010509060913060902181e0a06080924150d020307090207020409060905010507020d030204060503070806010201140c22030b060409080706 82
    0x1054104c0f07401c20f0a41040050302003062000480c0126080c0e80c41d03030043c0c00821080000c02c0c0320f900301d100041c1e450400051a1036403648404c25030741c802c5d50680b012450b00f101c0443e01030055010a156a00c0a007849494030307412000040052150b0310000d4481e04640f400643c540b441d5520100151603051000c660701c201c4480135804107000d80005910402c005c52031105141c10220326108a02c03000741512a010b402c00301c051380d411000418158903032040010880c0504da81003031022000b0b500e11043c0c655418412050080c61348054540383c020f81182c42c244005803800113a2004969906400503103441072032000401918040401405a50030141d40c5814080103501c207130701940c2290202e40c0504005582036045e40200e00c40c02d00400c078140009032200c0d0180c0109540004144000161001100e003103044001c0255007041a0b0100400c0c2110140e103030703000b0b40c600c691004420300e5056155955034180711000901c0315010f2074a4003085410403441303200303803188140e0105c01800031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 423378938 1250 423377688 423377693
    0x32004080706050408060a0c1115070f020606010914040f09060e15040507050405250207080115120210110a03050307080f070818120a050c010b0405090a030e1804 71
    0x150480e018901807800380c0d1000040c1140144102d400311038840c00030b8401070b5a44000703100209243e0f102481072003d0540704100100062052002d5410091401030b814140040f0040c1701038020307441682554031031401d0203040d07a00400a0822a00ca50b001030a28106100c0031402501800d00800c02550400140008000007500000766251415007281c169041c0890004505502034401a10f907421100d0140142e08003900007070703030012180c076034a0392150032000daa074503411441920000580000c081800340103002c0c000c60170361036a00036240303840303500301640c820001142c0c1c80d00901c604c0c8201d891003d034901580301340078219604000d440e408552402d010302980d20403510103001039080c200082120004082d401c0c006e40c645c6d07035060001c3d91140416140075010000c2664280b088181e4080802200002480410810358902d0307190070130700c01800c1c207491401c1c1d080c034416410003040152032000045c000821580514040b0a44407448011400302910700390441700381026601000305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 423380188 1250 423378938 423379001
    0x51605100e1b0102010203010f290703020c01020c0306010506040b0c012406020d1409010807030f0e071a031b0f07020301060b030103110306040309141305070c021e0d0f0303 76
    0x585044078000702c04000764140c0120700b00e02c401d00400200e02c00240040c0310422403d4000500c40d0394040044141c0c0044207082100c40e086080214010382c412020b071440e135641800403401880054004042da541040700140700c03405107000d07000a186e4080f0381542c01000c2500038046246421040038089442c040c111100d000a80c0508801342c4528841e40c8400351060703e03010880d00300b603015503040000301401140c0b0508007400800401d82caa60062041c040244209000703448183d0042416a1410707007141c2c181d405441071881c00810900070060150106183e03101582100c034084c40d03440003182c900100e24010090042e41541c0381800200724103502a008505807405807203051503044214082650310401110001d0005115450030401c9246035152510b8161005046035450041041c458040b214116400e6000034040f5102a05605000d44850180c0703202030f0705104174060000105003003040c80c0600030004981c104200d1b05040c4294040150101d034400c4504030030145900808 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 423381294 1106 423380188 423380203
    0x603020901230c0d1106070c05070f0b030a050c070c0519080f06040b0f040b0c0d09080d1a0123090409020a0b13120201051605100e 58
    0x2481c00d90b0380300300760901c03580703548594454100b5800c103031820343c03070110950030f10945a00059003444081042948180710342001e400c0450285012031403e0402c1c0d2120041682c240da01240001c04a03006601841e074000040c04140c40d00701c00041203110300c03100108640701140b8200324a04007080e400c01000c0c440c08511b081190748050f028101034085a103614640c10010404c010844400c01c00340d0007847c004503c902900d0951b0380c10b900c00001414100c061f03580407030b407480b03650010303001246890703484480552030300311441007040501403240c5401010507000ca0020b0165200e42410002510310120404196188495052403076105012841c4c110761611003036005a203070341218031300030704450107607503510601ca0201c84400b1045030045040301c01150180b101503079000059803040b64003440d8040510000d46032440c90311a2001240541c18104690289901008911f04 = true := by decide +kernel

theorem cover : BRFrame.Cov 423201438 423381294 := by
  have h0 := BRFrame.cov_init 423201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 423201438 ≤ n) (h2 : n < 423381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
