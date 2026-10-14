-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0842
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:06:51.544989+00:00
-- url     : https://prove2.me/submissions/85556e85-f4ef-4f15-ac51-74154b1d5d7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 151258992 ≤ n < 151438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 151260242 1250 151258992 151259023
    0x20a1707061b03022104050307080304060f03090203060703050a15030f0b0a0c091710062303030a0906030e01020c010e0610120f03031a1509010810050d0b280b0102 72
    0x280e0a01e83d90094480644034502460f20711100300c240aa1186031040390010080101180c2c04030350b41d0418251250041c0c4940000b084035080503035910b5010707002e0050f5481e03005000c0d00f0f095882d42c00aa004000c01741c100d8460554400e55230b82007401220501c0c02441c014280da500f040240c0c03401102d10303031004014219646c10000c00401c07081d0401d120f42e040c0c882c44c0e01088082c44100d03044601e031038802c403003240b0350303905000c40020b41040c280506407402c5441d104078000d603004081499601c0c8940210500081e540700801c0002610030b034000c0c541407620b600054034104101004909450000d21088140d4001c04244105000f800c011007004000206030501c1161598950410f224142c500c0a41030607103541901080c6d00c40c04064100c0e80070014510800c042000c0d0650a454020641c12404200c080000c503160086521012046541c01005007002c4e0116075a172a07648900a0210b1182d480a414200465013513a0504010810341e0a000140700317482c907000a180c034a0014900c2c20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 151261492 1250 151260242 151260287
    0x2202150d11040e19090615031511180604030b101706070c150902030d1101110405090601050703050d020f1e09030a022b0f0512040b090409020a170706 66
    0x10003c403201d880c0d2004800e55280140401e00e1548800b0308440307a4003c205a15029800031221002d043d010141c80c052200d096080741100c0e03e21084810145200c61400c13000d00000a038200f005030414419000a06094107059070b0f0740d01c4605068094a903910b9403240c1e45030511a1240c074900c014250000400108194240070f940a40104030500018000011f00403045400841c1c4e03402090350654058200d40c0c1510b03041c040100b8860000c00c1410b455420407030881500c12007401550196000204000c07080d40301d45005480c1a030003d40e044040c01001e00c40f0540e130100c01c0c40a0030b10160703150b09080c1c0e00c000c4001500400202e89405038903105041c420b038480340d203000400344a02c0b0390580e06200d0075a0021004040d05070303409121a004039408580800b0000c200250f40c0300310780700b581110030700303a00c0c884000c41e50f0080380529410360006100c20303011454a038002c01001c42c00504071401c65074484044061711584040c0c1c500113940302c50070401c11780c0e42c41444000b2030b0b4101d110144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 151262742 1250 151261492 151261499
    0xf03040f060c06020f0a030b031002070317100807060309030e0108090a0f0809060403050109110d02011407080913020a080a05060a0b131e03030e182202150d1104 71
    0x1240c00d003401010100204050b07400704000302a4110703081420004c0410340c032500d007804024080c0c840b01800fa8001d004c1d21070440c441c901c01e4001e88000d141d150709c6804c0c1e1546401403051024034003c2c1000304101b42954006540801030002e03a0240156581c017203004c18041c28054003028081600c0c07410401003404005107000085040e1040503440a1164038045140c1003102c0f540c05018003256002e180000c00000b040015400001e42030b1181150030700d500c010303000304a00514440d1029000c0307011546d10740900f001c524003c01d00fa5100d2011641040d80d40c1c00801e29880324401908080707540000d40301d1500b6007149030658041850002400f4a203044e40204004501c24868024580b00106501c0442140c038884140a080170084046040c8003103210400d244169100a41c04501042d9845401d4180b011541d0004402c1c61242006615035810a640c0d0074050300014050000007940c2c0c00040c3d658001c044480c40c40d0b525407540b68141c41c4030010072189030b840b940c101440108002c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 151263992 1250 151262742 151262759
    0xf0c030304032f1c0303180c0e0403050d1a0103050901200c0c060f03100603090b0606070201031d010501090f0204080d030b010c1502040608010506070b010e09150108010209030f0304 80
    0x100045120704810500300e0010b6494603604840030f07440568800311158040c1c1c850080000c019040d24081c0c1d030140030b4598440d42003002e200c036600c806071140612050a1250282c91681c0c90f4015200746000c900c0d1a400904034000c40c0c0384844988181c03500c02003154219a45402a140c005410200801042031080804030b0000c0d0220520817207110701058410a0007824022108003003005045569115082006081c03a0341c801ca558049424900c40007190f110b210748038000600c0e0388103089480a0721030201f004034130b030000001281050b03102c59002a1144140340503c500e590220008210355050009683c02d5035032482c4c846100903c140706c100801140090f1492517a50582800141c0d80c6150740100c03004083c404000d00030005078078807041410707081d50052040b100c142d590090b80d640c841c01042111721860b04040c003451a1800144010f1050b51201600700030345a08403100c41903030404000c9200400d0b440075800382d50202c0d40c0102ca04052203038001c20f02030100954602814614070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 151265242 1250 151263992 151264013
    0x7120b22030e0105121302040c0207030b0f060621070801120803040b0a1b18090b011d030106120602041e0609090b0402070819030c030203010b070b19020c0f0c03030403 74
    0x6800c00c045002d5001499000d10115458111100d0b0900f0310703450000c8400c48070080742d940c200e0040749050482c5107590f101003074900c2075a5218a80111980701c118511042e0000640000d034072070010010b540c842e000d40380b0844501d90290190800b50b15080e440a40300d454160f000c3d0101115010101000413449003c9a41c4603500420b0307100d0980325040c0000080543c9450303603d06c00d03c0c10004183c040c3d000107090340c403c0342c8031070602509a22807101d4800c1d50007040c000c0c2e01141c0039001895284405168000b00d803103014000199284e900d4401450103030581105440c5d0300d41c0010240031210407415038007042c0c14500030343c500305450940024140032462043d664401d58803000306102c0d035202d4040b200b080d900072901e5a00c4603d00035001d012880c6140040010030f240441c0508000c0c000d00a4074101d84840e0382140c01c02c0c40a0b16030b0000d1036070007050400081c001c03511a8401c0003841c40a031600450800040c005481d0381215641307440c82c1c800006109078414041000000c002114 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 151266492 1250 151265242 151265311
    0x1b05091b070503040f080f010c030c050406120b030601060309020a080604030c03050705011803050d051503030a2102040b04030210110a02040908070b071101111305010c020d0507120b 80
    0x12007541d0750403604050b4158000c540180906100002000410107000103804c50300400d402c000308500302c142441a01250f8000003502c02140003840100410707801307040c40480128103100041282641400001d0030044240c02c001c1c00b1943c2e500c4e041056040500039040900000c4000f0106400d01e600c1c00b4220685120004040100005591040040c203401c502150032541d1031905101d40d1600d4041e00d103400071154001c002d494500020b038010300c0342007048000310001d00994500307150a0821501c000300c400802424608811100c102d070203113440104001e110744003519894504510404c2912008001c0301e1081004445c0409030070312000c00c1c0f034409907504a40001b00729008e03240042c3c0c0e90095035406404d0a903417404001004e038022415034410340800e00204803840b40869130008600901d80c3c02c0241e0000320a051100d54040d00b121601640000c0048180d80d44d0b075a1903900c0e010840d00190a100d54243c603010400200303a1800c0e4022000000c04052100c010840303c1c0e262400b541c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 151267742 1250 151266492 151266541
    0x70614012702070c120f08160b06031b100306120804060e090c16060b030105040c06020609030a021002090604050a0f0306110f2a010606080f0a062102010203161b0509 73
    0x70b0b0400b00301b08001003540c0d400c0364400b80c515214401d45200c0c1920301c03c042c6045c1c88003011000054440c1c0350200311020780c0c1041d002035649100829080c4441c2e40601c86d04034050658a07a0089166154403c22155031031103044101e80d21410424003c11908030408a14061500c0c0c01c184920b40c4460000d50325012098000c01041c10218105040503284044165405529050500007031082e03440100c42612240d800325645600c415440c9a500c1c4200601100180c000c440c00820071303001da1300200b12028000f4040c500301a00e0301d00040c01807405604c443c06c2c1c0e108440d0104108050340c06403001c0000f00a0403a07040000c7c94907080401e00c1000e40540f001d21b40501d03100d4492103444c0c07800c009501000020043d991312100c015000341c1e41a80c004005a031030384d0024686400034011501607035000340c40c2e0050300c030580100e0079050ba010b030000ca0550000703014170105212a410302014917801410a140d4101c0001c00c0c10300c0c40456a003003940074203800030401071001c1d141402c20000709201c0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 151268992 1250 151267742 151267769
    0x71721071104021e070606060203030108030703030b03210d0b040513060b24180d0c061107030828020706050f09210601080610050108060105070614012702070c 70
    0x1e40001d000388115040c92001210340c10300311105025000142003440d2290b081040b2144d15a40166540d0009200d12000e681c0100101c0000a100e070f089042d200d407001d002c842d03803005030160383c1d00900d071400b410000404012404010340c1410b0301480d0800102518104582c0c1044d0b0300408440c0012400a80fa2035100e1422070b00503203c2c012400400300e050000700e400c5241040c04101654021240806510325a1019440615102600e03210090780011000d806629165060b14000c1d00403100280d07034011610004003080424000701205403d100d614000d00340c00e030108a01e00240350752044110f5200c078100b802402c0c1c01c0811544000030446820740c581d403018000034012284082c5a4540d003580311a00010440b0024030709069400c403009540e20703944e507120070900e012824401c03240041ca0400200c1c1d0315501540003803460500174a80414550015280a9182031080c2e00171900d0107810308403d031410301140c0280340c88400780901540350907140e84455480044500030000d205400c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 151270242 1250 151268992 151269023
    0x302070c060f08040f050f0d021b0102160e0c07080f040f0602060603060c0310080f06010e060114030610050706021803060702071410020106080a0605010306050105090618071107172107 81
    0x30007209080048a070100c5840010308c034002911069604d42480300680e032a05107050a600201da40c04070b0701951044640c40b18a840106e04903603e0280030072641c0001044400b001c0303041d0a0051041c0005038100c160380f00e15022148000240c9a07000e030b030454002a0900c202c650b0040ba0494016414180c1b82da00c0ea203070a203982608a042c0c2c0e00c007005900c540350440304626004a40b0314100e84041c041000e081da5402c0040d2340c0144010b1403003048100c01c000003005807421b80c0076600c00c183d0f189480c40c1045e0b40f9560b80e201720380c02849580c0caa1480700428413403d02e02000b4065105981b0700c040c19a60b460820098050101a00103a1140c0c010704000c00e8039920075406803000300290000c880100a103070900c1c1000b00320a000a80c1d921382068004962810b20b08485c1e80038840141c4165800785100203820910040035112604000002c9120000b50204100b46da01034810680c07010784110400741c0075441c08040400c4101c060496441c2c002d043c1064a054500b0305070094601d84c0142007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 151271492 1250 151270242 151270253
    0x22060c05060c04080c13060b0406030f0e0a0203120313060e0a05010606030b06070b1f15020c041b0f030b040e030c10060312050d14010e0718051302070203070b03070302070c060f08040f 81
    0x40e260400c081c1c5581c003180000d981032f8150404089181900c404200c03410025500702e449158641d4069099800f840010a10750b40c1e010083d43e01200d03010740c0d500181c003240c0e241d02c1900d0300d0300d108001640c00410301c1000d000080c0b01c0c9000510070342c1000c0001ca0079900101e015401086005049003480000042140250100c0103c000c1c1c48040800011a1503c05207250804a070b86840014418510250040d040a10501025900d020644406410b010904403144982d42c01800205502c5801c00b11b40c80c2c4460046a00c042c2ca0000515140e01c1b42d031034030a107485400000d1070b8902d810711700d0420100b4031200d141d4421071003515089230f80c7d01e80c18054001030452020f0440307451113001d0000035018424041c2900660785591a05803034504294403041c00a100e006059114140c4a42889440141e500a00e1824400703000d03540301c0c030b5442d4100c405580048801074080303900040c4500821100b081c424024040d80d0070200311024242c40020500c0740c0c02007000740200080070700c01d000e002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 151272742 1250 151271492 151271501
    0x10b09060a05100210090b010807150503010314011e0203010503100912033603140304200f060409050f0108030705070303120906180b100605030c22060c05060c04080c13 74
    0x1175820020310040b00c940c64000c00340d80c030911036420580603d031070101d080d0707c0c0d5481c806110003041d038919096900719121a05000e414500e5159159a5901c2244107080640030080d0200c0480030016100d40c90141814204503520520006081c07400004030001465500030149112071480c001a600340103d00340d02c0f5500000d034074152106805001c60540c0f61100981e20b10043c0701c1e6690b442d02d080c02c685040c9041c04180c500406145061a80c1e500c454004141c010414070700620403c0784a01500120300c140d4003075080403008640790b800300031030348840c101c0090060070060000e61800745940c4506441e28a03c1c08001c0402c05072a10b2030300c500b0007a40020f08040c0e00a0000c10082035501229442400f8803842100c0f01035528000420740c8110340020001c4030865120a45159140d000f1030110b903200107004810b6110310800310300d20b070462550351805412141c6031403402400c1c0c1e0800a01d0604c00801508402d5820041030081d0840032855900b070385419540e629002001040440c06131 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 151273992 1250 151272742 151272763
    0x809070609150201090209090f070603090f0303151502010222050d08030c19020f010b240904060f0806091005040201050702010806041118090f070f0f0207080d0c05010b09060a051002 80
    0x142102050023450325010501031450601780040b9004a66150410b8041d108148405060110440d40798800700303000c7d8208a200b507010048000b080ba0700e5036140c074404035030b000c1d1000040c0e45c00702c1c0c2d58a0a44602c540465034404110712541160715000000f40d1101d034441d00100322000100100381c1190141082c3c90b4241000c0c040f4900110307801030029507480c500b8880d00003070740c03c0240c3c8905a013031105e00c0c40102241c1800151121198109407100e03940701b007004940041d1380b54030000300c00c82900c4900000e03180c070002038201c0d030925001d200e10b00a4480000d07004030389442c040c000141e03000011503400c0c0c1d90a0822520541d6181e001800401c59043c681488503030002d06031a05888140b4409143c1108030b42000013601e420030f508145c03400c201c03091303004a04098440140b00e070041e607a80411100502c11190070316111641c841c2000c90358a01c660208024000503020041e0a004a406020040d0781e00c1c6070903d80500022800a0135120311030080c151b4400c0c541700c0314424070802525 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 151275242 1250 151273992 151273999
    0x1060f1211030a0c0804020901090c050c01050103050d2019030e0a0b0d0e010204031a041b0308071406060a1e080a0c091508030d0b0d0b040b0708090706091502010902 73
    0x340040c1008a41040d0b02c02c0b90b1001c001d0303140c9004684450302802000c0d0040c2c0d00a0031100c801c2c0e091001d5a401030642000c2103007444814440800c144200b40a403502a620410140900d000b500c4030140c844540e290480316401405011140c1c55480000c0ca0303800902d0100b48205180e01c1c82c03c05403110400b0410081d046100c100011400d054450b00a244020760305000300716807054007503070901b00d004501000308012100c04124841d103036482a8183c0080c019041100a080d60a221b000b80c0000d42d07104441c0c2000104a134000d1010102203510101c80c1d2034082d010740d00e041d400166008500c0d005d03000d15082c0008070340d0a122190010b010140610703000707c2d200030440342445403010407544903100c405418403400c8200844000c0c40700c4211400f0368011410282c8140380320f00075000c104000d50700070748501f03a01d2000c00c00071b029040c0228003c0e500401c41c0c0c03c2c60007004090400007003040c444c0340d0101c4c07010482035602410120854451014445541d9041e4004034090701c91044040d61 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 151276492 1250 151275242 151275251
    0xa17060f061801091509050f01031103010e1902120417040b0a0e04150807060813020d03050a1d0d060908040e090d020f1605040c020708010507020d0206130b01060f12 73
    0x16000d8008820b600c0004090b218108403036502c09145601c60711030700d200310020f4503080007001030b400c1012400451100504020950706089a024442c03034000f41c0c0a030000182010078000403100c030400e513420001c0d100205500e80000503ea01c0c01078000904000d1842504880710349124082e08282d9015124541e401c036a00d1022400060050202d096824415072410380103080320000329202030110f4040e00042d25509142c20000d94106038001c01048080041d80f00b42c400507611004243c1409201ea1665611028081c800a11041c41c40c420300d5141c102e07040c981d1801c0d541c1c0c0360801410a40c400000309411100e440c146a1901559020307034201c0041c1028052003400100c0e1801c407954003a401c41c1c400b2182d040d400b99950804d103060700620014240d09004500302038100b440380208900448031260380d110f41c2c4900f1900111180c0300180c01c40704842c410150305000007a080058140307400642080c90b196010f507054188039450600c230101211a0302503000300407112110444213000c12 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 151277742 1250 151276492 151276507
    0x5030c0a110c0439140708040902120103110306010b16050109050a0c080d05130501050a020a050601030c1802211305030408010f05010803070302070306202d0a17060f06 74
    0x14510744d407a1003103030a01c1d5400f5032000c2001000301d01c000f08080c8159a0000903404c80c0060000c503501c114800da41c541800c0101103001c050a000030280c031040074901508641c954140154418007103034003140b11390007100c01000126501000d661140d61800e1520503184064902607005011444006225004400e10102800350050000c030031900d806c010f4440540646204451512925030401000038a10701c0601095104c4e00160820841b503004540c0d810300503407a00c038a0242c3c00d0f482164151490001482085041c610707656000d03828000070b605004070701241044c40d0300040740701d200017210f500020341003281c880b00c1d0400040d017010035241e4031b03916501114040d00590000e54405820320b000010560b00c0007003120600c580680c05001e040d0f04558503400074200480000b111101c00030340303030341c07225805000400c41035041c002c558464200d07580034200600c0f1002038900300518248960300071030f40c00411003241004251154280b960300e0b000020380681464a0640e0810000700350740c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 151278992 1250 151277742 151277771
    0xf03031508060f01260601152610090207030801030609020a030215190836010f020d0e1609110706090f03031a0114030a09020d03180605030c0a110c04 66
    0x890588021034405c1c180b41c2500104280c90241401080e001c0340e20500c010000300c40c03600800c0c00031181c5490300c50642414074a001114003840c000700c401c0006035006005a001c18943e10b40010002c484042d400c103601d80d240074000c400c05110191a054030b03a5909021561a01c0300c400203503038020040314034030034281140d6000383c12007480e80742e41080788101c240809018a403c42d20404007562608900c06040380c1c0004090803050701e00e06062400650405440c400380104004034050000050700d50744000548403d44001c40c0d80c46085411030070044a121105600007000d8a1070b000c400309080d0b03c203041c10655403080c070741c020700114030b0300241400300a0310003076440026029070350a0208054640042546690040006004c60040c0e521801c80c103031210041c41d031000c0c0d40d600c001001c0c00c440d000320300c039641c41d51001c90001e4040c0c02803d242010ba01e40c0d80c4050314051500f43d0842c58485401d07520b500c02e4004c2c41c41440140c02c0503443c000c2c020844003441c04c0010784140303c005050b0113030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 151280242 1250 151278992 151279021
    0x5030106030b03120d0e011d03090901170a03050f070c0303030902091e160c021c031202040311120309120f10050f0402010305060a0909050c09130f0303150806 70
    0xc0300c0000b424040c8500c25894002402d015210981241501d01102045c50400a100c040031410281d500c52101d80c00b00c00003118440d0090440c60301469070750300000f080002c4404140c204501207290100750410b08040090341c444203591504040b55101c18443c40842d941c014440300602811005001208056268200103502d070310946007950300e51140418210b40c42c03004106039082040050000300d45035507000154003074054500780440e411401d6004a401886c410507004061030281c0450000c1583c01417401e207c0742c91f048000c40c1030604690301c0a072451480d21a00d44115814585401c42c010140102c1d05030950007840d0000340b201011407507444604c0711095a803180601d010860403014140500b034494120042140034642d03895005400521010f000039800451940c0003182e0034020707101c0c4080541c090b40040140d01c81031070803c640408000d203c0c44040c4098600d000002d60580f5402000b1507140c00c011070340310884445040b032100345d5800710009110b0300042c80300881e0709004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 151281492 1250 151280242 151280249
    0xc030702070f0f0f05030a0f170c03070803180f1f0204090f0c02010c17010302100201020f07060207060b0a05030d1d153703020c150702010b0a0501030c0e0f060f0307050301 76
    0xc02005031350b607490402d5220740c0c400d40d000d03040361240d403801c1d800620780c04140360327500c0309121000d810000e10a0340c0b58a96081035800319040c3c240003040c012002e82205035a00300690132401082248000600992034142004001c0c0814460b44220041810250151000f520300e841082006018020142002e03090080403200594039105031075005030720a11101c9800d04550390810102c0c0d2941d801d00110900c031480751411558203020401d84504441300809441e80582800350719844581080700c00c807030241150501c2091098401c01654502056041084d2144c1c144101e41d03540c0758104034025030095441c0c41d40008500c0d002c9600690000107451030440d0301c86a00c5120601d21142c8100d107010400c5002001041c4c0c01c41800648690010042c0c1040e04e4141d0324048045200d0404601060b1403000c0941d45540303901940d8200424a84014002440e041c815410712150151a01002c1d0310040d000d0342c01141f0840c2c098403101d0031180d861040311802c1c1e81c1c92411b1000200581c000b0300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 151282742 1250 151281492 151281509
    0x90a12050c270a11041e090c0903051c210b13060315020a0930060b040c0e09061c02090702061801111602010c05070801020c0c180c030702070f0f 64
    0x110780720b0301807881400c03186094132400d40d00d4141403e100c03459004502181100c1415031020114154a95004003660301c0b0040e19501c11660541c5811406c020f1441e01ca01c0b828581c6a80c1e990806900c07680366011b04800c107204507085210081c041c405031a02100241d0480116030200f0480c0c54603511042c110b078020400661058038054080080e4843d000d44100002c0d078441c000c1c03140309800300e47d0100d01420541c020421188070110500240b4107d0426035105641d03140544803810039000703c81ca8400c0510306204580030071800a070001c1405041c041c014904244071074404566031611b04881900104038000350314102200965420701140d08107030842d40094098003d030414003801d88424000b19071a8182081001008038a40d46940107074100b142041c40c03d00411018003110026240140001d0394400307010100501d0026070b00710072801046019825021646190780068212a03100c010581e40e8549031404c0b0b103041d410360421418030b4901d08002898080350541d4904890285 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 151283992 1250 151282742 151282819
    0x304050c031f1409060a020307050415031413170307020c09090a0303060e0106020a060209040209062d070c0308030a1d07081c020606040b0a0f03050705040e03090a12050c 75
    0x38140307030f05281c0f070907500364115a2048010034510300c0960081c56100ea81443c2c4036041c17070f69401c21485030a68820507080860340c0d8606182807400861006e50707215159000d40c0400c10100e07910210a50140c5107200f1007560f0100109104038401c0c0b00e00d12070164000d250030a030381842c03251282c41790141e50040300401d02d4018001154840c0140060480310150090a200c2180d80c641a02a500941c90f131648207a08000c0c610a44d914417020340050545981c1d0906540c400c1d00300e682114907007480703c9030500800c1c082100000c50381e1030340794107517030b1700588582c0c407501e5140158000e0503060304120311841000101500e0300da00000d00804403000982100c8040104241000c2449540700c01c450050300aa030020f0800c1c10150401c040b034a0001d88145000c83d41c424441100001e550000c54194000c00c200f0400c5242c180121001665400040c40c545620342000517041c182a102e4109426070816524052003c2880b820043c203d01402500f0100d030074030340d100c1505031100031a180880c0034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 151285242 1250 151283992 151284011
    0x15060501020105011d100e04050a1203050c0a0c0f06061d0705130611070503060c0406020f030f16170703170f010e010618170706110309150304050c031f 67
    0x501036a13040700d06a0101000301c164030101c1040c4070000034540c10341e900205e1000501220442c200314410f90042025044c0c05c26240f4010071480d220b00720380d504260408080c0a01c0007a0241190420742035410041003040c00781c0b8041070031590404014104074504040058102d81d40790359413004104410360803510740e0710034100795400e00406031103072042c101d0402e041c0031090140158902c164011000c4170810303940c6400007840c11760212510400c0010200d01000140d4040140840320090b50029500300f00381c00798100c00711b00034611003a10080d0815800b80500c99000c00e504c001c212090081c0b6035030005170a02070a40c02003001040d59040359280040c0c0700c5d07066554240d05807501c1410f00b0925902c0c081c82110500a11000e282900003110000a485041990903190312403012000c1c14085181643c05400c031011140c030008990000c00c48070b203603030760341078150480440749540c0c09032a525030781001841e004088201980510a039030140d800c4002b100841e092840303103440c00740f206900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 151286492 1250 151285242 151285247
    0x5070e0112031b0c05060306040b04050702072918060d0204080102030105011d0306041403120a06030c0e1501031503140718060b0f0702031606080906010e090a110a08070315060501 79
    0x41e950300c00b800c010004d500610062401000843d00624000c201084540e6618002411280d0540d1042c0269010b4030080000c04840048420700f1850400c0741c5524010701d003003802007131007114882030000360f450b44038444d160b640005561040704218011512903032240c8005000354403c1c041c00d8049000092007031103108003213141000c0382602a026041c40e44550799650051100030109040c640003d00000081c008140e1200c2d110304180040070450b1855824048080100c87d000701e804001e4060070000440c00400c01401d002c5030a19000507500301c00c4500c0c0801450f903030801020002d520b4010b401400001a017642641e001c800526942c0c064031141004481e518881c211400d103007803010510072412000613100860014007a1000c1d4030320032489050580d2203400c80f5001c2102c0d03074203000400408014031405000010540001414500341d51581d0b0010105c0c0140845030039407180038180c84414440c002002c0c09400c80f0b2986032207160420000003020060204d003441c00f07400151961 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 151287742 1250 151286492 151286537
    0x705040e03070b0603070506180f0301020a02030a141c02030601090819080706150308030103031404060e1c060f02090102010f0605061b0a020d03050c06090607051605070e011203 78
    0x8140c40290b103490100da5640e203121a00400c40c0c1c1d818026502d00154a8503080001c1c01581500a4141c20400000f0100301e1928074660030309010782e2061107001002c0b60004102d40e03118100f420301120700c015400018560340300d982013126031940700031ba820329401d5080d00078500403c026280e4100d99034845020342e0b038601c0401011040500603425450116001c0740050070114018003001c0751a10307a0005654403144544d00071035140d03000100400074154008650608610b03100d030703840d00c0d051510310018070f0f05070036507102c51248280014100a0101d005401e4050a5000c1014002001c035101460700075000502d240b4055402c00b00c0c030a21040c058801c141c190781c0014215070404070314440c1d00400c041c0080c4804001d10a90002d500135070755110800b0f04240c03285d5140c917600c0b0210541d143c1071020261225511764071800078071001f2900801503503060713400864004402c51031420501e14100141d1b01060b150007100e400414041c848a00b140b840301d01940b02ca1000451000c11440d11b031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 151288992 1250 151287742 151287761
    0x70b1b0d0b1c0503031605070c030506070215010305060703051e070807020c2e12051005040f090f11030a060e070303080705042111030d09140d021f0c0b04060e070504 73
    0x25081000040d403000c6c0a0041605180c0391458190704020b030660750004d0302d80b100e420980d1a0fa014804020300603904002c010a0200350144006207540766598140c4e41b100041e00361070038140c8071000100031190303011035111204171030303c03d01100d410300d03400180004900344e51050050003543c004c45018184405111001ca0040c0b00c0f0001403609900344042c40304405003a40304101004611825030400c1d401740502491a10700301020842c9060200000c51791038261080c0154105103042c404030341d40c2035040c8a2141c010b00800a0050503200103410b02500c540300a26162400c00e01c600089000500042030b2403098a441e022900d510106076a43e01840c070076200820302507a00420201070f070401e0100c1c058455840c00b10096007030000682810a0300c50104000341c0024410802140c8003582c4100880c000d07a244034804c0181c0d004a101100c1150041c0c1c2c8069400101c51030651059089950a6070040c2081c821410b0514012000c0d010001f01c02045e4031803250302080c0c038640ae00c20700154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 151290242 1250 151288992 151289003
    0x90402070c0509091207020d051f02180d02030a030305100b04030c05040b0301023a020301060c020a090c0c200604031b0608010f050d0302070806010906090608070506070b1b0d0b1c 79
    0x7000703007e508105615581040880300c600403003804480308041140c2007203000c8200b800c09070312070341c022a00400160207a01441d100706003403440d440260314041a80c0c000c2c01d4240c68080780c04e42e1000c500d01c481c50104c1c0d0040b2074030000060000284090a644801a24001c0354284181d0541404050a0340aa0404142c62601040140c50200c1c22020b60325030026440c1100ca90341025452400704a8000f64401c102003411800d000c000c600c0d04c41c0801000d8000e021007004400c2d08400d008013281c0c500c0c01c0040c002540c480301190140e541d05140d10281d080100300b203503240d48a02d030201d960903244112580880340c00401113a05800340f04100c1c1a50705010212580c10b00d08010041c0c48400c240d41a0705500566074046041c00c418040315000c0c18410758041509440c1000e00030885041c0d601c190120b8101107010f101c141c1d54101210076007500540050070503110240074400720085210341c403009c603100180811105010b90440a16864102e50003461112040780c110003407103030a0f000508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 151291492 1250 151290242 151290247
    0xd02010b060c0c101101090c0305060a0c02030a0f0c050a05071703030603030904050403050d14060a061404260a0b16020c010c02090a0b1305090606030a0804030215090402070c05090912 81
    0x203400c12010460130300380945000d03514401e58031096401c60300b000c5c0003601d1408590034103005000c02000000e4004250f40d0040049030000b82009460f402086007140c200a490011080814824030030121003035082011b0754641421441c003680e0700d1080d0300c904044c8041c0b00341c44103107204000c030550748504030281c0550301e008482c1c0c00700002000014030860a10100340402e032156407440c401d0b9000d03407090b940c21710080e00b048800c000001040d81d002c0d0040140500800a181c0d08510582d421100050049081d070791080b000765000b1041d03910148814451214200e00b07100009222a0041c40b4844602c51036114480c1d0490300ca454003c96540428402030040005007810341042c0d602c00390b012400910001020002010240c020142c0314420361100c0602584842c18822260415000c13001400300c0c0d400d550302c0310064005e910001c1e103d50610704400303001504030012565994001481159280d610745440c04403116180541401000284002951103800044190702c08074030300038150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 151292742 1250 151291492 151291513
    0xb0103080706110c1011090117040c08100c0906030b0102060f0408040f0b030906070c0f0611040b0408010f050c16111f0801090507050301060504090b0a0302120d02010b060c 76
    0x100c00e03807006604940700c0b80d80300c03924012050348101408580420300b0180440c441151343c0c003010b8441441080003400303020041c45115a0308400084800b00d0511805000c55580d418220b08040d00c3c0d9011402c540a014010601088070b0761040219044a48400c0000354640e403007201241e144c2185240568045004594030301d21115206074000e01c504d000c145000d858038509010606654000c3c16001c0b008000d1100c1440b00b130020a42c00401481d10413005626600c1d8101d0b14052808040c200c1c0eaa80d042e6080c8150b100d40860300905010001036544039600c8501900800b401c140320030502c2d2520012030303d149005030480b07004901002c0d0095001025886038400403a001020a174000b0b10350b241444114144030844103130140c0e07a254030003103600d4509001c09581c0c000340140100030301080107108064011041d502643c400c0840003403105c90034800b061580100760006980070340b07002100140100300045685a00100d5802408542c03400c6091210348d014807130450302250007120b94038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 151293992 1250 151292742 151292753
    0x70b04050103092f042f0c03090a0b0405010f08060105090f0d0209010b09090903040b030c0c1f0203011401020601080a030305061507061b050307020c0103150b041502010c0c0b0103 79
    0x1000d0460280e41005403404e103420620900d410740b0701500690505014101526203000e10801c5283c0c0b10214007140c100c90f006d4000e0702804007100c402807540601040076461104100107860300c0303400103090301c40700c5626035040804507001442110b00040300150028202c51003607003618041e62040c1c42c3c090501d20208200042e01c450702a060f03030800058130700305026981d03030180d850084c1001c2511660700c01c907000c240843e80c400280b00107440c0e4000c01c801c004201103035040742d0788400d004003507503187c49040302030307074204000f02c072a0f00c502e000042c0301041c8640741940118102c0b002854503080b10b401400059031212000d100b050402d0704034074843d5002c41c0c0607402503680030000524000100344200e032254070981117031400303503038081c2d4030075003240041c480c02c101420141b241d0a0181c214507103004002c0d82c80b01070000090400d42c480c81e49800e03a10003083c10b4005840e4660005488a48890301855040242c907820710041d82403207003480c4c0c40c2c0c2c00380f0203100b140390304002403032504e0f821a12071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 151295242 1250 151293992 151294001
    0x10801150c05120a17010b04030b06060705061915080709020a0905220c031109040917070609020a060e03250b0703020a060b060301052b0c0f17070b04050103 69
    0x4900601c404054190005141804200708040c01100d816480d01803030700000b084141c0004004501c40c85031401805141101c800b45e0b0112039005268180c2e80c1c0c0e40c0800300304113010300b43c001031140c0b040b1010300c02958a00991880041d6020008000c8424807140d0400266264818800c9581000900f400076600c660000c0010703841070f09190034855911804601c5200009403100386c4402040c03036101d4644064010b51460b90303501d2800b40100c040495145895105070303100b079803150366603040380c50030403d0411082d1a1618015081500c50034a810444041c255205d01244100000140410310b507010790400c1004a81c05030051891820505041001e080108080313201e0010241d4001444001c00005100030f40c444e6010b041c0300625450b01c04203840c00504079030711903442440107000a40350844076456a600b6141da116550101040001000c044460058400d008651005c1103000d400118001201e40a500441d10007550599003502c804003405803c5080004110400c001d40c4203422 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 151296492 1250 151295242 151295279
    0x1d01200a050438040906060923040e0d05090307050d0302030304200a0609150309030f03110d02041217030903070308071701030c1a071713080607030207060e0309010801 74
    0x30b03036820703102d0090055108030403d40c0402503901800103060204010034056140100420300300014114100702110500c0051000f49031815100c802007120746548a030003510701c0075050400e441c141d40401038014090f50203610210300074810714100088504190301d1303990300c0d150141e014500b140c64540e6000501400c00c1060007501c925076044071141d60f03e480700300005010030f880d0820014584200030180c0b601000111b41170600d8607030742c2c0021a13000310f00381b080c421280c50300180510a0000001e1030380a45280c41c140d082c800719003c143c044c03031440b410130018080e59150b40300d800c401c00000c40a1004803020890b80e0401e010400000380074112080d00907000b400e000e41c459203c020fa142d40440240d0080d82d004040c0801001504400c244401d2407440d0304002c0c0b4134100c00d54a070514940040707022411200400182c802542c10900c5000000e800460241c0d0220b0402c10341c01406900012000d5901d41e151401405603240700004454a10b50103031100da40c16841c2c640e49003901d121646 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 151297742 1250 151296492 151296539
    0x50d1a09180f060a05040605090a0f02040c0315031104050f0c090d03110105090a1403042904030f030306030210090315050c0c0102042414040b030a1d01200a0504 71
    0xd00750042e05040c0003843c46042c150344002901c1c941400d02c06c0655101511040c1d1540020082d5000b0544003070031810701c950143c0700400c80124020302100105055441c0410f4000c03000008003c0002c000820b00a481045a01748501d40b50a080c079a50070200786d46000c01c1d21170400c00c2c0866070810403407103c281c40c000e0800704900e41400c02d00c4c500b136440442d13440920340c02030002c8404000011b000c6d20005c4a200700114101410032515800040051403110011200c4985803507060300c000003114050342e4407402c1c60180e11460f1402a0182c4101d0100f05c3c41080310852620105200b8156001225000041007000080c00d04549008020140201440140030840083e074804240010001003030042441a03543d1079841036030f43d51944c00d81541c1e0412182c85440c0484907484025a019510031400741d50381e82e02d030101c0c800003c100d01c031030005904101c0c8004140c0d8070410f500200110200c45181c1ca0010342c003100c83c00c854030401600310081002444140542d0705c000c1342c05001c014491 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 151298992 1250 151297742 151297753
    0x100503100903030b21060901110a0309060e0d02030307120b0607030302090d33110421020a031a0610050a12090804090c1106040c03020d050319050d1a0918 68
    0x84d00801c4400c03d2a08044054850100850fa02e4000c02c100c8194406405402040551000503031440b1503c11041210700709500d800c0e0340c0e002d001c040e40c03184043e12901000c603584e50101b50b80180d100c0d042210100d000c60b1400f03100b403508849500030b030381400e0002003080d49401c2c01a60241c000b50001000702c0e4000072061525000100d0084955440c000717280c0d910702e111044034182041d485850050703c01d01038201200c2454140c055016035040e43c2c4901036440340e0030400324104d02c400d0185030b4007030750002102c00e0000c140700815041c0d00b000c2116a000701519030790002801840341d00e10f0324003070024804002900706544100d030400d084005220001c9255001ca4a03110065000794120040403030b80c90368061151600080d890204803030070b1018207118985500d0340502d60840b07110107405859240d0306c401c100042801212080c0c1c0c0c5507a07a0a81c5900e03a008e005246402c881c1d100c010b054541588070803501d1110030350401a00c00200040c200d503880c0c02d0030300c41c070003000c4603648004d2080e03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 151300242 1250 151298992 151299011
    0xa0c12060303090503070603020708121b0f030709080f060c090301090602070b0f011d011a0906070309030c12050c040906020408030c0607080a050906070e01050d2310050310090303 79
    0x2038000e0a004601035540e40440908150400d070510000d40d100c030341031500c1005440c000074020300a03034045011a410202003035560802c0b0300084001c491840b0100180022803090110f25180918040c11160ba924985c00da100c444650303651000000b0700356141e011000155114034110b00900d403061000d0300209001c061907640c54203a8201c1c010480c0d400c101c0504005240c95074000003401000c2c3c101691042c0026410000b000c1761060040d11410b00c0040002081e611406045030340c2007001a25003903503003205080c01006e0740310340e0004403010300210f8400640c3c880c0328150201c0d2185c11038060900c0410f47d000f0000101501901265580c0e000d02c00025039080c14006004100492409029103180c802d4001340501d20081c04540040c0c41d00040c0100c1100001c2c804c5d610508908040c0d420101140040e01c2c5400f0300b4035950b0b5801d08140ca0900c45019032282c0e007801c0c1d0755144a42c09907417103079502e00343e04003001e005898150380031001e5030541c1440d90f00b044a029000b401c000504403407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 151301492 1250 151300242 151300277
    0x518030904091b0e09120307140306040902060d0e0f1c0e1507050706030c03090b070c030c0506090a0515010e191415010e040c020c060c19030201090201081308030a0c 73
    0x40f154030110341d51100d4070800062001c14810513888103600644a403030b526000d1000b901c0c108032030180700102d290200c0056100c0c0c0fa02d90180740c2c1650000d00d00740d205c52140010308040e200c846030610b03103070055025000a0103000100c0e001018551281e00400b05442c100c11103002c054a40c41e960f20040c0c81d9454030f02c12031903d00608403103001d41e010b8807445080c003602400380d0740c0319440d040c10103142c1003010f4003144820b0306454001c0c245192150080383d40e401c0486010502d0340d800f0b082401b4102c1448918040001c0c0700c001180f09006030351a00782c045070740036000c6100344102080038402c1d00c001a000d00721214184c030224400000002c0005031b01c14001800842250b5840c803000342c0c443ea0307280961f00036085140440003140c1c00c1c030840640d200700175200c514076021540100b1011a403000907042c2406941004101c020541d2004021802d0090180200310800c0c1c0c08070b481c0402007a0008116040c0015981d08041c45900c6c545800c2c03031000051025035444e40030803c2e80c1580d00c40d61031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 151302742 1250 151301492 151301543
    0x20109090e0604030801120c0308090f0406060302130504020f030609061c0309030c0b071208090f121209070605120705121e0717130204090c060c06051803090409 71
    0x1030141d4028070340c9107440d04d40900700c000182c2210f5640c4c80040001000502118403607c10b99520601403602d95044401262140000082d0941d00c142400d10125221b54035501a11881070220b0846204075900d5081c0402c030b02c141100540260030800015183d0f0600b902d18982092001e01044170650360b000c6009103206858004600207004010b04005205c282e00040010300702d00426145001501d41d212a00005402c561005014003440080d1b109801440203400d41d069071070540300c6d0034494054a0300705038441c0d50017204215000000c5503007060300040302d109680058595510b0a110b2081c0a0402c0c10000c0c00740f01004003c10840d01c40086881180f070168441a86000c02401c010780705400021009207200c0030072010640a508030304056400c00e40081c0910680c604808550011902800740044060130340d02880d840014003036841145188158065503080020792220402181009041100354505520500c200c00c05c03403900e684240081b5200d00075403121020441e440c6211907 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 151303992 1250 151302742 151302761
    0x1b060c020315220c18050f070c0c151112040302010801060503060d170c0f0318060903070e01060f020106080105060a21170a0914100f02070503061512070e0a0902010909 74
    0x8244c034120404c0700c20b02142c0040c049400030310050050b4a418a070000b04520b000340365030204900c00786004140710142e01c04902030500915625603400c880240609400071308442d400b903038440c000b402c40704804c9100070364069070ba05030341d00c40c216440c224040740c0542000d00020b82c05100c4040281c000398144c0c005051884071620340c1d81e01e644003000094140300001009034150b80080080600002054010603400c0e041241c52684500c20030000c42c0c40c040c00d03500a0f980740c45100d0b001145c4c107900207042e84110001640207000c05d680300c4680754242c0740c05440241c3c0000c3c001c0814402d045d41070b07851402c1110228a0002000040d4440160314120403081204c070725000984100da6503884240d01010700142884025030709030300400305480d031441c0f5642c00704104802036802c502a20a006580041c40c00070103c41181c01d05141420811005207000b91103083d80405585003c3d0011448904540b03503c0030700c0d1250f5803516506d90140c055405c0032410001340a1010a079015248200c020030f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 151305242 1250 151303992 151304003
    0x2010b180405010b01081015140d06080616020705010806060c070e24060d1107050703050c0a1e091d01050c0910080405250e041b060c02031522 63
    0x10360806003010b508445404107218104248a030800c0210089500001c3c216400400080c210100301c860441e05420704401c000b80f03155001400858404040d0024020b980d1048251111a1114507024406008441103000541c0248100b04520740c0a06159580800c0c00380041c2c0c43c1004050b44242005502d070800c1125a80f01c07000e10032640c440a510f4a55684a14416000c1c2c141060024985010319216024000d0705d070a4101280a1144250752070168001c00300c40c1281d45034907285071030706454803540b03000e001200310015045070001c1d0811040c401ea1103030041445d003810001c00c058042e00d02140490b0031418a68280d12000b4030130781c0d1103a2144407074107485100d103400b04086a8901c8804100b00704042c0d0500010500202d0f044803a0b0004103104000c00c141415400d1042105900001902d24510b042205000101b0100381e001e021034600c0c100301c20b8442006440103400c040002c1d400d03a1080d2452007010190742c0c6d8003030300440c490900060706000c400c0c1115100842a204032030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 151306492 1250 151305242 151305289
    0xe13080c0d090501030603050c1c0503030907090f062105030c030a2a050601090504170703020d030c030e030909040c0504020415110105010b030a0b010311130f0b0307091502010b 78
    0x2075559004000001402003480c1c10701425181d0b0720b69617603680005602c5442980a040e200601140c410301601149910400796520f9241001400340ca40d03042c0d1140030340307007402c03d81c44d22110241c80c483d060564080c1542c2c4904c5800301030b0506041805814119503520041203480360b07962003080980341a060940d0390f0b5104917160300402c4550144002d100c604090792400d1100001c2d40407507041e0550f40e80d448009150b1781d41d42061020f00e0074200000180b107800042a80c1410760114400080044a03202800780709080e480440c00c40d50352749592036280c5c2050100c1307186864104900c50300300b0b000f680c5141a094442000504030390142d441030410544449003409000d42000d50311541ea01d2450007007100350b1524408600380d100c000d000ca08c0803a0b41d082d103442c1c640c0c06940980401c601410b60310780c6500c0c908170040c0087e6094001c0c2c510044c24000b0001e001c0007441c04070392151840e03641b1100b00b2450210361442c40c1d81c2c602c020800799500c500c501740342034941e0312507100300074242d208464 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 151307742 1250 151306492 151306513
    0xf0a0906050a050d031e0909090305030103030e030c0310020f0c0f0a33090305070b0a0204090e060114120a050307060911030c0a1802120a0e0f06100e13080c 69
    0x20781e00c00580c4994010014079400101185d0049001c40c00e0103004250513000740c04500c6c00300d80740d0100c3e8000030052842c0058070030515a105019505892194554041040c0c0d0b91f81015924000c6800180d41984000c0c0c03030041807001c40c1c0150a910b4032004a0a0400360201e4429003003100b10b081818855005202000911201c090100ca408401c03031076a048900061020070100603c001040d6040d58070385c00c2e4501050303c50f40480386401d4100010702054100201c125000c1e501070f116030381e1100d0404d0800c2e4046a0040364140c1200c0160241840006101090141500304064000114000c1259400108400b80000c0c051a44520000500d552492500304d046030a4030500d140641d01c90444402c0030f0701d40c10324100c1030300c0143c15002001c0001c030b40190080d1254a0011003001c005005022401405410513041c0384100426141d540031840141507850f00e00715910406200040c204000d451080c0311400d801c0141c0711960303044030b11180c69070700b455400074903921020b0344202d0710342 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 151308992 1250 151307742 151307749
    0xc010f050717060f01050d050a09030221090f03030408030d0f1409191410020403050c0906010503041704150203090405060109060507240c0503010e06180708060f0a090605 75
    0x565100e600360516002030819109070140d40c500041ca614013642c1010202c80d030a0780070304c040d1040000242404d010741c0c580f0224450107000e002c50110054032031081e80103501c080740e01040008081d045501404e2080300f03800c10090300c1c0007850071901030000700300206d81c0410038802040c91252800005c90fa017800760324500c00720340b0030740d001c410030101000030303c1036005e00451850741040314814203007100d00040c1003a85100e80403c00100e034030702c95802e03c0c18000c003168010388100c038058420341d003c031301c0b0620030302000e507000f01d0701d031400901c1c01c000040000d92410325800400d880307503528904090301c0b502c0e030241041c5149840c2000da031001c0354400a92405014103548102c082c07030014562031405402a0050140050041080b0601c031001c140b05540c680141d0059083c48405104009103004040c0c890340c42801214090505000001d002d030400c0500505070074940c041c01e01d041d6941c00030440392000098000b030362011440c080a0252343e00e48400c01c000e04450000090118648803c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 151310242 1250 151308992 151309001
    0xc050a0303021f0b0a0512010b10090e0f09061305010e070315200a1b0c0b0703020f010902030a0b0606120c090a24080c070501020406031a010203090a03031805060c010f 74
    0x1501c43c80d82403145006180e00c40c42041d5040313a2050300c45c51100041e20040b1805803031358004d11034200400341d140504095005444500312003015900da666a2290b10b00305084000131101d0f0034081d48001c000c5407003040c05180e80c13000c890040c40005107c0202da40c2da40e08000b902c0e0301c00e4030284288001030360310503582c0c0300d404150342480108501a0040c250a80401d0044180d00b10074040900e203c00302d030704071002034210600d60001507030010940700e11064056402c100f5064005108041010400e03000520411000940040080c0503010590b51090b1032101c004000580000050081c4101d6041201c1020701404030003013199103604844050119101195000301d01e038010803030420410300780200706503442d40da40340380c00640c43d52042f44603a418802c280004100d58400035001076100d42c1030f0701c94041d2007400108004404000001242e980c05494482603001c0c2c40403404000103405035420022015002e41c01e03c0601c2c0d038800c00114160020940552141d44519110000351920b224 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 151311492 1250 151310242 151310293
    0xb0304020f0f010e0f0f04061205010506120703060f14040c080f0a031407081204050303040605010609051e041b030506090c25050c0603040f02100311160c050a030302 73
    0x103902c00407080740c4000130b11400d02c40300071074052010b4080e013560075160100000c8480700003900038022a0754820a508114008520a45041d483c01e00458124502b0003170f005501482c0000903d505821a15480000d000620a560046903292001d04c42d403000004014440c134001e4840103800380c5031820079030800c2d922038210407064202d04543ea00003600302d01500313a0f07151400d41440d20340042c0e213404802c0d440f4031980a21000800300402080080c00030086101c2c074820507017801140d036a45020b8404803854003515512071142c101801110300c640900ba0300c2e651004001142c601070078400000001e44030140c0c100080e4403801040200d00340100c0e03c81e00b18440c4840d00e480c00750380d030703641c1403001451544444060028001503000e000003009811110f00c401843c031030303032418185080100c64108001c224054240c01e00c0c440c1c0d095000b885110141085081481c2c83c0c682d00704055042e280c20100b00b00c6002d90001030105242d180d050b00c040280d032181d001003807403e01030081c40041c01c14103203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 151312742 1250 151311492 151311499
    0xa0c140a0515010f031104060e01121401180201110703080f070302070e0105030c06030712180201020f0a0c050d0f05010207060623010f030b06090301090602180102030304051209030f06010b0304020f 87
    0x10060900102c000c0701c04c17260050000300c2011601030009001e40b030b41f5030080e21031a210400105800201c00a8000141d1054844441c05480030040c1402d841c40e140c0070840526007600c00d8805940900c0011600c010300000f0ba865a50703e0340c0d12120207401103075194445140c041202070805804022807005081e200da440f40d065072502d00005d80d58900da11803140200004030124001c1405181001e1001842101c10721800b26881204580c41ca02001c2c1030340140311f0000803401d102d00c0400e542076400e40245c85640c400742020140b0543c0070700410f00301e54565144080801085080c03014007107062141d02c01007209403805408003026140c4c200c443c240390310144209a00d5a80101103d140b40c859420003180f80b0340494001442800340c400c02e140c0550034005c0000811030598020405142164807a07107901c3c08203001243c0da80406c80b4014001c0d40150700b003440321a142d4020b09201203004085400046101c2d2100e4100700c000ea0007824558070100070321003140b4100e514002d49842c140e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 151313992 1250 151312742 151312783
    0x160206010e040204091a0103030e0f010309020f100207090e0601090b0a08100c050702060c0a03080a02040e01031104090c06090e070c03021b040b03031204110402120403050a0c140a05 80
    0x2894115a0302409800213101e035a4840b00001082a4004407019008610700c42d0303070540d80e690401600703484560b03103520700c148000b81440035558042d00c20060040c1c1c0241c1540d504003d03003814005280e08a41c0d003032007948251800010071500b00e000308400000400f02400841d40f5104c0e4000c01c1d180e8030540f00f44108031f046000d0005100002c1c108010300d18150010890b40390b116000e03a100e200f5454041e401000000304c0d55401e034000100e03c480c0c24403917922003140c0c4d80c0f038100c848224012030051909801c541d10041012510a10003005400c100410010740c0d00110307560910b5006050388054082001e10004200100c0d543c40c19550000140c01e10440002081d507000b515022040d10105141806030301c2c803280ea44441d031140b40c0040000d400c4903035880c1c00b014206012041102e0840b5107540c041c1c2640100d08140c0280c81146400e4080c1303c1d501e454503a8247c416410208142d000c1003040c0c0c8021000c43c51541c070030240c14904030054500444507041403400c0010380d55003c0c103000b210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 151315242 1250 151313992 151313999
    0x3190302190219060209180a0c1e020309010302030901180506010e130309092d0b0a23061c02030c1206010f0206011a1306031d1c110c0405010e16020601 67
    0x714041140f186a010b2001a6181e07080e500041c80d680000820030404c80c8100200089000a0750040c00c0007102c03600c0d0460413071000480c0d805488900032040b00140c009208100003035009030091500042c42ca000800e00400300d6a10b848440ea4103841500c0980c82134004000c000320f8050859040141185000d00d544159103016090f0840c0e4881c80548941d00c41f82011620040c03244605c1c044460034a0113810f070b40740d90102c00603062000300a44540d40381d0b2000184820b04d041c0c3c680540101010403004420a035041000300c1c0c22009001510344600420101940c0d005e01c001c43c81480c1e803000e60b54845082641d00117000400800c030310306000410b04115000ba40004056046880104021202503903800f00e81c5000c3c0034000111072907070303024103020590a41542110351051500311000050414444240307540d10040300c0300740003800130704410718402845040c40072000c612a804403141000c2180205003110701c240d000b503001c480080c0034064481d61480e59100002072038402420254103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 151316492 1250 151315242 151315273
    0xe060d090312200a0e09040606060906050306030d0807020307081201090b041401051302070507150e0910091d0303040f02010305060a030203060a0207050c0d0b01050103060f0b1605031903021902 85
    0x1ca2481507128440104071010130a12031000d503955504007900114440c2043e203000d00241540340a1030380400c0f141b041c00316010b40701d003040d2031042c20000c008115841001c40e09603000c503806403100046000070031080b0301041c8804000c00045507040b2840b6440d40c0b4140800b401c07919140d50446c0b08a0607c40c1c029001480460294155a41240c2004001520f040810001d00c10b501005140740500100064010f1052101001400c1540c0756030011922200400030010002c0383c020f440f50700b00a01c20b201e145400c3e800994070352841c005041100002c520780510b150011142281c5103804d14040c0802c55900d400f030290003c1040e58040d07540e07400d640c006615a44010703e05031120360701049581c01e0100c20000200d2450000d402d20070780112a040290b128142405078901083c117101002500d40c0c1c591030301a040340c0079180c0140c02c00c80180e00b1a010582d50410070f640d240b00600801d850003a0f010310f2081c034150240c40c0140d550b02d845090000e090780920804055410000e0030280710f01c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 151317742 1250 151316492 151316531
    0x1050f01120b06130f050603060f0c1603170901020306010e0102011506050d09140a0506150f09100b042601050c041802042c0f0114010f0e060d090312 66
    0xd50102e4810101e540d88008100010318141c0c40c08115410400356441c81c8926521050091000f542510a15500c06600c50780640c401d50701c01c80c06030f00401101003480d11107071a550380140700b403600250251601c080e411140405988919443e5400000d0018940e000301078209001c0e020700080c00101e210300c0c04611213060501c115401e1090000e40795001a0041d800010020351100240c801a80c3e444010380d6900b91255089449108040218010007140d000039060724100900340024030742c80c10107001003074202501d9030314808125540410481045d10240c8007070060094482c40c0d181d00c01a1120008887c80e402030b9003a40b4000502c5a8400401e04480c2510815100110740e6080c1e81448170080c440c5a0241c0074004d080e803084011010410414501020000d10400440c2c4500341c031a0384840003841010301811400c1e658504a5020b1924040040034cc1d090075401100001c0100d4465800085082d0080c1d42d604d080300304054005482107080100c12104026010043c1104003000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 151318992 1250 151317742 151317779
    0x60403030605120703031d0409020d111314010b0c031603030b011202041815030b0a0204030b16020d1b0f050f07170303060d150f09170918040c0806011701050f01 71
    0x40241c0412650b2901c407a04103e0380f883e130185c003440c2e400303090b42400c5840114000c82a44211803c003714040a95a8000c04a1402400380c0044c542d91030200151450340c03004808101e07030b010a006d0744d400c550301b400159204501913240030480204d4000014007048001c1d25406009106000a003d00c42442603c081c0800014a0019002c140c1024034048803011b54001004800c0340c1d001c03c801e485241d00a0000c81c0e104a2003065240c075003801c402045000010142c0060303000c6006090700701e200700c1c3c8180d404009034001d030300c500c1501d840e0300d10000e0b03c00c0800e44240d4032028085080300f40400c2120020400c6100c030740c8a140380646031948030300c8041c2c09035100b40e100180c11030501c800c1e424014600c1d000b43c1401c00020000180040240803590416182491184910301900136114100c0c0c03d00c6074000c5c0072601c10304e0540100c0103010310107402590b01000d054030209058030100001c40c040e001c036103600440ca1404031015803c1d54801050b00c000d41036410010000700d031400401d01c208 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 151320242 1250 151318992 151319027
    0x110a0204091403190e0a0b09040b04020912010e0609070806040b060631050102060601020d0315030203060f0907080106180207050f01050709170a0201090308030408090306040303060512070303 84
    0x1541d450600e5080e0003010401d80e81a4040090650702224400c8001d81d1410390a4450000003003581e070400220b08907510134560840da040080c08001d181c290700c0065a203100a100600301f00e000000704440d08494440041d5580d503071292009405800c0000507408074403c0c006003800750402111070f466500181005000c0b021450100b01e155a0310303010307502c0344062883c038426040c0c0304003812003181540500410714141b5101003c1825440130600a12034501a002001e080c0401c0ba012801018144840444011000300100040c3d80620a50780201d104905203c1681080340481e8100704480c0d200d0701701c40c0c1c0342140400c521204031140660400d520740e001a26a02d00e8200f803814040310901081d180c2d4038284c10810103582000480c401d40e42404c0340101c1181c000c1c4051991002e4000019000c41c02e804070410000f0a10401035074800d00c80c2035118108100071000ca4548075090b10200e012a807aa10144038a082c10078528051046a000070701125180d03417006440803880984540e170 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 151321492 1250 151320242 151320251
    0x103080a1103071514100b041403070b040b070c120c090f020c0f06070f05091f02030705030a09091103071706030a050601080607030b01090b0409020d06030219090c110a0204 76
    0x503400c00b482914285074100625449a040141942c0014840f22090b403030140d50400104103420301d0a1410f806507048096903500e03060611a466440c1d084007041207525115070320002c0358149203a0080c3c4020b00c10000b05a4480300340b490110416605038000403141119000c200b40440c81041c08041200c1c03100d00002076003410000e50301e0281c1b08550110406200310100162100c8002403518490301b03190b82e86514030b028030602200e0500c40c100711658071607a059585100e00810304031822000c0da403401101d00d400601d58a407420b40e0400191b0f83d02203480800100030800c1e45001d88035051914880b00c528500e0f000c030b8003900348001d02014200200300500054600d840230808107188980000480b0080e40c0c2d141403141c0d54400865440001909141c04843c0f55405550000141c1c0c44000320542080e09001010000b5089a00c00b040c201c1d4a816001015884851322000880d0180040210039410002c5010039070380d00f00d4107101001002c0c2054454690041101c4000c41d90480d000318 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 151322742 1250 151321492 151321517
    0x60709060519030c0314040f060e0c15090102011e020406020c0108010305100e16080327010f080a0b090412080108030a050d05090a120f08070206010302060304060c090b1b0705090103080a 82
    0xb002004e12441046c0440d02401c1800300f40040d9016600b500d502c1107905008042c10001c05c591100f515081d0740b030308640c0801d0701180b04490403010300a0244107100001d00d00d655914000ca01b25122a4110019a80041c0c2030203901d0781401150400902806d014681d5450740d691641d44184ea4401000390940d6600038407400311007480030800c080c88046d2200003941d00c1c0c11041d42c80368800c547d600500c0808802000081e00300e01d6070040044030503190f0758140ca82c402001e03154644020240d01140d940c40900035419503418585901030b41c0038030041c120070003001c48040c042c5041a00144c0d6a0b81c420f00043c80f0b469401021144140304480010440b40c40780c00303241d45071210510004141c5800b0980d10044243e002d0015440c5400341e50f03520b00c0c03544441c0010398540b402804003035008030042000401065194022089151580c41e11580071039542c80c0c0f960305608094090404c0c0d400742c46130704024500c10400039025180488500c0003030b5145664140302d51007602d45200078021096400c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 151323992 1250 151322742 151322747
    0x807030203010308160f210305010f030b0402100221072303040b1c020a0509130204050d060218090109050703061a0d18150209040e0606010c240905060709060519030c 73
    0x4038017055111f080030f00400c801d0450300070f011040e0110800041d14103400020f21869110300c442c11640c00125580180c0c6660b028000a62420b03280c0400394070501030400315446050000b4070f82c00302c0b141d100ca5181e248074540001152500114103180c2440850f40042d0503c0210440f801ca40c0003a0400e0341d21100c03088682c51035000d4542005400e440860340442158210004045c0c03405c0480c0c262402008a0010008900581c011706800c00f48212090700064038030340c0108105007180400301c0c41038a0f0390b4000382c04054260410f6600c103856405000505425000d0381c0d026205650341c0040c0c2044001c6102800e006000c4040c0013a0703121203040300001c15017401c101c441600005024191219462200040d43c005030f00b00d0700892420402d0041460003081031070203504140d4880e4041c01e4140c44201100040c0f2024103850403000c944000781ea00b8901ca803010640c440c401074a0b051420b0800a000b2080650060080c07013004c0059184245140d01100a906003074240040e00c0c543c0740504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 151325242 1250 151323992 151324013
    0xe01060e090403081f081207110a06050a030209040f0c120c0e030a081e0f070c0b03040f02090c04090e0109060617030a03021303080c0604060606030b0d02040509032206080703020301030816 83
    0x19181c0038007e0080c114094010080c12000d000307000081401c140c0c5024000120905e100d5040011014022102150300c01e070004d000758580200049204c220050584045560004502020139120702c5145820440350007100e04021103401c0c00c4103d1600d800c01300791203031a502c40003071260100040d404018510b640442030000c5188a070f1903103554004041e0240d0313521040c0240d40d0342d80140000608009504c081700d11072a8001d003140b140f001168284003410305c000d8449529640d05000c00b1918452910030010540041000810300101c1d030700388441140c0c0d464000603038106118441d41806070002040350344642c014600165171320b21004145410041603007008012040014042d030400a00190090081d03010342020402ea036503540c002c0e000c13645042c81c803d4110418900c00070251a1179031129601c0b032900b009681c81c28207041c1d580203046500b101004100a00050148800c6038041c54a5600c400d603420110701c0c65056071184075843c01101c0719441c00501031850941000a01040d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 151326492 1250 151325242 151325249
    0x1b0503040806010e040c080313091806050703021803010b0603070c03030b0a060903030e0d0c1203050405090c03070215041a040813060207171504080f130e01060e090403081f 76
    0x6440195858410004e003040c429203083c2c40310180aa000b003507192011080b01c604804420741c2d000c0e17140c50606a003010b09061800907280d40140d40021010884500a0601c2080942d4006070b0300c0381000849228641c10555040c0a43e140600d5650952203800849800110900b089490642c041c41d0031400303004020810354208185000018981b42c201c103072482564841e031122240c0c10400c106200104808041c0500040e1000c081008010860801c1d14022800b07072070070310312302501c0c0d601240d01c0d0b92040d206114540800800c1081382355040c07191700a00b184910406110341055241d040525140d0801c1e81c100c14011004101044207280881d021002405d2440050540e1080081e4842f81d9031722032000014400103500289484c0415040391120a0301d1190719640c44685a500aa8015080c5020a52410803a6040c08000d524280005101d0354242c031840c1e6062010003031100108618140c0225088814000000c1c0c1285801e5400390510f4040f00700011048510000d5610035403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 151327742 1250 151326492 151326509
    0x604090f050601081612150b19180605031611010e07050306010b070f0605070e030703060903020d1b0f170706050103121e080a0b04060b0304030905101b050304 70
    0x64056114105600128030522098841a44c60354542014450560103012080f0019012585404a201155106041a20040c118040c0c01522228a00d160b030340100d1318840b103070030345542e00c4d400183d0148802e00c4042040f1049401e0341c2ca841000b50030f41c00090250b0310716015080d800401980f280e0090501c0000c000000d0125045012400d0b48544290141c54064000c2c140003040008002c011100c0813a1f100c206552040c0b0107403500001010094901070810070003d03c2d40030f1640e030410a140140d4010742001804074010301d0064a00814060641e007440929020040002400c1d048900681c0e04141d0040b10119030780341125218000d0201901c4e507030030225903402801640c3c1e1105050380d1007600c0910981321621010b0b10041d1311584100d130040001c40c03100c800c1901c20016507400010707204012424030103c1b400076040d601c80d50021a90408044100300915510903182c0313000780003e54540130b45110050004080b0034900f1050001ca1715282e40a10810200b0805c860003004003a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 151328992 1250 151327742 151327751
    0xa050a03020c16030f020906040e0d120e0703030908010c1d04020a020709020c010609060e0906011e030206070b150d020a0b1303080403210203030106081902070c060f020d021506040506060409 84
    0x2880e201e00590007858040c0d006451447c0000c080f820f203842001c2519200c0707801048132201440b030480740a034603003004414541d220880011801300400035a4040d510a0703c402000606202031075003110850f0321054100310041c0402c803443c0c912905a8110034009880150b900c00050f007040c0e240400c47d60003065154800240c034224543c0643c840819120302030300900c03d46640c1c0003c07034000c800c00d03113114040b500403500400248004010030301c1000c01e03808407440039036540d4000480b03135000100c06940e40d80346c8204101285402c00a944c00540301160604010340c6941c02180c0490f4550040030490000010096400001c080d01c0703e0003940d21035105642c40c0d450f440d20181010103580c15801580e0000f070008030340d0b400030040d01c0c103842d2b0030b40c0d440100f03998030520b860928803442603000400303908022010116260041e4000500000d0b1282c080403150401300078034003600c0662203004c54002680c20a50301880d40d81071900010115030104660f2900800a1400c0c402c0b07a1103007100f240342 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 151330242 1250 151328992 151328999
    0x20c060f280f02070f03150b0328020f010203030f010b0a020f071404110f090607030e13142d040302190b0720030901080c0405120a15020a050a03020c16 67
    0x40941090703103904583c00d0b200040e035101c600d80c0724400c0600004001c1c00c02d24402000d450101d901551a20354000c04443c0b00c0c0c0c40321490398500317404038140d22241d4459a4054819806c0034441240201300038070045103140340031050b00c0b080c1041030140c0101580001260340b207540c800c120b6444c2d90342860080e80c002550740e079111035001044100c0c0f180a80c2c1420440c0306d21841e0102910446030002086c0c0e85040705d541704008142e40f00540440c240800c0c480c1c80315241c0ca0302c403202040054a500c00080e465241e14920601c20b5004100c44021007442201e4480c0d04194001e0101c0c0114440001c00b164030b071860181d042901840011440100c00c400c2201405010b01c0d0f05805074840da03c030b80b19445d40b80d01c07220609940c1c054030412143d000700000c02c01548240003482d80100c05c1100d66041a403200e001445c10301000c04103800f507511840c2c0000603c10b40001c8079807200500b40c011450200d00d644081c20b00d005001c1810b05042d8040b1704e0851525050094130154102e0070301c04d4010544 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 151331492 1250 151330242 151330247
    0x1f0b1213170a092303030706090501021b0105070306140102030d09020a090519060f030305040618090e07030b060f0a1203091a071103010506060f0903030714060402010f020c060f28 79
    0x5180c4285032aa40c00790302040c4184c00d810b40a100c0c141c0000d00a5460940b060704c554000d04510f0340201c41965003041500d45071160100b403400044041d4002240a003054a802070541d59541c2000c1e03c1d81000c41035000c103507030300003040700c80e1404030600114048209000244042605a201e0000300d030800041100c46101d803001e078240040200c0ac100290368075141c400304004040c0c0401000300f9020030061144c90300440380c03c1c2480e01444141c02c5101d4417803079140d09403500d080a01c0c01d1a480540c00f841085044900503502240684a008140071090005903584400c0d2090f141800941c8400a06062103012444e000d84030b059040c3c0752001d4814600f20841d884100c00340c58000311041d0132800392034180a03040c001c002c02031030307142170008070248a4104d90207854425414071042103481d000070b103108507410509081001401e0f4510781800050448a81291007008542007050307101c61a5071408151041711403103c4005858a868001c2000044a108180d596207080e00403482c0e501513 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 151332742 1250 151331492 151331507
    0x1009030302120c040501020615030115030303150518040807020d060203091606170f071211130e040f0b062d04150501090b13030b1f0b1213170a 63
    0x500d8203549003400e50f00c450803d038007801540141030050700306101090304005400c01102c9c3d18240100001010310103548411084001e03a8800c4022039290391380d40b40134030f0a908140e001004140d407015030811109000c00c180c03180c002d10041510002207040400d54803507041041009600000c04c650300d0a10751030040e5290744050402c1c02d10400110f0124100b4810710042a40c0044a82501010b8850350100511108020503c5003001209000c542402d119402842080783c00c805421783d8603110003040d116a0700864010b0600070007140103010020380d08903110100c058100c001584aa120540050300700d04a03099a0030329a102a072000e60074503c0c8146140655000300c0301001040b030b468411710903124181c841c1a0204030203180801138209803000504000303030307041d281d008602d0302c995030074880040035140c20103d069180056145070501c8032621000e07141c041c451078180740c0c080410507408100107154180d2010720303400d801c040084002020a4040c1b5040095131601c415050080100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 151333992 1250 151332742 151332757
    0x90f020f0309060a0f02070f030f05091513050102191101050405100503090c010e011b02131103010f0806040b0403121d0313150905060c0f0a03030614030c090a0b031009030302 77
    0x794031700880c8030b02c4401284225202c466110a41081c220b5407501c2c240d8110000104030b105010702040703030300216913400c400070b1a8819002042510360700c2c0b0020b42405820760343c1041c0c0c10b55100a2403082100c00c0b42c2c2501d40540c0d840403403001c01c0c0744403a0040719540680e070711690b0002c082440c1c0c4c001154001d00518480c101f2082100c1c4940500801101c0301c890000c256808190b800b0750f26412310017116240d07101d447c00070f0540b4250412a04505040b1040d0412064200c9404001800100c05000c401c400810704800200510b040544480303900420190006051003040c0f0826122a55240c004400b40c440f407414070045504c04504603600c0b0ba000712000307011495004404a8030410040d4100100b518941c0d50520041c101000c7c05407a03880104c804080380300303034060a02281c40c01c108500e40c2901c681d4010030505e150801c64040c80c0390960342984242c100d8110039006031150120039600002503000440c02011410202c1e080400d1001c00e0f8540d2801c200f00141810b03011340050440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 151335242 1250 151333992 151334011
    0xd091e0b0d052d060411070804120203061312030902010c060504050102130b1c09020d05071d01140f01030b0105040302150306030705010804080703080a060509180106090204060504090f020f030906 86
    0x2110851400b402e00c10380c161400b5629602d0307003004500701e07042c17541c080000101502c129626244880d11303420110b4005601040d51144040801821400d05101c4180c0010040c0904c2d103080c9a0b0382c2c1c1300d44240c24034031641c0d03041603035500f041410345e03101c0c04061004036000b640c100100d0030325080070340c040d5204c0d45c4501210148002c00040990700d840440d404465981490360003000e2035a0100040c10000c1410303644420907581401c00714209019a034001c000544100d400001c00e20a00c0025190503413100110304d0319800859000d450b60b0200c0344021000340303800102c003c402001a190380c000e0703800103500490700214400d004060400218000e0008030121040300d5680d0004480d00e05080b42d000748020f0042c080440000c0c001d0010b5608005944004121a500e0354040340000408541e0a003081c005101c040218003c203200b400090720703405009524041c148030001d4124803d5128403902d4a80d80c010013071b00d0f2002c5a0660f0241c1404011160740c034104440025178501c03003503424101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 151336492 1250 151335242 151335271
    0x30f061a03031e07020a150801091b0e090c0409061205100b03071403010204120305090a05040507140c0106380310030f0c21050105090d091e0b0d05 65
    0x351880c0c00003c2d51407886400e8564600080d0400b202e034803a8000e400101d800503200740300400c1308a003c0c0440c2d03002841c2951090318540c074005034401a00d04845c051044243c442c8001d0301c00c04e900500084c1061010b559509c2140c03621088803030540b00b10742c08030307070800c0c60805d004c1100d0881d42102c0701c2580c018001c9a410041205c414000c94070100c08095040c0c0c0f0400040044190098050b003105000400041c2840e03034403144c504456503003002c11400180e000920542c6480d002201601901042d10200524685214003800d80080b40072114010174010036200c0c0419400d4000350007801030080c08185d80c17649a94044102c40c481148080d02c1c00140988907501d0303e100381034038031810600f084070550314030b0350f04ca810749001882e1041d0b50003121300c1004039040689a540111039070034408846512a0142456403c4460140800f040742c4c12980d82a4a1150300142c4217050f141210300d10300310540c030046016007180c9150b1001e022014003280c61109094240e0100c0c1c418010b0b1407101e40d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 151337742 1250 151336492 151336541
    0x9050301060f170a0c0e0109050901050c0a0e040f0c0806150c03182d0a060c0f0201051614011e05100e070e06040806010303030e030310090506010504030f06 69
    0x142641c1d182c0c0079a00d0b1403034031a01e04001c203031142480009850b04950650382842055251035010064642081343c198003828010060382031148151540072490740300801c02d0341451054800709120f880c03060f508020007809074034200d98480d80605c0700c00d03180c0301042041c804064006000000e0489e40180303d804545c0d00c0e0390010308060111081103c002014500c5c4c07407602da40080392200811a130540106440808101055100e18026940611082040c1405c288072040000c050610b40040042000090060300005c040100c12881c0c0c644c2400c03c44e407950386a1100c2258440041e00c00b8000581101620104d00c0040d880042da905842c0909400d0741c1c4080158000e907101902c0400d01001074036020031405030400034080d006251403030039500000101e00000c80503082600f251402d5000100100101600351180c3e40c844041800510b04614001d4001c00346503901d40314444401da26103001a166a1185044401640d444400000344210500380b0303400a054140b1400410295035984d01c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 151338992 1250 151337742 151337749
    0x110405070f080112060e0102030a060f08070308031b09101e0306120b151203040f0e060603010b090f1002010903090f180b04020904090503070308010b1629090703030905 74
    0x1030780c0c80006a26000416441c003e9415042c0908100503908079644041c144a081001e000460041b02c0c0003101150321800c14241403500f500d1540007034419401101c0c10000101024103803075001880c0a105080f1140e003410442c06c51280f1103031194444241d04016440ca0341100552803850001f00c0280d8160b00c0c895420780407607045c1e0144a00840c003405034030f0000f402203240144d004030401c03034180c018510304002c50101c82003490300c866140c001050a00c11101c031541c0c80c000400301001070183c20b0401a005c2481884180a2200394503000954070450341c80d4030390300c041ea610340506030b00c101d520000c070001d0090460020440001d003400c4400204000320701004000e440103020a20262519140070000a054660b800d2b81c000f5028040c0362601c3d912445298691801307500075590f10300407443d00428001050b00143c2102c281401601d0485d004080b03c014441e07806582e44250222454000300040c0009011a28001d041820040016004035104007181d00c03039202c9141042c0c4031400c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 151340242 1250 151338992 151339007
    0x30109030c151a190f0b040602060906010b1e04031a01090e07080c010e010908030412120807140a0e090103081e0c0307030e01170a050709060c0302060403120b0402040311040507 78
    0x2035100f0031004040c0754010715042d4a42160490010809141c880d900c481c04c6255030b400b5070003410b01c580003140c10031106e60103022299000e0690405401290304003038001d91980160b00d010703600801d003c1d1001400c011b00030101d0f409076401101445070890601035180303441509001e803d16250404810a500407000152035081e141c03110050052a610440111012013186618504005549100040000061004001406408800804041403810300b0440d101c582030468040041b10320420a40d00c0d13012008080c903e848032003456132541e110508641c40080402d02540c448040d80c00001000802c0380240f01c0700780000302c461494032240c0e405044034010210141096001040b01c2e40000e0700c0740030301c01840101410840030501e40301c1103c1c20342c018100c404000650340d40d010321a0064000405a00904040c80c0c0b01046c080e56a50003034980784054402070912a10001c1030000c02000c0c0c2001d0f907119000703042113495941d2800e00d07200700d8440251080c02a45071001040410384180c84 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 151341492 1250 151340242 151340261
    0x9080604020f040b18040602070308071403040b04060b031b0307060c0804140a470711130e060a0c0c0c060f0314090a020102161a0d0902030109030c15 66
    0x10b00100260b00c0700c103000203052200d40c0264094070411042a11010100d6071502a0380101e4005803251a07504d0060500e0360058420002e11a281e0040c00407071010700304407035200d58400ca905031552183d140180181801404855141c000e00c0030000700c2c80c2c40102c074410418000c90031180d480c0e50381c0d0404e45003034000c0e6030080e20103e42044107005402500c0b5030b94920701c0c3d002d020021311036590610680444041001c2c0c84030380002d80c5030450700d640901c9405000d0085d850700c0c070002502c202c281e451a40720f100b5008003084100d0f4809004c95803050700c0c445221010700000d000c60140748600035294101110403030031183c0b4090b4100000c900c10100020510b0707024401d14a101e0414400784c03079580b4440822000c05880e0601409003803002c5d046a400381d1000300040c91800001e100184c01c1c003505808006a2070306400081118a2142c0089040100c42c601d42c240c3c0c03000804030391406080c3e0400060b405609000141c2c080603444102d111800c1e02a00c10000031800d03d000395010b580d020310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 151342742 1250 151341492 151341499
    0xc0903070b1803010903050316030209060702040c0c02060c1e010515010516080417010507080403390506010509091b01030c0e1005030a3204080714030a0908060402 72
    0x254140300e401c0c203030801403041d400500161000302030001c00090942e000d0203022070000c0c0000c4144103103e05a500070000c09655030030305509100340c80020507613070f00681c4d201074811500d5160307180c640c1d4040c0741b00c0101075801801581d540d4800d00c07411a643d05d598448104e824444c0d06e01c01c80108010310420340589529403050165400400044903141c00c900000f440540340740c1841c0d4001041c00000b003004200b00c1c40c14040003241903900a08540c002003e0005000c259402c01001a9000da10144100c54040346500c3c00c50706414002d101140b0342501c2400c0070640410301050110002d00380341210000c42d07503116a5503030b0300f4940e40c481038201903400405120407502e400640c042e41044120200515118043c044c040d00001e01e1142c000c2c4d10382010480020900145a5047c0194500450b0340558840d06603c1003084c88006207c4510480c035080440c0049420000310004a542d007a0301302484020400003101034a07100e13031184950b0004220f189100181001c00454098440da4008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 151343992 1250 151342742 151342753
    0x32018011520070513181205121e0709060c06181509150204030b011a0c030a023003160302041203030504060f05092a04091401050c0903 60
    0x526103120048030020080300340081c1ca03010000b180426500c1c0307030400c64104020140e5030304d8071052200d2640025844c42150342020300c21599020000c0752503c0c500d44c441d8a42c40c450b1350226003203d0500540800c0140452540148281c61354a4004000b142c18800c03007200280d1203103442a01c5500c0306201c1c8001103803001c200c000118820750700082e0342c6414420307542020710305a41c8051201810b2413008045990b500f010344140725403424112100c403010101140b500341192180c6089040501c180480100e21342a00c8080c010801d06031038591154508594407540700c1d000c0a5142d81c001c0305283c0c0d01c64800d45020424503140c441c00a041548201a01c0c61901c030315030584d40d024009031142c802c1c1f6400f04000100c003882e1039280b241041c0256000078550901d41382810644159144001445080805001d01840081b4880a882005115003248507042120b50200480090102d0780e11502d0046d40b04180055440c0c440d029400300c0000300066903800e0021280ca005d2001643e4241c1d010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 151345242 1250 151343992 151343999
    0x10030e0f0307050613110d0615081207020405060406050a081506060f071119091409030c06060904150606051803010c020712050f0316020102070b0306011202160c03201801 75
    0x6001c0b092840c030701031803609030a1038000700450313600c0f60301c0c487c100c0c0c2e21581d814120048204098031040580301000240c100050010000901030080000180c403841da030b00003141950351a64000030081c54050190b00c5140d6076151282d4032201490080243c0d0310304900003a22525001d000c03030b07403007000050116080203910384a9801c1c03544039084460700140e865400480981c24041300030b0042055440100d00380050301c06038010140c1c0604070802c190700511580102c0000410115440075081d07860809540e183c2c2044489184da0001c0117034140d180902c00b041c0c0b40e45c030070000c200b062400c1507a4550349503c001807600309c800060340c030401a00584424800a150b02c8002c450150041080301c5051024044d050b085a1005d22581e42080707015007943c0442d601848020001c1c0107505c441819850010000b03006904a40d00e044426030f800100d9140741101d103094620410780040499020940fa440d0090b03416802558184129091130f445802c43e1403c10f000304154891441003c0c0564079 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 151346492 1250 151345242 151345261
    0x90c090b03040302030706050405010204150203070b072703050c0406062c040e0f01061e03030806010813080c06150a050d06090c030b10030201030615020604030c060b10030e0f03070506 81
    0xb0704102d0440c0410030040010840900400d801a409040016500c070f02c2e1805690b150120081d0300d8041d50014040e100104910041865010040b8100b403254800341c2c11843d00d58820164400003003442548011040c42000501035404540c01c3d24100b0030720b600e0b50001d6458409140031615070000718840034610365032124580300f11410184c00031a019a100c41d83e41d09020006410320680d0390b5070441000036205034504009003500616000300f40d83c1c110b0f200240003840090010703061042d00300210b030f00300020b0b0985035401500b140362207444000e0a0100e9407280c00946064040e01042e4807990f1f1645480041070b02101c2000f840c0705601011039507044081c0580450650302141448800000308a844070700368410700401c80e01401e05401c61002600700c030601c1e0070a44c0e07107182815514880c039800041c401e42040e05404e01014054040c581203000d0499042155040444401c418a0b4036415402c0800900108000d440b07000b9060078190b580d90052000142240c1e0050012507030801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 151347742 1250 151346492 151346497
    0xe0f0d120201020913020705070e0402060421021302120108030c0d14040504050108061e06100503060a090606030e010f0c0503010612060e010e0402010806030a020901050103020c03040504091b090c090b 88
    0x3146000141c1402d055600156000b40540e01d4100131940001d050030070000d09220303c6003d001450342d010142c0c201a000300303c90303000b64081e0025005564400302c1c06142d400e440306015036401019001c08109041c02c10300603420040030b103440c1c2e40581c000880d00351400301c00d132107007000d030100201043d00c0500d50480e406200d8401441003480100000b0420781c49500643c0d000e0a860402829542420001007a48400c00401210112002c00500489507107118400341445046d02c5d09580325102e940004120f403565511070030116142110008200750141c000745464403044c402048404100310842080d1100c00c0e00d80c0f00000e0007017006000c01802190508960300c89000c0019005440d42072080ca1050203800c0141100c00742020003045680c440d4150340c0c08001500505214405a80850380d02001809140e041c1500481c40304c41c0020b0400c203603001840001c00c2405400b6590414030180390506420801c403800c000c2c004504542c4038010724120f51415503521407445d26201003c4003d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 151348992 1250 151347742 151347773
    0x50d05130b0c010608060a0e03040603050403170f1005030304080c0d050703141b0301020901080103120e0913051c08060613031a010801050a1116020f0a0801020a0e0f0d 74
    0x1845148011503144100d001500342c0440c01000001c0e41400e0004036880d11100600f180061400c05900320007058001c401d441c11981c3c28100410341e0b071682d01d0142e07001c100140741a01d00745c90680c00c000500002201c550b015254140e41290b0712500c82090648a128a0184000383d0f88006d000392aa400e00c61600910a405842990345041d165038508003100590b080605503540411000712000f0180b14400c030701803104030000c524003000800080c01d4103030b0501c0003404025440031a800010b000c1d603107041d02107000401a0030640351081d1003040c03c05c410300003034034680f06440e014400c40c001c6000d24100c0440035207d0300d65070380d2a9002c0044951000c030024480383c181c64400400900142d00b070303900b6105400c1102a056040c20082070844100800e10210f00741401640c9042c9042c81007140c40003024031a090f02113a40b0303400400c20300c0c0c11410046d50003046207000040c1908041d0301502d05440a035441d889000000750820004040c0b0b141c210b03a00c17201d035032100e400103204540000d024 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 151350242 1250 151348992 151349017
    0x80114010e0c0c10060905070c0f03140906120f0f06010c2a080c011103090a0306050c0705120a030605010906080c1804020310090612030522030602070627050d05 71
    0x5040300c80300f8031070a10710340c12002c0f484240c0b6002c040c0308079181401020740c0621249018400d41d007864803680c1a922901034040d0900802040081240c030040049845521000c2d00687da40c0f0360800000e0310070b00007150401c0c201c000c004089414405038000a90003124141e44038070305140301c0d844a01c3d402460403500f400440e140c01d40c40f400d506058070000300034044c6402400d100c04c1c0150001d010704140e01c1005a1641040100d108107a40d41035008050380c3e00f00c5000206076440100c1030015109202015166104040200902603181802440040703015601170003125541c40041d60314801034060301010440c940d0005503807032016005401c07014210012004900181d1020800720303801900d4618000100c900280100241405843c004000039030750722600c2c03606a14001d0040c003990a0749020303441e610050304042c40203010400051a000301c0115529000d600d0501c00910b060810781808009000d45260b80384644110401a5500007000e400c648036880011143c907070001004116 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 151351492 1250 151350242 151350247
    0x10305030a051810031a0a08061305010b060f0304031407020f0405040f020d0c0603200f07020d1a0a05072c03071d0406110a0e0f010c080c0a0309080114010e0c 70
    0x7035130b8803a2540a120011501e0024443c1e03944000c4a409168403c2d410340260740d070406c100215000020501d9000401d803610700c501403068038141b8050300d9400f4126034030000105500034000072040c0294020741c402e448480c1c5441c03e59030b01880350301070725002139031110103640d08401c64242500705a40c89441020702e118070350b0032a0f00007120360341400b1040c0e500c040041000d003d0300360107202e280701005001e10160269007001d141403815129104135482082d0000c05d0480440d211300200404d600e5010501d01002c0d07103411a50310700c1e000c1c1103c0c0a0465030600d03000c900d505001c0d0340d02c0b04a00c0c8071080060201d03e4042c41031485099540707409034162041c2000003a0107a8080c106e800101142000c445080c103107400c200c0207540c1c2c55460f18000920400500c64015001001143d280e0300a4a4161322000f00e40c00680c2d400c00d02a9001d0b0013070200103900e26038440082070090b81c3c588240c0f035401c4959101c00035242250741085020501800c03000c0140060110401c2143e40075241d00045407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 151352742 1250 151351492 151351537
    0x70302070206120f01030b060109080703080901020a080408030711090708040b09071d061801080d0807120501031212060506040909140319020d02030313030503090c041506090905010305030a05 84
    0x281c0000c44e03040d441c55000d10010700030002126041381e001902440c01d0390910341001c41440d1201c0541c40014041e000018100c83e07140d00900c100040309400c1a116034a03035554001c40350703c940c0288021905070028146406003850245c41050240c0b00301e5a440780380c0e690710340e40c3c501d1410026010a10610407890b0014030340e421959900118010301915068a05005050021991110b107503600485c4600c0d005002001001600401c0340d0340606d02242d06480d09803080d510f0b950004030545c20390342008008030034849440340041f82c5041a035102140200300c58114800c580e10f9004140d84004100020481220705800041440e4000c0190201040140c42802e146a0000001d1a041e0402c2140840d00ca5018031681c0410403d6001440c650300d0b15034240c0d42d881d00900c200130140000403011031200002000024810310010b00b0400c600240c900701c90144045620030500059960003020a0344038103801054100e0b40c1c000015410078000080c01e5401e5040003182c11031010038000c0c0340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 151353992 1250 151352742 151352767
    0x6030c0305060606120117011506020a02190503030f071b060806131a040b0a05060d05061809190614010e18012a0c0b04060f0f0b130c09080303100501180608070302070206 75
    0x140007413240d138009101d3300d840e41c414410b010030450044284055039a608110360b86010013124a0a4004110656120954a031200c20000c18070800c0d903030100082030210700660400d80f400c0c0910300454070118042455007500007500c00c4032305118210b140400389041c1d01c4c00e054125560a100042c060000c40f92248041942074000d00140300040f520345040c0845414a0720003d2183e1400d088002094074040019650300c082c580210785415903c400c07414148805603001030406001c41548044a5075507002d250240c007820b4a584c00c0c0d80b1001001044c86880511403100500000c1304a178102c045c0400340c125802040b048042c0911040078807074400200d0704880c031352055200d6940010901d4a105082c001c90b00000403500400e41f926540602c0381e0b035000401845400d0368000403480f00c1d0640000c07103001000da0700201c503901c0003000384400c215135600040c3c02d4417400ea03200c0d8981854111a04004d000c4c034031621010514150200703030707254401d030000d0003441d0001d05510310380244003522 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 151355242 1250 151353992 151354031
    0x4030f050f270f190b0706140403020604020a17060c03070201270605280903110a03050702120d170c071a04051204081504020d0606030c030506060612011701 69
    0x1840d00942e01d141044a061508400060050005880006080c5948894080c441c46280940300c0614004280350040101942011303120b9100c0343d1180da95400c242ca0042d5581c20161b6049100d51344496000c910289000407005800749510700800c030701d48071914040060b5002500c20340843d500c40502540b10f0110010b00c481d01c0702801024080001941007403011070718040d0880b100c20740c001040084444158884031645807840d50000f07201002c61400343c42c5980b000030b140110b401460103c105050b00720300a020914025500b00020112810019071911614801100846e00000840d0116201d050700c15900c420780030b004078076040441d02d608403c9001c0e10504041c190b030490030842044401d00c001c452041e003014095041130305281000d515084e00700401c03600243c1580000e410341d6620084003904c250008d01c01c000c0180c5908003040c00c5009800251003a2080601082c01818404100e5403040080c0504040303076403d0400311201082032905442c0c0642d01c460f00ca01c4280c030341198 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 151356492 1250 151355242 151355287
    0x902031305070b0a140901080403030b040902090a0609060e061516080324030703080d0c020106091407081311100e15090312090907030b0127061704030f050f 69
    0x100c29100c0200490003429400d000d8485d40280c04e06000e036062590300030840580007036160401041c416000c50203d4001c0c190710001035400754441041c000500c94681c40801a035010356810f001090f1903003041c0458500544546410480c0f401c1d2100b54003050708041c0881d681018414070f10500c0d291501c803201d130000d886002c40042c0d40c3e41120b4041c21401b1000022410a402400e1201d146454075159401140380c5554003a499900208005200b9400003003e0418480101304900c40440c00c0f180062003180c95501041a10010646000311050382e91580741c1d103c180c14058403000014004592000480c440034000002030800742e0340d585070200781041804281d071544481a0030b00305841c11031903490300390041d041005003110540343c8680d1140d00c0115030038042801c4504d4001201d030465200601c0c113040403084d200c89420700105c2804000c907265981d603811011400d44228203111015a0700901041e0031580082409000d40c000d0000b48828040d0702c0d060803082d8815101c002d50004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 151357742 1250 151356492 151356509
    0x230c01021308160e0702070918020907211a060c1b100503010b03090a0507080705030105010608240112060e0412020304060215040204020d0e03030a0e0d09090203130507 74
    0x161400310a507107401004024141c1d003009002251181d0340d000c850183c180507143d00e04400100003801c65000300400402444c0c2c0c49020021494591100d212000c00c500c1c0c101d100d9002c0b400030641e80703413188003c541d10141d21421840e142a0940407080281445050000d0030b20b05002600b041d552004068021107144034041c0a5048a9500480b090030320403481c10722900e0010f181014007680442038a05444044842c07640e641c0300c3c6c4900c3d40c60101301600c001d2662295280114800b0700220301003040b101c0950090180c1e9032205800d540e0f178501214004030000d85480c0010302c492041c405000c100a041c1420540869082030244c251200d5800208a00c0d03050342c03d00c01000080402d00700e20640c0380c805181001e040810080d2100414002442c0c079044982c0403405558942d41107072080c90710b203102041040040c1000310b03141c0d001102e200d41c01918142c0b0354510b100f0040b45c10010029030348d440a0503141031194100c003e42010302844501444042454001002008028003400036071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 151358992 1250 151357742 151357747
    0xb070c020a080f100e01060e10030b0c1c02071a0a32010522050403090501020c0a18090809060f0c0f01060303200f0d091806050604030201230c0102 65
    0x18018090708074100d5115002641c0b10003003510100c080820300b81c01060b080c0c0c101180341c904040c482409440706d80c204a0305442e03d10140402c0c1000140982d080300d1080700502001d5590180e01720150090340520700000e414010140c01101c0e00368010600c0900c510480c8004c0c0d090848141404001141c041d41426a50018003410504c500f0740d849952000c02820501000c01c0c40d807803068410184601401404c003182462410502c90102a00300740d8440e0080107903103070a042c0140026514440c1d40c0c00340c0101140402c0c3ea042082080c82591080070b11031050b03031b200c05149030003040e102c0c80541743c1000034001503410f03540d010300070314050018209058036041070105140c282016610303042030f5a80740140420000c0d4219031409880d10b0000c0b0500c12158800e822182003031980342c603d40040c085c005000e10030581142000701681c01048543d2410510400110121100c1d800380d40c1d4804002c1c001000150f109a000305801c104410801241c10203c0000c10626080004a4862039401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 151360242 1250 151358992 151359017
    0x1f1b0203091503010b0906070302031b0706030b100212030a150803030a0b0925050708031003110307210503070b04060606032016050316031808030306030316020406030b07 75
    0x7002c6140c480b004a041c860b00c0c65140056000d010b220310034601d805194085251402c0c14003d00030fa85900c054400d4055502c89000803442e1103140c1c60040d940480c1c60041b100300b46060401e060303814540d03d80c00500800280c44084105038100501c4108030075150344100c583c04400020403c01000c00c28019500c1c0e0070104441d600340c6500f600c00701e0242c0100c01c100040042d1700c074121480e0301104007060004400781d5a0848140c403a6050160403841c0000034002c801d40e203100f07a01b04a0b4001d03001005401c444504040c2c46003c0b0b4813a41e2041c1c4660011280131000701d0364001d070709a100b001201d00d800196550310007140e00888060356425590b040c01c03c800d60f00340c0641d0080b603007100101c155469140a250100740100c0c8036444441110141d400304202d1700f00101c0c1c2010051207091681c0014600d4001c0800d031140f07044c007000304186080001c0500d000019280030307410081c00780d400c3c203101c1da10034903072b418003014160b81c0039445920002c0810314035402940038001c159030f03604900c45d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 151361492 1250 151360242 151360249
    0x4051c090819020d08030603030403060513030210020c0a14070306090b0f0a0603080d0c090302031905010f0902090c070f150c0f090308090f0d0605010608180601081f1b020309 77
    0x81102d07030340c010504003150101c0181d4800222010b80e40c1d000c4100c6860342c1b92140424907500494000802051138103050002d8228003141c0540c03250700c01d5007100c1001e4204c02c1140f0582c012501100d000e50321410310080012080c0f41145020184801202c0b0555900d0b00ca64040c0d4a0b03030003007902d0401f240300501007400100c9a00d658410a40d46d03051007120710311380d1100104e10805100b15681ca40d03624600c4100391050000707a0065030028102c41a44620920101003220704000c100c82075843c048801000c0c29850007400b042d690014040105a5200318001d002a848284100c98801443c48820002403002d98076084512002600045d01c0c007000102505d60421820804d0500c884480200000b481440407281e00040986480e84480b402e00d000c1984405019402000b4034201000070411340d44c0690034510404401010700001480900d04940301c101c01c0c0a5240700d90040868072901d0f04000b80911184100444000303a242c10304d21040022002e401403842c0103801c0022508143d01c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 151362742 1250 151361492 151361503
    0x301150302091b0f030c1303031e140304030e0105070609030c0209060d1104110d02070503071b030302060403030b010c0605161101021614070803071103070906030503030a0504051c0908 81
    0x140000e40341450000d0303030f83d42070703500e07001d00404503035445000030006036100f60304c000361003400c121032180c003041c07a85a18000d40402e90310b040700c13650f20040c0041743e040f070362041004507140c42030407100920b903854544049410318801d162440c1844410006c41c8005005445000c00c210700a591714020b1800d18410041701c2c810150980d40305141d0120a170011459181100c01820320440d0005841801d00b5520b000b18041c110212803658070118075141409070100080448034458900d102c08c5c0d002c02001c441105029000c007900590104002030b0010380039500449000d501410088480c0a0039511481518400c40b003082c20707491040c45144800380c0060110305982d4100b802941045402c1c605a14829050741d0702911054001130b841000e180184a044060a0900c0580b41e13140b50900f042e00c49003100700c000b0f80c064480c1550016080c12984141c0044d00c1d4004045d610354ac41e4500340c2c00286c1809841a1050302440184a240e4603000c107c0c9442d442a58076002042d40c50194004d0074075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 151363992 1250 151362742 151362751
    0x80703090b030411040b0111030403080d0e031309020f0f03040809101b030804081b031b060606040303030e070810090c050306090706080a1806020405091e190209030115030209 77
    0x51406200b0f000005180394544400450292000a2070140c0400120713041c40040c5180b0003940800140031041c800401e00800704480002018001c0c102c452407401e96911440815580405075002e05005186040c1c0003030034984c400309195030900581c041c214015600a4070700315545200010801114140fa062501d01031051b8100004a00d6103010364107288041000001c1c20804c5482c002001c01502d0001d5502d401c0100b081041c609080c12801a5254007101840d202c00d0700c031544c9021403100000380135202d818081d00d52420301d884e41d50b058001c0c1c00052880388072801020310104064908001e4034080895102d404180918203003012550701415410039030280d0405410000c00001c0044c0c8002214450f20b03060407a9900c0001c0350008200303540c03403528084a0030018030144461500500180d4208507242c81807511200715600d00c4005000200b004424141c0c0001c403074103e0302c2c0710445041d40984000d880c0c00c80030300000342140e0020b61a201001c0e1682001d2095041009171309601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 151365242 1250 151363992 151364009
    0x90c02100515010c0212060a0b030f030c100f0207020d200409020901060e0612010e070906111b0d05010f0501080c090108031c06080a1a0714070f0c0e0408070309 71
    0x2801c2c0002c8000081e00d4810b03010381403041d080f2140046484010420f103c1081210959045d81445480c00000e0615070b241c083c8240301c0c604028040d1440842103401c0f40c10000002d15100c8100b1041502516141004188499082c4000d1001d40c861814400d00c4c01d01c21406001038140c0d22240c0340c80c0c00c10b0882c156005510305060080145c40d0303201d441d815166a030500702da0440d040c2d030000d28030b40302c3e08040001e119480400003c4507032208415900800913030311141801c5403220400c41d4003000003410f0342d04030743c803405028103070f42d45041140000006c098481b0010b02800c1d1107041c251694140500c0285503034400410502d8004d000300c6003039020482e00c00c4102c0d498400c449a4034051480103044221035500c501c7e8403030004d0f44c880750081103d02c083e00c110183c1c1d81880c0106904c100b2450050b00034580000b010a40300714103c03014282042c41143c100718850300c40c00800d000ea210300315070342c0c0300c0501301141c0643c0c040d42e918400c901c942ea003d65034203040e00c2e000380104202d0340401403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 151366492 1250 151365242 151365251
    0x1207080f0109150e04020607050f010b0f01170414030c0f0705040f05060109140303070f03030c090f051305180304030f030e010503060f0f130c1805030726070f090c0210 74
    0x740043d02580302c10858a20280080407501c403400098070511441c04010b000380319802000503441d030190410b0710355010071281201210034110055a0000707800c40e501c81d0358504800040d0005201980d1078400d030340720300c08581c20848501078480c50072902c410783c440f00d139024440c04c12161070103002d024224010a1000c0c000d604103000081d103005040d000e0320300720740b0030000d521400d52003c1007a42d49090700000e80341d48a194a0902400410b2100410400913000c00e0340401c2d6011441c07540f000311a00904041840b18a00c3c00c0c440041001070b041e41d45e008400000301c005804c0800241c03020314022203040051000310300d4042e00b0300e21562940380c14800d0600401c40340380da9101c520400100255901140300c01440002908600044e0030004028581843d0b0707051380d0740c40041059184107054803041d03040e8558003090355a02043c0305000c410042c06c001c08540001c11840660307080419801c80c2c501c2070b142c4d021400400084d400010f003503a5a0110b4000c034990401540c2c04d1213200080802 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 151367742 1250 151366492 151366511
    0xf020a090f0b120f1504020304060b09100f0b07020613030c1e081e01140c0408010b091308070222050f070c050c0402090109030c0816060f0203090d02061207080f0109 73
    0x81030300f5001040b08030480c84003000680c0c0c00405010f221032030500103004654a00d800e2078910000c0051070400e9000f5400f03038000840500300e800b5048196030126003d01d08461500c40c540c1040d80c45035900303e8001034107000c940080b03400c00d26040b000d544122005140141042c11380d0042404501034001d038044005420003c13140003241c2690125495942d0400c00841c20071194090071052480c43c0f16140c14a0400c07001c99494005081980d810b44004e01180759407808000950306d00741c07140c2c003401d1500b03c2410b001500300e4004004962000c1d100d1a2811501040c504458480880b083c940640741d80c104030810000c1d50b000d607401802800c00082100342500d403a5030740c02a00c44500c0c06907030300140d2120f40781e01a001100086034003a46039030f502071301d510f9190340ba40200ea65186c91289041c102041250048030026a1107000f94001e5090400310010010340142c2964141d8104604111241d0304000b500300b528412803103503c4210190406400040160034140e005800740f80c80d1000c41f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 151368992 1250 151367742 151367767
    0x609010f031106040b0c070302010f020307110603090c121020070605042303190f0804080a2a0b0f06010f080604020f210f04020d0602030405010f020a090f0b 69
    0x5403600b09145010b88403215001c69081d1003650801055180e0204002d424080c0005040050764402c0c0c0e5518000740190f6010380e0340b400ba80000a001009000100140b802c208015503442150102156036464818012a8420001128540d96900300390303000c2c00402e025002d40c0804614907410081481003d0444004502500c0c4c0020580d0b51601d0104040c002c0120100302c00038407800d412444007011241103a520345c01403c200007458000c546010000c4e0081000c2d014a0740303140c0b02c1031040d50750b82d41e070656143e101c41c02590501c40e8912003042403101e01c100003000e40700b041850700a00182410581000e500084c62180342c0c2c0540030801242c1d0740d006041820044240c104802c1640341e010000e0080d0044800e051909140031a428413019440c490032200c0700020f25107004c80b51070390411003003000c030101c6000e0f4028440c080c4090024026074001d581c07042c007407800021a500c0405906d0142d90007019041d000410410051000f15034041401004200b0300c0b541914103040305401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 151370242 1250 151368992 151369019
    0x6031012020307150c17040b31030804090509012c1f060e01060e0a0608060415170f0a0f0204150f0b0409050c0a020601150c020303030a05060405060901 67
    0xc1011003444144080215242006000003030a00802d009010b04000840107060071455a0290b400701d10340b00c4a0301c450f003c054115020b5803c40072496150014405602542c9090383c190a0000881e41244820652000c00040e021b98880e9a41c25681c526007503010094a102030500507559140c07824100081c481e002c900010740328003040101c1c5480704031030901e042c82021100e040307141866400410760040c640d801300003a1144100d002410b66250b1004036120740500b46581d0f009980804144600c41c020b80001c0e40c0030350001c001140040312448002002044c0c0e60050403148003c910103c0c24100500140703000c200301800030042c503006511402e02124031a840070303009a40e600104110101148040005002c840e450300741250b640342c55001c80380c0e025105011040745480b0100c2ca00c40e0000c4211049010b42d9401040340364245040c0784500c0000d004403409000021400c0401078a0505c065840350207079007230019580c9410b009200540c1e00007421144103800d00740040c440700852441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 151371492 1250 151370242 151370249
    0xc1c0c02100f0f350603010e060c0a0c0c050607030315081603200d0804060212030601051b01020c07030b04060f06050603070809030904050124050f16080f0a050a080105060310 77
    0xc1040d04c034583c02c150500440b00c41c40b16102c122000400c0c5807035148050421900590083d0020803203e07001e041142e0300d4140c10b8070040741e2540100100d03086c4600c030f14060380e051030007840403400da03903521000200c003075024000c1100480e8440511020041c0a120780344000c01582e0060512241464011800b0506500009242064005900c102d1a00c04030802c011408090003142044515080000a94200c0d00caa0f40040c4544c102003040c101400040c1c030300500701a11882e00f04402d40f242c0c400d0984000d00ca14042d99402e00060300f40700c030104240001103028408003a101d08003402e000050790300c0300200075081070820a040100391030780b0044a6000b600b51074523100e1a203800856504502c41c5001b082c1d03000c0d040030004515469078180e400d0b03c0c40c1e8100c3c070300c0c88100d204100544e010b01a506e10080c00440612403405100e10403425480c0c41e61146080758a4004d0f040341b80401c81e000004810001030020400c0040d03e90005403860241504581050440c602114800707440300c454007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 151372742 1250 151371492 151371497
    0x91b020f0d0c200306070c0b0618040b0402041506050705010e0106120308090c09040b06130b061b100203040813124403060f0103050f06060c1c0c02100f0f 68
    0x1a00c0400d400210304049020f0300805032282c07801c015800420807440c0803404d80e02c0701c1d030340c8021805070300e06222040341d80e91072702a80c1c2c0410754460f101c104840d43c0060060380c2003600c402c00c276a104082c0076440d0014000d02d0711070726110344803400e00c60b084500c080400b0103241e1600300180407a40340000c00c00743d40c80d8503241004c0b00c0c1c4e840c0c4c0400c5003880d00152800d90002c000300144410080c0d8000141e21a03c4140e5010400d2901070f8000e40541c3c03440e1394680d8003d00e00b0002d6000307054100d4440c3d0b8642c10350000f156030300c2d014050110100d92007150142c0b4404004101d5009444202c02058000c0c04c00748144038084e02c0503103581440000f48045000340034421911240703203c25a204403a40403207426408080a04003100c2203505500403550a881001240d034050403e40c040d200306401100c500c1d90000070343e0f55050500001d036004044502d035271b110b4803030352801c604100c403c0061501c2c145d54900030704440038414051008212615072091010030400400c1e4558898100640d2024031b2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 151373992 1250 151372742 151372763
    0x14030606040e10020c0d2709051305060a05060109050a0b0406120b040c02070302190b070b1302060a0f020d030e030a0e0609030d05031b0403020d0318091b020f0d0c 72
    0xc845a2601094461a9005134000300c1c051848880114070001450255240d10709413110041c0c013400c0c0500d203280b03103c6280002d40c40a0181000583c0642d0388542c00ca03040303951003072084d2242882c020302120303008a080d03100c5040200380d503400403510004000645002d000c0324100048102076000794096071013001a00086500902155040382101003c0a00100b2030301d40401d40081d110724080c00182c0c0203094141c40524521010310383c01c02100c4003003900034248826603403610b031040c501401c9440f841060310760176400b42c0e03216030080030f8a10f00c0762159840700751030a00181c18840d03064ac0c40c40034107180001240c4281e070007000f00c1e1503140301490300700f902810781030005001d40a00042c0c07a03090300c100d0035641e04068028005502a505410b1090f42800c40907014070311030711480c04000d40000402900a000900508800d090201c3d11405040d07141c2c1c0320103405c021101040310134070f0380f080c1c1803d000742a0380d01030203040b02c450030840141109600d601806032071800ca800002300550301c3d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 151375242 1250 151373992 151374011
    0x406020a0207051809060601050a09050603060f0a0b03010e0112020a05091f0801020a0806030705030309060f04150806040b010c020a18020d05010e0702100c020d11100501080102131403060604 84
    0xa02c54900a0031004182e60200203e420341940700a0701202d50307020f28412400400c00d590b00071030a4a08002a641d101750880d801e0a0601091343c0025007002d8000890026020480d41c82d00000c40190070400c0c03009442e5032401e9845030544c10103030700402c8829080420b840168995410510903100e040e640040d180d11148800b4507001c06064500c1001c182c030301c0011610000640091212880540d100040307515140201611020b00d0b22a0302e80c154002c120b800031504041002e454039131840d2002070708141e0b898421030034662210301d8040015001504000052916205a1480c50420b00e40b4011101160b4041a602ca81c1402442e01080c840301c142e144120f100c2c0c04450801841000911580d60340380100c20399100d003680c0200140c010f031410001c1400040c400d05540c400c11768010b181d00c1c080c40c5400c0e07882c050000348042c100d014406100050302e019004041c000c0c0055000140e131f0b00d40702618241007000c1b6030050001c54650706640c030281d0b503000607615080481194001801044d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 151376492 1250 151375242 151375247
    0x10c06051909141e0d0818011103190207020a0504050a020d090c0f060203030403020303010509060a120b010614070302060a02030a02090a06050d06170a030f020708150105031c02060406020a 83
    0x805001c03450030340d0a10640d102000300c00e00440d440c0980700411110119260310004103810120960701d85941d00403050090b16522400d00e1580003285460300008802000c0c90036401e4410030490340c1c10503034001091083c3d00e1300b101914014100c4200007182401595400203501c00c999225051040344c450000c200400a0340d0304680722220441c20801c02c490580c541442100300c01c0c49080c05006c00300c20700195450000c02201d1069506501071407540c3c1c2040100300d0001c40203007100d03400c1225000301203401d0010000340c105850003003c41160329850804001e044c84503407c030f090034131102842680d001940001e005030304154068030140c0c4139601e0894000080c006c0700941039114503c0100003403104c0d0003800518404484120a0109548450707081940044150b020b0403103030705c1441c0b0070012030301c40d42c0d081320a00d4041c03040d034100079543c40c4050719081c2c5040e04a0300103d0744400400c450b107010050f0340c2e0080c00100b0080310360b114000d000307911140000d102521407038000503400328030703407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 151377742 1250 151376492 151376521
    0x9010c08040b070f02040617030313170a021507030b01020a2d0f060c08010f18060e10050f040507091806081009050f0c06040504020d0f020304080c1b010c0605 70
    0xb840203686032075000b5818542c0c02120f000500364082c5180410200740032410f080e005004026000003145161a0421007030159425048140c030040090700b510203107030f02010010f010b4892558000c0c0f201c455a03804d01d0740c00000280c500e4062500e0070413604070f9640c003c5200ba45041e04142d1024502c0c82c8441011405013002c1c820110298004860701c042060b15000302801a025a0042040815621040c0c1d80b582082c01510540d02c6001c004100c0d164020400302c0401907402d0001c1030041c2c2d075000501c000f07117081e600d0320b1a00305000b07001e110505046c500900781a008517414003c2d400c102601400c04140c0e4003440032502854800f00380c00e5502c03500840000d000c0c2c00700301d6020080c824540c000620408808607054051000c4500c0403d2002688000b00f86c0d00420340f5141c10321307041c00c10000f5400110012081601e40307060841102c554805035101e94080c030748139640c821462210320f05201400300a2641d00c451044a5812a40d01c001c0e4a652103034050030005240c0c41d140400c0d003010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 151378992 1250 151377742 151377749
    0x816030609090c080d09031a04020f0306040605010810060f0506030408070c09140a0b0a0e130c030503090907051e070c0302030a1b060f080610030b0d030221040302030309010c0804 79
    0x1e81c10010150108118401d0a004440411054400101500c441110a40320610002e004000381307640c0080900070092045030442d100500540001d001d11022908251045034242c070000d80c1c4400400c00b21030b007400317188618100400f04201880c00d000c3d90b000c40104070b0203854000c0342c021002500304016282283c00b05904044640c2d01113555441620107805040c480e4000c148448000c07a80c209598014102d14640c028003041802c5d0030b00c03048000700341c0000c1420764045210f80b40030003c00d2001004102460280b4081e658507110340c2d00348584136001800403010031608105440c00e081460203044428103d000c005927991140e070402108421030740e00060b43c10702507180c05200b00500d11400e466040c1010011001075640d515051350017000c00c000640100740c544001030002d16003801032640d56140c50078005030b0319803c80c004c03c2201c03001c00ba0440c0583d01800c10300760881005031003580d148903100b140510300307411680465200e020740b804980c18005120880000c000e02c1d0000d44015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 151380242 1250 151378992 151379009
    0x1504020d080f09031204050609010c0221030403050114040201021906111902010f0501140630041a0c0d1a100c0b0c07080306120715050904051608160306 67
    0x307645412a0b03039595640b0121015100348940c1310750083d8020800141c0e0216800200590704040d100130041d20220040c0e40f00f26440960050b102050742270b10400d2540300429580116151415460414210b4505010807240010a4000c201c0180c1e400a50f440095041400e0729400e54602e1030210054081c0580002110340d01041844507807141c45081c800034103a44e4000d00c00c007000e170140681111001c0c052061032142c050744081c01420200002d2090652044281e180311400807404404c82c4203c0da0084054102c1e00240418400c01c00c0004011928200310241d040c1008540d144103441204021019135464002a1024400840f01550f4001010340141882d900c0528001c1a040d005ca40403030740300c43c0785800301d9141c011650a442c40c1e85e070701c0381020b40f13181c58030010409480100c02c81103005115000000c01d40820303100404104200940b502ca80310445c03401008141d070002440c0c035105040201c90703548030541c440035544e04034a070840000c44030a02804124040e2009800c01d006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 151381492 1250 151380242 151380247
    0x604080304150e211903081308090d05030403020901090509031c02070203060702060907090612030e03190312050c0c061f0807080a05070b13180b090f0403031d1504020d08 75
    0x1151003040c0c1c160900c04202085c0c400020f15501070f451342010081018000600b04c0e4000342c8070022120407072400500444566007403803d110002400300d659881c080b905034002060420450902c4c4681c82e0243c407642006010600e07041c2d91103580c03409080628000e0314040b03d103500071101164101c440c1c0d00e40186c142c804a103032050002e035584500b514842e015115000001852100e18801c0c1410745410f81021200103540e034038121480311000c0c07071040d454003c0b1400c0180c000980c0e520101c0c03240c82074035003044140c2c00a1107401102c10061003109070030b0003048a40740b130042c08250320341d0104079250100c00c0c3e025034246000403507009400043c42da105440000c120010006031240010344903d04880001d921190b03c484c1500078060001a10600108240540c81038405032217200341c0704030000102c0071aa6000507210b508182d8100260000300b00502c0145a0b041c0100011080c012207035025000d18040415074542d00040c11015919034507020804658441c2c85111507a40c1000300240c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 151382742 1250 151381492 151381519
    0x30c09060c031d0d12140c120d0212090a11010801050907120b0301060801050402100c03050706050c09130221060a052b030210050106020601060c080a03090c230604080304150e 77
    0x11000c07500700d084240403940f40b4803401b12030301d64042219100301040029046841801c1503c19203601300d036040300403440e001c1c4486031141036807180840c03040b490040200b02c00080d500f4103664154201412504010020005003d0350b100d44144540003401441c000408142c0e000383c01c0014a04a41c01981c15420000001038014054000d00e000e94000c0300c103c1195403140b4010741d030f104130682004010800a21120000c40e810b0390001d41e002c1d0024203807900e4920b4490001d01c0001f081809800c00a50100c1e001b00769a070742452800c00e90044d08100039060500d40c0002d40114254418140b09414481141c85044620900041c03043c074240c000300c801c41d6080c038002c1e4580000c5c1d1380000d00070f403400e000001c03003c3c4002845412180700c3c0e220145050055158010681e02c55065281495140c4041c08009070394001180000d04441c02c0500e017044204e580c05490442c0035940c240700d800240700c14491100c01000311411601480c46042440d504c0c190156003c00d0001d40c46030744940b182c0d1105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 151383992 1250 151382742 151382753
    0x307030c060f030615020601030b04050a12080f0708060307050d080d09030e09070806090a020a0e120601140301060f06030c021603050c090601030e060a0c05091906030c09060c031d0d 80
    0xd02e4a070110b0f803420300540d500c41c44d4600648a100303410038016804400104041115420720341e030024014030607180710b80416201e203002d50044246080006110700c0420030405601c030081070700f00105180914040c04c0c4503001a98031346450094a100c0c44180100764100540340046070f002100404e01480044c441382009840c0002c1c140138603001d003103e400081c01051150310b036107210303c0c0c004050505075100d6001c0f600c0290840300c4000140030703501c13408000c42c0d6940505d805030030322444020200c1c2d605005071940320302642e10446000340e04001050003402c00840d0f03a0f02c142c0b4403a260016102e62024000c030b1410041004015600401800100521101003410030040b08140c03943d00c01c84c2c40d424011000c071003500c0307469034064014201088035071055030010f440600e00741c6011424840700000161a4110301c0c02607040c1c0b2a003c00c01085140e4040c014881c05d0303e42400c1400801c1e04c0c20300064042d5034208401020000c0303040320480001d0b0990302020382a14050b0185980c1902407500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 151385242 1250 151383992 151384007
    0x1a280f1a0111032122050a0204061a090603150d110f010801030807020d0c08030a0203030a050f1306110d090b060310050603070501210c021506180f060307030c06 71
    0x1850004104800d00b0a40c45000030866220041003064a180080009041085034078041c01c5070010070315a032185115078149010f0307460102d0151010348130001d818030401c011a6016404658580000218410b1045942c0280c9a002005880320f80d0340c0d5032804c6007160305010341c80040d6400303ca0081200c060002603403807442029020b40c1c1500040c024540103650002c001d100081c03c0304030820085005040441100359018420b00c140c6450755250b440075030940c0c214000d400d00581c03020041160f8000c650040c503410021000002e0001c3c01e00c0040c1200d44816000040c00c50380c2c03210410348001d48108201c40702c20300d182c00100310145d2245440803d05000f95111440b0b44524210f200e815a007070b1080d2030082600900411404e49420015558038198005080907090b0100c1c0d00e0a10420500a50950349015405803c18000240030003407e0100a40210f0042c1e041c0002d03d94240c00310a00143c1115003545403000a5403908002803030486039410080c0850082e600008146400008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 151386492 1250 151385242 151385291
    0x203010509030309240c0903011104090209030c06090303030708090f121b0c01051b0a0c1d0a0504030503040f08070c08030a0f03181b09020f071a280f 66
    0x20b48121071a140e00c0701001100700380d84100102c85c88008034040205ea0030003441d104c140900089403007400040c40305a142c00603880b000e000b41d00001c030100a444e06028002c0c80c12011200c1c203083c60f851001182d0f5a0000403c200b05011194021500e83d1400b00600c0403100d18a030b08540414888800d06c1d02d69420096044907101e190120f10300d101d2700d02003000c00c2044010380d1040d0801c0849007a03203410460360324034540d050240c80488030103d00369440a1000d0900c414000c8030610444115070b1103424000c0000a0952509040c080000c7d800300450703800c113070490440d400c0300130142410001f501c500c205c000c5c40250080700009046d00c0c0400074040f160142e455000c2c3c21003851400350300340c40a0303807004641e15456003490000507154420f125003507a004040304002980381e802c0035007268071a000d204031405001c2004420014881c2070225084241e285c6403d180c01c1407000218240c0c100800440b66100c1001d03600349107940303948107204003010000e02b80079a20800c10b80c01e083c11100d80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 151387742 1250 151386492 151386511
    0x10213060806010807080703110301120308010806041703040804080a0b0612030c0307060e03040f090f050105060c0d140f0409060e0a0219030e0307020a2d1802090a0302030105090303 80
    0x400910340d400342021610420060b1103904195607000350413507031800d000f411002410307601e002c100414000b039005513000c1c059501c503146404440c2c2c2030141a801059016507178507805401048001940750046803e50080e0401542d100d44891920280a009a802c095040d1250300340680c244001c444c5201e02a20080d11621655200341d10403a0301e03071240110300000c99204100c51000511a0741c000351042e01c0e1003040c2c1f0304103902c408114150400c2d076071045031a50b8031108002014281e505c110760040034201c6105140903401b00070152617124052050080c002d08400c0c00c0003403454035045585d50800440c02c2e5035240c2c1c50340540d00c0100103600900954a8404002031004940d40c405c80f01000e4507440d500c4c0503e208030304210080d000d042840d4160380018130003140141c075440c20b000301601c2c500c000c24032103d4200800c038805202c483c102300000c2c0d040040c02c0084004500100d901d41003c4403001d1b03a149518070103d4880c60841c0e100940542c42c110420140c0100440510302510000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 151388992 1250 151387742 151387777
    0x30806240712140f1801020d270b1201060f0306061b0c0b0c0a061a010503240613051e090a090c030813030b0c03010e152e020c0607050303040b0c04080a050102 70
    0x500049a492008c860920081111490394605404081d070445000f14240360385540c4030394940c000f807142500260318804150f842c1200510a180d0844035814400800b0300d020441d8a1030000010281590f05103a4040101889480004d00101c090329030f0180c840c44040c2641c3c1d40c0c404261643d12039001c04140e500300e19110045581c25268100b6142403a4140c1d20329003141c941459040e4041003581314411407500c41211034406884070000b805220701c1e000750310b520451a02c1c0911000a0700020110865620b1030000d0801d9650406e44941082c0700c03440c0096400321514001100380040d810103040040045080c142e81003300128070242c9226080c03517505510340c43c2c3c45007036a0100f8094825100c000200003078600380c02c0b40908ca14030038020004c9125250b544c100340446403000043ca0012a10304070440e0202e50100154030129600b501c40500d03144150f1900d545a0002510040096500202041a1454500c01d58029001c001c054a400301411328000f4000e6106094401200ca8003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 151390242 1250 151388992 151389037
    0x6070803070e03010e0705181509100317040303030b010804051e0a06060306060302010f05070b0604110f031008070512030d0c090f0e04020f040501051e03070909030806240712140f 79
    0x1030341030b0307016a404119242764014140100035441c0c5c801481c1c800e20541c0b04200001260300f0700720410a05071005129595103045080040036214040004c03818007001c80e00f84400110001120002c0d100c941d0200f05d2462011180c2e241000c0e911200038181c80e0402c0404011b02c0070683c030960440e40700f601c0343d145440c0c280c80c05aa041c081d0040c058410300c0c10500050310b03410705401005514a0100c1403514100007a00c000754207130000d07198008031540495081c414a82c0400024000d0038045074065040121701c00c1d0345640b44134170221916a1511035800241d880d018025007030190002403680a801c5486040c0002d500400312000e03403241032003940803102400c0c1442001c0c1a210041c220300f440510919280d000f02060306682c5805118841d0009040700c01803258800141c403e03a90301c181401d180b400c0113070101d1030005145015035030041c01300030402101c0c2101d0210794446485840704010b4081035034103c0070031204180420000800a0050381000c00605135009142039040c0340052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 151391492 1250 151390242 151390279
    0x40c120308151203070609080405040e0a031218030315080708061b090a0302010e0a0503010f0207200d0f0302030d0213060f020f06060d02130606030504150b06070803070e03010e0705 80
    0x1000803a2110130341003001400d02146050700244481802140700d94601a5900045021149090b40011082e008018130f80109036114142d8110f032080b24000b07114004841c2000400181180c80003002d065071402880c40d400c965480c0e6078000c11243c000c2c1d07084656100c81d040e40303d5a0446400706249058030680c401c0e07200007002d9504814018000350b50721810340d4019101a02c02c98150360740300e904080d0000b0196424000d40082003184200948c0b9500705142c002146103140000c161209140e2071100e51907151001e04001c0c1640010403505103803042d04069041d4400c0020301140d0500008a0900f62442d03000028126002c0703030307102c1c24048030340701d000c03615040b0324003030341810f84c0201010030f00900d80310b889041c6441c0001c2124400007071283d100030450f5502da0102c40880c0d100c030204070030300040307880303004020b02446010b1060401b40e00008103680702310900101701c0305001c0085116141704030f5449040c0c180140c0200080c84c0b405508980d29409807141602c10030030340710160481c1d003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 151392742 1250 151391492 151391509
    0x5161b05060705030a1b020115050d02060304060209060f070b15040c140a090e090d180303080601050a03020d1505120c030a2a090e010b01081608040c12030815 70
    0x40d080006001141c641e120111200e40c0301034400c403025511590b4408044400013802544102a5000007401342d14aa00c00c6000c00f01035403146214000d82d0340d0000c00b6031100c0c401c0301e6010f0360000e80103a076000010005034241c090343d0303051840c00302c01103056030810180b481414003641282d9850018894070b42d081005a41c4500203603000900c02c0021442c440003400e02500b041d02141c1080568207071a655403280950044401d080070343d00c80a1025101c503002424000c10f041b404105440c4d260640c0c8015100a80240c0030130304001c0001a4280020312030750540780c0500c00381a09001c02600c01c2d01c096800d02040c007030b29118051260010b0020100080c02c02000800034010303229022158540c400c040000b5500c8181c000c40c66460b2110001015001030054852007a002808080d85a6410b0848032481c0070a414001100144003c120074290310241c02411450602c8d030603070701d503c0d10700b106152950028040e16207580452041540004041b1321450052104000c00d2613003404020400e03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 151393992 1250 151392742 151392797
    0x30905040c0f0c210201060e06030d05040e070e130507020c06031006051c020f0705101806020d060315020a021615050c0114070504030506060406050109050f01120516 73
    0x140401041d4040382d030061521030b400c0d0307004031300d40c01082c90034034182c0030280c03042840580140d5480740c05001c180c03d0b0ba54015005042540201406043c0c000051b201c1c0c41107004a044845002d8006000144113614104000c1409801000701e06d8107480302c2000790500303039a010050b0007800c041800905002d01964820006e10f0b84100c03865140003c140c900380d10035603d607007040c05859a084c8400c0c20b213000401c2180300c01c50485d80d407501a82041030501c00c14100111004d410082414882d1181c2d0055406075a0007500042ea10303841a60f2801c002c000301e5000034a0404552004000c400d49580940260104d980a0703c1d45820040e0001514030468054541000320341182e4101840c81a0054650a031000c00001407550352032101008101040f20f0fa42e000a00005017070080140038410700d0303000f5505480c1070000a0074400080c05014060145074000c00c0c0b0020101400d038030175205564120040001000a030404103e81c000308030b0800415400710315809007540c010488040818000b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 151395242 1250 151393992 151393997
    0xf070503120702010f1e0c03020903190c080a05101d06010609050a141c030c0c030f020114130501120207020a090b0a0b1903020315060c011d0316060b03011107080403030905040c 78
    0x72000c6941b4118000c000c00c0780d41100301a400c0c0710007600f036281003014135101d484880400380ca15103140382c0006481d2154010307000e0f6810030307101000011000141c0700e0300100341000204100e05010b5130200f1040100a600c0613510440000145458111840b40141d603825500c40c0003090b165001c1d40c2d40d504031140e04540281200d10003050400f2000c9100c0c079050701c02d01e46188121520f848040b810506604107480d00e2000703500600840d0307007203005501c000e056480118108020080e000c409884540316048c14130245015030000060154102e890b001d40c0200070b1007045072213021000080606003601c90094200c0d00d400310320680e083d800c2d9a204554448603151100b001d90085019420141800d01e940f00014003800c030070764805010742603010141d00005051550b000e009032040010100850154008110307441c51042201c00502c8020b0308124003080491707241c4003090041c11884c00c2d87c100b5140120320031040082500003801100d00a6584103c2c90740c54008010860380c2c0850038101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 151396492 1250 151395242 151395281
    0xd1b02040518012313031d010e060a03050603011d06070c030201060b0a03050a0c030203010f0b0702130603050a020f0109140d0c050a081005060616120e1e0a0e1006050f070503120702010f 82
    0x200200c247c69620000e40e41031401107602440100811641c0d000a203008002c282c84004000c11810240725080ba584400030451004200d100e82d500d031117280242183e030230001c084051b4014103000350800d5004040040321135a441969038002002050141d80c0d03901908d00f80031400d8001031080c02075038180c807405c1000102d81464a070b03180c4680e81c01884101d800c14820034175005400024420040254000c03009040841030b00d20401c04d4001031070a106050020304081441200c43c0003070315000e08002501d0100f01041c030741c1002c0c06885640d40c8082d1f8014100382e00030814500105001c0c5400c6100c8200b0f1085880744410016070b4001c18056000d001030205410001c1150000111107640040c180040c515a84034003040c2045543c500c401c0110040d60810851800c0c030040c01001010710307540b1000c0d14200060840e9010380030748a06410002d0100d000400d00003902c1c112146103500c101200d54401c6c2005802d950614100c0e000800b552030100d02101000030760240f0080780c0c0d01c4140c003a5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 151397742 1250 151396492 151396517
    0x718052403280203011d0103080f0a0e030d02031b071401032301030b061002070803070201050915030103030309172b020706020409050105030d1b0204051801231303 72
    0xc0350364000408240d800c258103401c0c040303061121460060051221040941d4941c10484500b01c05201040d80f540c4400d0408010000300d04582c065946010300c0d070300d00c039070f54605910301121407030350480503554107001d030b0100701c0c00e003076000030092107245542e03240b8108000307543c00d20030344440388ca103c0d4140012003180c544940d0b601c0382d44158184400b00420182107406110f00000d051300c243c200310380584208090200b1490081e0b0444160317038080c401404090309005d01c00da2030340184040207060207400f086001c1140e0361400f0384039141208503001c07510b2b581e6030305008024150098045da01e0400c1e1075800d0304040c404400700c5150680700b140031a0b5001d181e2510302050351441802072030580d401c0c0186000208140004e0004145d107800c04255075060404144c103102030040408140410580d40006070105808402c80150b01100d001130a03644101c1640d4420700480001d0415529010305541c88251290010b204100040c815a407a96a4100456840400a14080d002c0342130304140720b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 151398992 1250 151397742 151397809
    0x110d02060412110f0109031103070f111c0f030e042d0f0603150c090513020a09030209090f0705030f0a0b0907050301180312020412020907030b09071805 67
    0x503440c210030b618011100035009022503080600c07807500c500040e51503003000401e05034003200001c034801c2407a000d103290400325500c1d1079804070000401400110012110145542d4500c0f10040100744c0c220026444090761800c0c8641d120b000d2811001300d840704004048500b4140700d00180205e0507120356541d6052040041e914854003101c14485985500d104201d00d9000e00a113401075202d029a001d5203880c0010003016280820000320801000c007908009035034a030904108180210400182c1c1c0b1400e41008450190f22500040c0d00529400d080c0003206500168104004030f580f004d4035035450b2284101911201e11303c0c204403107640080f0001002c1004519000d42007004101203415450b07a41e00030a007581c548005400010007400380c5607052541107564001b0310030301d08004502d40382c100074000003c0401c16030080e0250204000044619009511038103007108020001c000b40d19005400820440d40300310746c0c1c04e00d40b040b182c0015043c02c01c0c0b14a002c1c101c0c20903540d5015042c90f250325 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 151400242 1250 151398992 151399013
    0x2e0b040311031c0c0203061806011502030d060308041d090309060a0903050a060507080f0103051f14010b030105030c04110a0305040f08040b0901090503150610050912070303110d020604 81
    0x2282d4540126000c2c5241c070704840302c403181c10720855156409803c40d94010181040320051a40c00382d2555101050015440442c020303054035080d4100c1c4d820460902401c900d10f00521640d81482458688040207200020f000390080701c0340d01445922414104100440240f41920388441c1a482880045030b10301e0540090000301c01540f62524240e03135a41c0b81e5515200550000303684480e070b10b0082c4480d056001c0501580100e085040801030751650b40c4265480f603120341d030010407050840c0354816414840c5c1086241201c400d0603000d465840b072101007250362007840b60511070304c0340400300012418540524910b250901c81e20354140740984106030050300b40100100c0305100307040c0c0d0b20f0300050722500240c07000c2c14500d2242600d80012500152410040390001b9100768007120ba01100040700ca05030343e40c0200b06803a2500100000c440a46050252021596000d000044400000e01002529008490007a03030355170600ba0b01844003a0b12054941000d40c01a00b15200003000314045112 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 151401492 1250 151400242 151400273
    0x20a05010c02031b190e040506070c120f300b190b0d0615090806010f081c02190b04050d0c050d030e24040308090d0e0f0312032e0b0403 60
    0xb509045c1518240404120a402c00b80340050000180001e0002c00c202d1907a10410900384000c0341000b6882e820f0101003441c108100700000d0300584100070340f041c5170000d007144040c61008200c400214048044016007000c05905074030b007540d04501403a010b00d564020f544a0a41070002e103046c9075012031598081c10111414640303c03c00061007616400840501104681d01e8401c02800c16000c50300707118040e4480d0142500c902000c1c0040a0045001600e00c259645c4200002c51f580000740d003000f5150030401c0c030b003480035084d0b41c2c02e109207812402c1c0304a00c070b070054560380d0040100c1030f1000882024090f10740c2e0300c01c81c03050b10303c14001da004d010440301c410101c541c0400014203414144038165060f0140e16a48001c0c8020182c2184801d500154182d0241c5212111001e00403c99540480002e12840f613100e2403410310384051080e40715110700c00810950341e24040a0b44040040d10030b000c2d00d030307070f100e1054007a00c481406201c1f07005031924640e0552a092079a01c515210b02c0d010305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 151402742 1250 151401492 151401499
    0x901050a1209050a150b03120904022107050a12180f06090206070f03110109150b12010c02031210051008060414070f0f020114130302030c06010603020403020a05010c02031b 76
    0x9142d04081641000303401e1a240c4180c0340050784610440f520000e441143c55024000e5001c490100c0d81d200e00c80085c2c596411742a1401138a640c4401d0780724602d06840701592001079484001d220a0645c400c00420100c0025203a6805040709450910111303000e00c42c540c0c1110082401060001c1c55480280300d4141c015078000c074890200383c00055440d4040a030495030b0b10501820300c420560070190b8041c085d000705008014801148d100c0107082c04500190419040d50380d200d10700282e4030080c00c2402c900194008000c000b8000102170750700e5012001580c0c45000003400205400d14600c06103082d900003134240c1c601450b084030107499400021782060380c09506c070074264079a10031036840c0ca84a012160382c0d040c500101030310007800d02e0012524490859050145da09081c0c0e00b0071004603007024800b00c0411101d0440c0c2412429400b0b040c0400b0010300400c00001699945034001e031090340c0c0221000380301d582c0c1d09ca0064401005401e002905904814514400c415040000c0840220081e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 151403992 1250 151402742 151402751
    0x5180c120733050702090603160b030702030d020705070e0c071203180206070605060a090204050303040b03090c0306130507050607030e0f12030703031a0f0303030a0f140103030503070f0201020901050a12 89
    0x81268442c010300d0b1100c2800090300c003192000a40c582801c54580104c001e50141913401c0450006030720510701c50080208081000000c280c00d14801c208460395105050421074881845103401038854a02d0b1080184841500d00814100300c42002101c811079400401a40c0303460700b02d40e00380c0281c55800614140180007104410150b02e42100500392a48503041c00585440d2030030030800d00b2011a042216114418842031100d40c03400800c40342a55030790072a4644030b58640d0309032482c02100641554060140509000d5102224822140c51504c14802d4070070140c2c40b603040c05428051400090002005582082c5240c01c2455041c2c2030205c02405c40c20b49458056541490350b0f101480c1100000d07510401c036111040d0418900c48200760458840c0001400d45001999900000d0103026a8a554850121028540c1e50003880c0e010300a001408056950303041c090440c0cac0084640f0004a030440c0304c1130780d2300c904c107200326070342d14105844450400030122301c04c42c0c100540541009006548 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 151405242 1250 151403992 151404059
    0x200a02060f0a200a021504170307140309010e01031e0e10050606090a030b0c09030a030503010918120509062812020c03250605180c1207 60
    0x10103004003036806058034203942e01e807103a003030041c00d051444000030031030b10618107000809070003c559201401e0701129824509032418060f043d20b0706c40c2d076112400e80282001925078000300403015007907407800360000c100500715189940381c9034411189141e000490b40340c1b50a807558043e5200c40e248081a00d003004003511000000c004442e20340382250a141c1c030010240d1007488947c0903003035114905030740c0d0a00b400601c070049040c2d00c4041c0001003940d46180005180d946a103800e41e001c03004002d040303070100070303c41c10302500c2980280103220080d414a00c401d600c4080d6240301d08040e81e030140b101e041c0d5440d0702c403085809400c60000c055010b80104201c10300c100441c440010b030030703100c1c0c6000b00c001016020060f102c1c0802906a1100e0f50044c07110a1202c00e000c01035400c890940c208155840c40300c0911070a680440d02002445145403009104400d02e00344850304865881104868205400c03408011403024188841c9445600440b002d01140c83c00c1c2804280f1101c44022900e8620364 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 151406492 1250 151405242 151405249
    0x41a07060e060a0e0a0b04080903101a01081807050103020d0b03340e060409110409060b0109120f0f0302070510260f04060b0136060f200a02 62
    0x200003805240e581c0c400e0042c4211400f0070301c0b0b084410350026004001d0444195611506108010000361020001068850307040c1c03818020801122060310041200b452850504809548040d550500191840000510300742c10b424410600120342002410707200e00d0040118080d40c04403001001c510380305c070620680b0380c5042107d1401a1070000000710b9502c11080d036400c49030b5583c2c0301f140c02e99000500c1005400700e000703403154111005903000304c1d0704035080c1025000c2e40c4e6403600c07203030b0894902006d10040c880c1d81d5101d00c4106200343c0ea40c3e00001c0e074440c00068814450007019240100c050882c400003400b0308400f01f041e901c40e005890074075682d4070001d8048161294a400885c0020015820401c02c13007811441d0b05046080e440c5890030514021008240c0081000302000d9172844030700300036806020111003400c04032620414400840b60648000041d039140e068448110210115000d809036001c2d0a81030060f03659480203158038104440d1160183c42050b02501a004142000d41c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 151407742 1250 151406492 151406501
    0x703051332060105030c04020a0c060c02070e04110a1401050a030515040905100f060311010509040e0601060201020a1e14130f120201081e0109091419030212070305041a0706 76
    0x4540002e03010781d42c541424141050403207800c00f031240b03104000241c0c02d02c1cac101e040c61850580103580040c40350280300081c2e1030513140d0b4228503010480c42041104110200040c02c5100d8000e035220380c080c84c0d030386440d2041d507118041d03403a021030010300484030450b10a501042d889030300c0c1d039440800c0700841c80205040750501801902d46400210b01c1d0b5024980c5405421201081050308100692560b183c1d02c194846481185040000020340c42081d0307540c0d40c0000041f255030704140c0b1440e5950724400381c001e500c00900640071415000305900b80d541748050488a081e52500c0d145441e04243c908000f03242d001c801480301c94507150001144441e25506244007400c0c82012040714003419000141c1000c5005208107500d606900141040c11040c02c581030441c0c2c800e55000c40d0409152400740d200c4550080034240f41d1094888540280c0d0164046020250194080c5d850004c500308804061f80b18007400580400d20402003013000b200b40c0500e540104014040307140c103002e400d50390340d410741c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 151408992 1250 151407742 151407833
    0x80c032e03030207081b030304050111010b090123010302071709060c060705180d0507050402030a0b091302150a0c08070f0206070303150906081518061e07030513 71
    0x1a030000b0801d018041c0200103001c1180a075100c0010310951b1134001940d20301c40c60003202d0410910071413503a0b031034800350008155103800404234401580c5070171400046010188000340042c4124a028109500034403c49400b503401c009120100000b105001c500c03507104050b60380c0c0101c4204080c0e0000d200c01d10545016180c07075540c03a5a00c018203809442c488407001032031441071500514080006100182110885006403009030710f036a40c8441d900001c00b00c24120302e4108802104100c102c0050040400100f48204ca001000d860040156070041c001c07071602401141c504900d07000410b414502030801288907024240104440381c3c08540c4942003030800700c010036120115220203c00108020003d402c0c5507008106c05803a0031a2560341c1c02c100f0404001030340340c2e00c0101b581480c9400103c501c03100b94808485043c181410440e806079115480c0810904501c00460001440b900403113020784080f00303016000c0f10150315000002052680f203003808886040303c039841c0703c010034a0a10078 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 151410242 1250 151408992 151408997
    0x3070c050102070b0a021f18050c180412110111040b070c17070b0705031308030705060603011a01030f06090509010e07050306040b220b0c07060c080c032e0303 70
    0x44034a00000a072801c052030f00925040c1200340401c401c2d09600064040c071505503481c280c1d2604003841c04080003045c0c520a884130130701c000c404110501c000054050700f030010541c1e0044c1c074609405d90700050000192402090f84030905401181a4403485024124813050000051881e009011740d800b0366109030b20080113440c0103e02c0301c00b40710b60101c00000401040194040141e24900000d03207035103c41c01110148840418442d040c07200400c16240504e1200042c1070440d501c1c2c44170f80d6902d4200c0c0e1070403110741c070403440000e00341e05060181c94010042039204000d607003120001900640016090400020341e142000600d6004da0700a440c0074020711000018080d080820b81d0741841080d0700304600030b5114905001c00241c08070305480d48046451401e00b07500c4040344000c502c8080e0600040c29203010441400b00c1080c9070320040003541d2207008204801c01440302c042e14400411207450040076824000910b252611558101c1040703100030351309042501c80300140020058a8005400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 151411492 1250 151410242 151410263
    0x12030c0f07090e0c01050304080c0727060608071b0822080c0109031103010e120309100e030d090813092909040803060102070302090405030a09060203190e010c06050f041101051206040b01110307 85
    0x90b018ce44002030380b030450581078140155400c1100142c82448094040360401139248240712a4006115030300d802c2d5544401d080e40d0302c3c011401414210069410030925031203170360358006442c8100080621002c50103031505000c1030300d962184008451381030001505035498407070000305a0400c6c091a000b0640c0320961585904041c8016440d01c441c03101c00782c800300e00c1c00d102850130782c0000003134600d080702c001000303d04840e941c42c0a103840c0c0940e40e040c03026940d1a40c0049860491900400300001211132507186000c262408403190f8500740070b03000d400c13403070000120380490000300065074468010300444050598980c041048040119015101a0004a2000d403000d51100e860b9009042c184025400c00240c6000084842d04041c0c60400344902503880200590180b16504a40d80d0000d0042006151041164410300d004440c00ca8085c041c1c0040144650300640c140c40b01c403140c2c02405c9050381da0306018440100890001941231080351107141c03a00890800081c903500303110b9007103c1d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 151412742 1250 151411492 151411529
    0x210d051003200108010b09010203040807120611070209040f0501110703110d030c09060f030b12030a080106051314041d030408060606032412030c0f07090e0c01050304080c07 76
    0x144024005050950000c404900d40c80b020381e4452402c43c15115407950359541c07904040b006074514895680803e2280c0182000004d42c150340c284c005000c0b03800355400740700c21100a01e15201e00e01c01c80c40c0003540301881d0030100b000300300300f02020000301d8841c1c40005a182121242c6100303580006208070f002946402c011000c0f041c09104070076a01c00b0900b02440400c49600001d070804c0582d0207040c04202d852a850304010b842078104030800d14000d090305412001040780030343c80e0340c007062600380403c3d40d42c0d00000d01580705500b100e003000104041d4900c1c0c1801d02102120f0400800881c0790711680f6100006004111140c4084021454500070b61362145006011810100000d0040348507400c28020003400580019461b00c80c15502c81c0104014514680042c2c21141c044e00c002420344070200d014140200c0c005074040010070b150041b034502070f664041c0c40741078950240003245103820502c2c0b0b05126502910245402500c52410706081480c4d1350402c9150440329841180c10050440514 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 151413992 1250 151412742 151412753
    0x50309010605042c030a091a09040501030c0306140108070909061103010621020c0604020904031110020d0e01090206090f010210110d05070201050f18030c10020d0b01020a05210d051003 81
    0xc10f8840020051801c081110720007400c025420300c2923011400f102c2c2d00b26145600d9400441c0d801c0c540c014400c0040356101d060029800c04113000880e9154034041041204440303001c1d66078101c803500c00040214506045c010f4006d0b0105e80d40454070592210010a001035485000d903018090541c2c600b5801d28161254806854800700c1041c01c4074410415003104d80c0004c0707011a8016016202c50310591100e2504403040448040000c109020f0390300c095100c540550020940207228a1061100b0044201c00c0e900300c80500600940c05801040000c2090a04411020500704c050060720b88034401c00040c28103448030b0300c0d010540401c0c0003401d0418540644502d94014913503100812443c41c11060017144000c000c3d0031048507451908034261006810006c40d05552035a1040d10071011294602801030742248004207021800e26080191651001880c0a03508d6008001081c280e4a4160b4035076203500c00c580b03440b03c554070801551500d03055a000e02e80c00303800c0e03020305030642c1d5141d410034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 151415242 1250 151413992 151414061
    0x12040302070e01083703030e0d0212030105190b0a09051302090f040519020d0623090f06031606080406150f0314010b0307080d080903040b0a05030901060504 69
    0x1418810b010320005003c0d441c400030300d1076000e444180301082000c0c5100c0075030016050f070030400c088400c4007400410806d54160004040c0d170402008440036105005026a00c41e050703850f0341440740c90103200401892038603e00c001c455070318207404031100d55103400ca031000540c80048240d0200c1c9400c08108080d04040c080021285101581103080070040c1f0001500c0d0103011041d41d1080c5c0d00c58011175122140c0c25284c090540380803c045645003200340003800580518400c103c44001c1610740d0048110740b40061104180c03009000c4901a99120085a00e264000e00b031581c0521500e920081100c0c07190140d0409400d4540b560165807406260980540e1a028120748041031a50001c0144c00107415414003500d501010240201007890340d064014108491090340c90f10a900c0700041d414804103040361a001c80d561040340e1592803e283d69900d04c10780c4981c20340c032a4200440f000c070368401c0b0f02964012000c50000f05883d40e4500014098132a000c14004405541c8a8503c6140c003030800d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 151416492 1250 151415242 151415249
    0xb09030408281101032408011104080618010612030c051b030d0311221d0403020309040e030d0906020306030d0903020a09091505010e040201111615050f1204030207 72
    0x3110150001224a9458040316554004084510070700390f01507240c0c0aa0010041d241101c0002070b401c140e000c1002c03a6050302e500c030f1152036500e40728005492060308022601520070000007086c40d03803151158050514184048401ca03550381b40c130003040400e207442800001d64004d0741c039001028882c0c1004c07800c0c080f00c0d0104000c1c4178240301150f011601c3c08152020318010a00380002c003601d803525458101d00c5848020910f0071120780440e41400091944602035604004404452100d400f550241c80c800649000e03015178000e0015080701d1400381c000a02c10813040c02503e040160211202e0140e44507614120303006900032040060b1030404202c9841c80d42e4407490568203561554012840c0f600581c02000a42600c8954400a21484d5081d0080d0720510000410a6681d1035030704000490040e10105e00003801c00039450310041001503a20000d9281113044805107282c000720f4844040045143c10038040140f0280204010510250401e207004000003001031409142c0281440010b82 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 151417742 1250 151416492 151416523
    0xf06060305130201050a0e090a091703040b04080d020904020c0a030e01140d0510170a0302010605040e030328020d0504211e03060f060f1404210206070b09030408 71
    0x301002403101da507810110b207041e02800c0c400e980308080c900c200c0c0c201c0104125940c00c41913400c2480410805580700b41420380c01902001c4640840e040042c1c3d0620040e90090702030040039000c1f6001c507602d1401001c40000031240185132880700e030080341c181d80100e805c0d091a608107c08920915404c0310030340c182040c09182c4807040c3c81d83c400d503400d0340d401048050450f107503486002600317000121060034060841d082000c404d402c0781c40344a40e9203136074440c0c0440040d400c081c40041c05c0d042501820385c50f108424091402d550303c4d007158600d500c1c21421030100d0f1a81c00011001066268401009468410003002c21a442c02e070800c543c8a0050f000f071000401342c1c105042c01c245621a1f8159000d44e10b001d60381ca4404003050044010741040d4000140c83c200c085070000b46c1c50b4210704580500c51140d11060211849103032900c205d0b0103140b040708401c1e0b44241d4800d010703c5600454445891000700b0301c0341803030103640320801c008900b00c0d6403104603400090140b10b409820031000d298030701100c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 151418992 1250 151417742 151417751
    0xe0301061512051003080f03220309090b0310061202031908030f04110907030e060601020c010503010501030b15070807021c12080a0f0c030b1e06120c120a0f060603 72
    0x14001040a0002001e5a02d00caa0b294081004940005103000086811560312602c2d98111a141c03030403a8002e0b959142c8400c0920f018500d03000088280050145d05030701c440c06903034642502200039296401a079981030051000c1c8801c0c0303402c6481104040d10001c10218042c450520500d85008020304e00c90b0500c00700680d040000031403034000c50741d000000f607038154225115490080511a8000c620320b503c0030720700d82004143d0b540759000511000c10401103960030307240d850059890b942054074040c0041c008000500c502d5019400404900c0c4010340040c00d10000741c0340490080c1c000032011200103c001075010b056107050031440c500b1050b03113000d4021161944ea00c031514274022090080c28003030b03041c00246002c20309a014000c1c140c0170042c00c4c03210f00d100010040c000d0070040c1c1d4540c0718000c03510841080b404103960002c4081d00160405241c2b4407850140b100320302009200c0380100408200450040386c080b10754274010080780102089680c03a0a1411098484a802840401d03250 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 151420242 1250 151418992 151419029
    0x3010506030a091e0303090b010e06030a060b03030403080711270114010507051b0102120a0e040906060807060305010f05040b13050702070510050301080601080d140a03021204030e030106 82
    0x51038110381e0410829400000c1041c070b9890702d001c0d038049000c500300300a40382104a20500d501a000000068411a4080000d0380c8442c0850b00031035042e601c00e0741580c42440302000244941d40f2031b010041b8010300302e03410716a0340e40d6500b425500c20001114000400b0000b030f4070505003036840100c1078410803141405444202140e4008090503c40c0403010a15150922030990040302111003480d080303004e032a1030355082c0704107451101c0e10760700c4070b0700504c5480280028500303141c0136600f03403211540d1990f8001120b0000c00015002100e400c0ea02d555990134002600070042019100070a195240800c2a6140080c070550406941c6e1103203004505140d400310456903034020402c41418094000203072525440b90483c030f80812b64000caa00300101c0c00d1240602c5400030055412600f84108803503140e03803600121a228600169180d0205003242007000c2a13140700301c0a040b110035545001810200b420310400030355081920160080303203400e04001c1c41c5003420302880d03014040c4540d601441461 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 151421492 1250 151420242 151420249
    0x1050402040305101505041109100807020c09061309050d0311040f0b03071202183d02030d1401150207080d050f0906030906070f0e0105070212030c0f0120030105 71
    0x90302003030703d42c04c660798141800c0c0c861000ca03042400b600015104103d0880b000181c4403655001c40100c40c8114403100b40002100e1185a07461b20a60195029100f00301c404420700c01950000f81c40c0507402164000e034a81c9240d82d500c60700001c240100300130310501001042c0501114809419000c0051080100f401130042c4050004e04440601c0245503a90350340f0070b001c89654032019540c484081c0002002102114901c62201014100301d0b000c94054442d44a0400c100305005120101c4a44150610448442e00c601000b810080303401541c2c64942c054542c0c80460703413040010000580c5800040c010311101070b54840901506000400182c1e05000c0c5039940c0306480c40216040080004001d1560a0380400340d808048004d0109621f9042026005450f401c0441d4007000040150080f262482d21600e0080381200040c1c540900c1c00c00345400340600d041485004061902c0704000c4270300020420481400036040d41300001403c8031183c03141e0f5071003c03210035103918030420030f2005110558 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 151422742 1250 151421492 151421503
    0x17010609031a060301200418021e03040203160303020604120309111002210405120303011a03040602070f030e04051f090c020f0a060b0907090602100c11070305030d0501050402040305 80
    0x418040780c4282e9610a400640500280083c80c02079440d001c80b00005046220042c03c00e4403501c1d481d601080e80386401410413405500c1d2a01100c0301000108001038910000541d000390015040d02d50300c4801c04005000c6801903401203006a11940c2084103006400901c83c5c01d080440c90700740280345068803444819081c1c1146a031080300540d000c1c5108900030084070013071241d02045041030040541520900303400a2180c80d00506004119000d640004001c5905a40c000001ca40c0c00516440240030160001031040f100c031a07080207400042071030007080c6a0101e1080d42c80081d4807403a02d083c0000d03541c000c1d00301c4916101c41440501110b40d044504410744403800030000381650300d0003049140103000d0000b202c150081f02e0008040c01020307003111008901c1601c01542e65290f084088079800c846206075401604225065800801d1f560440c8a00b001c4502e001c3c40c002000c55103040c1001c40c80e030302c00c0751075500c00076090005502c103006290040c90100d50440c2020301d552221031300d42 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 151423992 1250 151422742 151422773
    0x30c0506161202071508010f06050c03071b0b0d0b030c03010e070506070204110f1801020c151308100c0305010905101e08010609020a0e040b0105220806071701060903 73
    0x100c034948000c015040c0f00b003100030014140750308010381d804043c8602616502007806080c02402c1002c001040490182c000c440701003480707070000c61508116440302510403c14035400d9401c844221400118880c0307000180661003807a0900160003000e01e000c04d4078181050b191907010341d040001d050401000400c099040703036006c0d0b4105554884503c0002c3c000c02030170b5903907800c099010840c0c00c801e04001000c1c0c410803005000742c21100d07202600590780e4040344404035900003902401d194130301d480c08010313004003c028030156000c9034840d503200342840510310700c3c030010940c1c03244031980590381405101d0051200c00820003050504100c0c003440b0141c030b07000d00300d0340d90441300020000308810320038603000f0002d140080282c1600c801700f14019520600700c040021b103e00e01e14110614244c85609000d0740161070f594a00100282040701d840c44480c0c81d00a4a0034240d400208020148210382c46100c00c0c1c0e541c682e035442034500003002d554040e0000c50801140c0d03a402e1001a1118401d03c207039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 151425242 1250 151423992 151424003
    0xa03240b03070f0e04050a05010806070305040506160c0506040803220f0201050310090608060406050708101503020408011e1b17042d0501060b1c0504020301140c0301030c050616 78
    0x94150341a01350349120080c4030303da41281c034100030420041041e82c8402d050328044070958041d52600c180c100e0584000341c40103055500150042054141100c954030700304c549609040e162121103481d07644c10800200c1d03081c0c546001c00002c0041c08c0b00c11280e2031030890081004c84006030b155440c0c451443d4480c0500a060105c0000070401c0b41c01e281038148000c180c01e090510810340c942d01c002ea100c0000ba24200c0d000d0381001c01003844140950f8030107100e56440380b1803c40551070101d40f000242000380c8075806040c0d0820001c9905d54003030003011180c0080703c16641c0381c22045407003041198003554441000d07443c4a5240c090280c1c1c050b02e4007401d80c003e040d1020325520346007059241040b80c40780042c101c2c2d501c20445004030704812000800c080c040e000800280d07607109000d410b00c0c030444a1422001222240144a05030158040e9800600280001a0124004110071007440c410b50b011007114602000410030428031070f5000c80584401d43e01d05083c0710008061140d00644007800819 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 151426492 1250 151425242 151425257
    0x4060b152b0e0d02010207050c0105190c0602270f030a0b010b071e030c03090e10171504030c110607021c1115040603180209010308130b0a03240b0307 66
    0x641d201d508084501c03040325090310380748921504064003d5216850840361800303031044240a541c01f0754141c80e1100e854080209581680c0d1008450840b5008011100c2a60034082ea6a4200c0340303100542c0340c038416000041c220100d940400950b84240034180e44690700c1019580005116a101a8111828034220986407415803600754141e08440e8000c040c5034070b101c0100004e1507441044050018000c0e03c41240307030380c0c0301c54000d8240f200440744e401103401e2003001004071864001c035101203203020300705903240031140380d440502403142030790107800080c1804003900034000c0b8541d05c003046480c12209e40b440d00d0181d41c01300300c0e81940401c140720303103003851440320092050700c40b02d4045002004008296001c0c1c41d000d008045d42060096000007413a000c42c0c02120401c1d60344070500143c004180c84a281c2ca10340c1e860480344d1083c00441e20844035814000341c201c0500380a8520b42280351008035565025407201115110b440c500660860010041048560300c2c000460781c102e01c55152180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 151427742 1250 151426492 151426567
    0x120507081b090907031a0f0604090308070c050a02091608011409150102031905030108010e060112060c180b12090c011e05090a03060506030105070f1e0e030604060b15 73
    0x6003040e844da48050811100d65040d80d18000c01181c0e40d0380301d0a020390321003400761656020b0004071400d48400a0118000303070003062005000d0b0000d07034070161298040b580100103680c00300b90b10880c2a00c103000d548803900000914180c01c402010b0142c4030842d085c50410844400040754850042d2004d45502000f104004040e48207004079442040501c030b090380900f04d8280020020340c024815140035510f45204107502041c0410030a04035400242c40e10741041c0d03241c840e00001e1280ca140c54040c40700102085000b240301a03141c400400300b00f45000c0d2145121a51055680e80c02010809150040d0708125120380e001391f01c14609032410f40c1445000e004180f0143c646100301800c081e4803040d0704100204014603a0050346c440c95045d402030040d6120312806641d45c40c24015a0700c003044020844044901d0343c485030310142d1685180c0005401000c2021904090701654107613143ca03151080503400e07042071000d24a0364111020340030302d01a0441c01c01e405054448003009040038021500301e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 151428992 1250 151427742 151427761
    0x601090305030a0e030c010c080904021614010b10080105060a1d121006080724140f0a0306060504050604030b130203010e06010305070f0b030105040e0a0606120507081b09 75
    0x8014550180882e50341e00d00b060005083ca9280e880383c940302c0e00c19024a500c0c1544150410b0301d8003548512918107100350317038080001940003002c4110201c4900e9210300e0205111041081035401d908000280c1501c084082c00401c03202c104180d1300f80881c41c801040316442e80c0003256a58001450101c074110050744114440382d51100d80143d00c07070504140034800340700103c1c44841c10348440ca0100000c0b50b07542919502d40035a44a0019100c3c4416460010180d0803c4068011003561800562072008100f1190843d04002c3c140c1103490300101b100161990548100c101030035440c00d01c1800c0615100008503144900d020042c400000d00b80490584004c1c00d29400d40030754014028000341041c040c4455a8a0007480252158440c0750030001c3c40e403502e00780480c00e8a9403108000d146038202001d201c090031384400382001500c61441c1d1000414003522410024086ca100129024203007401c00c0380c6003500701c1e041340c50b090b0003060076010744100f0b8100155000f6025150107032240e070f510020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 151430242 1250 151428992 151429007
    0xc0309052115010503121e0d020705060f0415091112010c09091a0d08070c030507090c14030103140307050d0906030c020c10050d020f0711010305090d0807080601 71
    0xd550000d540e24800c2000c212941550340c00010391208440d8000c03440000300a00c00070a100782030301030b04215001580400c441c4020050264410300c000d604030070346a2a6481c9600000012085990128030842005000d0100c0c64002c0800f2003486024200b6031195801400c900702d01d040d1a0795218031300305c10440c5190824034407000084c009030801c448812a24068492031080c800000d140b514040303000c2004d031180704000804004080361600d00407080c0300c0540382440f42994480800e0140c0300001e4a030103003040241d4803070805419035918203200c80085d500340707000f10014000c0c511280240d4010304811b0701d04603030b00a01c02ca1749000480d00340d14114402d12001400312700421204001c481c0c0c02c8080c15045900a507000c00c440700785100204d88030788a00c20300c1c651000000500407072191007803015002210040304010f1510481000640340c6901800b412130b403544070b0120310600b568040c89413680c0070358554044d0290403030401c0000c1000d44010024818004820041011030b4401c2d02c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 151431492 1250 151430242 151430249
    0x31802030303010e060111070303080f07050405040504150b0a0b030a0b01140d0e1504020603240402070609060f0e03070b0a0b0402031f090c051c0b10180905060609010c0309 76
    0x141c07580e9584416454241200480d801d40c013140c4150380003541040700086000881e50156104110391b2104640c544407118003074455001c1203010b22001c41d40da502e610a442c0500d1080800034500304c80414040207071901d0710495441108152002c020030041101240c2d0312894114000030703030305c9250b00103a404000b410366444800340c011074442c074840f0403036100009402c0e6040895030460382800e4128001c41044030029003015061000c2410354100804140041e0040350542c80e00041a0001c074089030841d4800303a60140d112a0a04288002445422004d41c4168028041c0c100b02c503040350b50301e03c5220401004045818005056131040360710240d030348100100107641d2814120446101c583c0703500740e0b40e402c2c0c0c14008000901e03105140306003484d66060b41c42d024240440145202c00300c60902d007030328452944034540503985684003041d141301c607141e076120402260005c642a51000800d034000088441c45c00d802e0103440d90300d003003d490101c0400d203030925000304540380071100c05a2550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 151432742 1250 151431492 151431499
    0x2041a0604171c0c060f291503070f0801050f0f010c11061b0d110c01031505040c050406021c0926010603210302070b0103020910330201020306010f031802 68
    0x1481d0a4000341c4c0400068000e41c040c07402400003960103c40340301103e640c20090351707541c1d0103040c4603180d6548001c00900c00140051241900301d0000c42102e51f19441140c1d54030004010032600700c0f00e590844c5116000d08419107110f002c0b102424089001031100b814414148003808000400300728a0f02c86040380034601a0510781c483c045443da400c1c0c0c84440c9021101180a8046041c0307145100d25644070306076403107030000c00c40f0804000040d40200341c0040a1448000440380100b05902c6a0040d80359010041c2d440b183e45500e0000024100381a1001c00080c1105200545074083d600c4441c2c1c3c810f0720b05e07555500b0320305d50200911000c90490700e00c030801c52354207004d07000040c00908091188043c800783c00b400c12405010314100e040b4410f4050041000c0204070041c4003604106d050540c0c490904411400d40c50707215010b51441d07028141d40340c05d69200002c000d009000c038220580414001e10b00095086050103000684100302c521901c3c0c0c06c06554001d801c80d6103d00080703e200068019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 151433992 1250 151432742 151432783
    0xe0a060e07082401052707020f011401090e0607050d3206030106050f030a08030414060a0b0112110a0e0102070519030605061912030207030605011202041a060417 71
    0x604208100714078035100529100c680740000500b03810a11400140c1922200309886d0407001d6044a01d031608016044400714030681c840410b00c00400d200359940c0c9001484122015854503071031105607103034643c590106402600174400f4198102064903480d40c0314607004268820809809500001c03e00b0505c42c680852017400714281c1240c4d0107840c090300081c0e0081c0032194554042c0315071031440342a0250076600c0540300c980402c82c244040d6030031510500d682088d440c0d440300c54a1402c1802c1c5c0c0c2c203000d103c2d51044a800c60790380101c031011200801120604c091118012225a14081c442261040c007020715000b1310309030300c00d006c2c1101410b401806841c12601e00c01c1300c000070030100d0108031000d600d40000b00341e2625180703020000700311040c1c40c454102c40c01c020b41c049503900c130101c0440035445903d80100019005000325800f030b14280d0f2640f2100c00c01801040700782c4203d00031788501445e0130031411041c1d8a030b440484060b10017040200144e658200c8800d0b18104451401c00c0822245 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 151435242 1250 151433992 151434013
    0x40534140a05070606080705060a0c060212010b0406080901090308150a091b0908071202060d2a031b09060f090e0901020903070902030c0409090f050a060c11010e0a060e0708 76
    0x2c00041d042c542c3c00744408012041c3c680b841203503075881c540a02c950044050003072a09552090b545582080d100e0701015085c42d007910b8a048045000380c01414086034089020310000340e0201c1d400e83c1c0301501d4002484035482035107001d404440c010b80705c0d40c481802c1217050704013910742d11061170040844140421403103413440c030024180078962110200082545000080262000540130180c0f1998a076180c0040115420031043e0b030303c9214141c00c1d01e52aa100000e091304a18400914000c162084d6410003103007150041c202c44482c4600341c08400c420f14211013443e481b8044006641260808054081c0200b9003540c0c481e20562140082c5031048040000bc218103401500460710160111440c3c217454003041000d034081124810003030b00d01030004000d92041c5401107a03415014803102402038150752240c0b03052640c00c400a50f2400d0701d0301b007840c0750150b008160510200800000308000c0500c07840041c2c03a42c881c200c3c05064580c0b101d1031400c20b09001c0c07012600034034100c812100d020f4a03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 151436492 1250 151435242 151435247
    0xf0302010606021506060a0302030603160b2a1203060312070f05060601080108030f030618070207050f0d020604051e0a061205180c0d05010623040534140a 68
    0x98001c82c0d0050241c03184859111000202803401000014112414100f8600d0220003d402c01407420380c1c94030602c018030080203900c0c82e00402620031214402d607076131084001076030200c89403412074000c4883c4d4202080784d00e0303000c1400d5450b2100b0707498041c0d80b6215070000a282c000c0c0405502603c0f400018100204084403054200c101d100e601038034019943d481c01902c1e003880900c02c0e12002e030401c0001c814010303c000003c5501c0340000346141c55200e07206018101c05002201c1d0000580e0144d10103100c01c2c50942000359503030b4011210782c100711609a01103061405144178403809080c1101812140c01c143d40c405900021029041c0406a03079181002028034010015140b40c0b00e00d42804540954402c100441c003005076100201410301604051006514a00800b504c181d56250780126400100c2c03507500e0b00300c0c901e0403821a1000421810041151400303000c0781c145140744040d03011500081440c40c0303406490300e20101882c0301840700944403510b25620704201084000381080c01140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 151437742 1250 151436492 151436501
    0x308040302100e1b0907091e030b0115020c0f03030906070c0504051e091b010804061b0201021b0a0b0403050d02070b01030b1f05060f0d0e070305010b180106091703070f030201 77
    0x200d0003600c00c040342c04142c0c244442108103442c07410010b85080e00c14045413003d4030b00071100f02390711070440b03e03416581e0b101c0f0795400320203800c000c144186948042180329410890a020314408403402284920400c0000366a071180b43c0b40c0034059a00460781c0300c02d00607020f481e10010030010f4801d100c0c41c5000440a028070111406c2c2c1101600d214001c54128840003602c1980750000c0845a1a0f1007001001550710140c000d004407015600c0c0c04492442400e4842034012041d41a00050384030f04d2603030000c0c84007500f5a0b4201603160f100c1c0c040c00001c102c0903a20260802c3c0c0608080e41d48140b00c0714408040e1184800251001055000001c01c004039241313081d2060b0f04000030310b40510350002c4490b0090b00700e03214840e0700c608103004141c140f01d8507000400d2807130120381001503400d10790181c0320b09001c8143c1c0250346a9555650196050401100014682070824982e94030380d03041000181c19040c4034014001100300307854030164040f00401c11108604e802090451085400b40b400070302a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 151438848 1106 151437742 151437763
    0x9040b0f0a1509080f0d0503130506010305030901120902011205060102010e06011d010602030a140702040b06160c05040603020310091a040302100b011b0308040302100e 74
    0x140d403001c1d06803004003110489000759250b070100280012400340d1000c641500701020890043c840400c5210b04c0204a05100c0d03107945896581c04201c801000c00200640b050350004400d0000010162041d1082641c80810342410701c0300700025a844608000e0200f82d015150040c0c5104d00e0300056407000044c400002e03031403100c10f602440d141d000c1c0e206032000801ca09680c9003401d940b94a8a0262400380019071034291540c0005000d40f0080078448400f075404120b8a00319076864011802d5148000e101680b91002050440c80015184100710b407803601081c400a002d0501e802204101c90f0010060201c000112940001521140c82c088444403031584010701c180c21060fa070a4001c1d40281d00401d5208142d540d81e1046800c1084000c1c188150006130001c1900b1000222a101d9030500c0c4c00308007511189070681c58015510210140740d03003041d0021101c5100002e01042e007 = true := by decide +kernel

theorem cover : BRFrame.Cov 151258992 151438848 := by
  have h0 := BRFrame.cov_init 151258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 151258992 ≤ n) (h2 : n < 151438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
