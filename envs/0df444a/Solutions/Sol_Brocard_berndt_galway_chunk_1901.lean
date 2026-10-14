-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1901
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:05:10.782061+00:00
-- url     : https://prove2.me/submissions/e43ad212-2bf5-4cf2-83f6-055e8c6964f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 341726618 ≤ n < 341906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 341727868 1250 341726618 341726653
    0xf090209010b0c0c120a060204230f0a0b0c10060b040320060d0903051608030105042012221a010603051009020a0302040f0803070201030b011d0d0c120311060105040c02 74
    0x4905064070142c0d982e0181b550307292001c0e030340503500400d80c0b441303d8010758941c98000c03200e1102101381201c1e043c03240302d88103002c184c2074211813290404600c8041000c05e443c510501ca0b0400c2d008000008104c0c180c0c8078420504650130500060700c10791040100c4c43c0300000c2012604501e08002400103061204001e007000107841c14020072001c1003401d000362171071031302c00c07240140303445205550880d1258100401d100842d5100c0500304882d6840c50100c54112421301c1c201e4840e400101c0698056540351b0190702600c0c00c00891080984119442d02e00501c600d1041c003000070741c2e80c1c0c001c1d40b8250766200700880a03070310184c8002c1010082240200200708060340240410461402c016081907950100345c803071411590f02291040d0000560b00e000c542e8184200f0318144c8003400c00040d01400c08080d401075401030003495003e01224042c02c0144651611684020061000c00c00c02200c2580340050180301d001032080d640d44270309000402e42c1e1400e4040c801d1f82d03804c40d50080181650a205808 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 341729118 1250 341727868 341727889
    0x20d0203030f01031e0b0a0902040b03070f0e0402060906031504180b0f0a110d06080c0319060513060e01020a0f080c0a031a120604120c170d0f0f090209010b0c0c 71
    0x202800030075040c032030000c0d01c07407103580c0d107d0350502a0000d0044100d00500064800340d0502c00d1080d040b003c014800141c048282500340d4086100d50000303641d452001c07403080d100310000b15074030400120420a22011071060b01920000030390301400300000c800d468100140a102000b0030000400300014076802d220840154081c4100c900410007980c0604081c460354003d000c0e400545031030320400d200e4440104900400c6000c294020045040106130741d010782c48081c88010071480d1984c0c0842d510040b0030b070315104042e401483c204881c0218000040c000d42c48545680045541044108209409102e0301845218442006850922284001c500034a800308550a000481c1b52005030a0345030160b010100c0000c60b40100b0741d0741030034100740300c00c000c0c040e02001c204440b111701c120000f070301c40e08000007652045140648400d0305252140c040c14a9640941d501d91400b00782100c0321440c0d410166505002b0340d082c42070b50742c90700d4900b110347c4075031621083c841c4d000d064490143e00f00402e042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 341730368 1250 341729118 341729153
    0x60c0a050a0905040c050702090108030a021f0b040609020d0e01051b0702041d0a03170103050c0114120c0a0f0216060c1505070e270c03060103020708120106020d0203030f0103 77
    0x6181c8961110001340888000354441000030314007103001e008505141900c03d001d4107903503008500f03160703104c400203544910701007050700501c920041902c0d10422903004210072020040080c00f9043e15019040c0003034011041d0088020b080021070b03400c202e4180326a50040c01140e6890450f0b030100c0402400503409104100c0c0c210b592184216030014480814020036402440600409451814002c1070540e0400100306030310b007150010400200001a070742000b080c282089101c1d941b15041c400b0090048644180c0800484000c00842d00c41d0613004000301444c80d12040d8010741d1045040341d69010150101e80d40802d09042444900d00540003203000340c4c802c0c0c202c46844d4808600d20002d60301c1c02d0702e242000c00c1c0d05081c010254580380b52014000d030410503090101001480a403c101c140c09001c060120b13100102140860b4401c2e01100c044582150545641e420314a8000b80c581f4802d20a8400600411002885407480441100d018002410303158101d40d0a640f00c6861005150504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 341731618 1250 341730368 341730377
    0x24180f02060c0a0606030f050105090f03030f07030608010213030c1a030f10050d0501050603060c0f1909150e04050c070c030809030c0d0506090d090609090213080715030e060c0a050a 80
    0x2203000400034045c10000c0e41c0304031400c1800c40d485240103800d48001034007409554004400d10030140d0781c000b05807a0b0141c0039620540e42511100c90960040005030400840e0b03500008680688101c800303030204c01c4034030902e030050002e81e841580c88103401354084c044e2200482040440c0441443d54004d03a0801c00d914000000640d841c03002800380c3d80340e51012603079a511001080300d10310b01407148c0e45e40b0030340441c0924a0b185943d4407806c0b1621480720350100140c2385402d4440c023140f180384034a000e090f0340b2900c848120185a0007401d000008a100c601c0b490800f0001581c00d0110ba0945401a6000c40070009403401e5a941349000d8005144854244c4a4050401c070a0340c5d8552120f0003981c004e0002c0d0005080c810340d0700d82052007203a5040d041c825103460030041c0710f610400f4071040b10070135000140c46007101e818203000016554020410f42c4924003002c10740c4422807922826000d11900e04015480a450510351541e02c22540444a018140710b410f005600400007040d204115107031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 341732868 1250 341731618 341731633
    0x903040602101d070e0103150908030c0a02011b0302070c0b090303040302010c0602220905090606010f0318021203030f130b011202010c140304090c08010305121624180f02060c 77
    0x82c0f43c0b902c691540328900d038a1040e40100140b210041500350018401e0318144090300d260340300c6c00e02911015103c606101b000040031003000e4403c2d489030b40710201025841d640b060040000901a41150030195203451b042040010031281190807520401409400b4606003031442d001940d08000c1070340140d850303540070004200041040324410ba0341d0032406910b204110305210421040340d1000b03102d121598000c0c0e0600000d43c0c1c0041c0c1820079071070189004503000403500c28080744504c010750002d402038130101c440001203801001441c46182502c400c9641b40d43c034a1049142c081503110007400580d00e050041c081c0a10114070744041e50b0043c18001c40820181d5a040c2581c02b00d0074982889800201d8140f11400c2d080c000c4001c1d020203403610044950464841580700c00006100303041c2c100002030300d8480340302c403034130942e4101d50000005c24845454062880088441210381d04501c0d15118100d855038070744500035007503281c100c00310f494070741c0040d824000203074840354010845108916 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 341734118 1250 341732868 341732921
    0xd0807170c0703060c031e021803150105030d21050705041d040b01060509060d020703020c090901200325020111070503041e12080304081204030c0b090304060210 71
    0x10300d1030300189002050b48610b503050032403c0303c048090300020581011a1040c03501090144130300a45013035280140d2394070040100c040f441640b80e41a40c2c140c01045160f2041c030403182d0516048030400d80c01e440800b0240e8004550050b4020310601e0020054004a0b0700c1c00011750043c0c0d80a00c242c02c05615140c2c8a10803291070104c8681c095161000c5001044104207011480900404403400c2182c104600c020005195002e030002c2d446000c0c0c9c6c089a0601854420031004d040008007800d001d00904201260305d02030101c0d506458100034203d13100c00c0c17114864104503441142d00d110341040500d14040c2440040d001d4100d600115900c680300b0303610b04d03800400100300807445140259a00c0d441c0036117800c01c0032001c0c00b0005048003044070801c03424507151b1080319400d50014006580c0d03511850310403614007a4076102110b11500034104010950400031891b40d140c0510b81030882956042095940c0c0e204074000c1400580201c0d00c02206891540c111031042103854014085080062 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 341735368 1250 341734118 341734163
    0x1e120302062221030b0108010f030209090120180607030c0b1b030108072405040312050d090311191110030e060c1b030301030203030711030f1c021b0d0807 68
    0x110f1842c04070315214141400101d425114109101c1c40a0030706190941c07404001e0300364a071540c0b00180c0904034480020301c501d2420351203809e80150041703440810400b8505040841c2d00882421217a001005809007650724292056039410303a415580c420201c2ca490340d507400414005040b0011580d50009064059243c10010b14040d1212000910420f850b24110b220050542c208004030390380390002c85415990310200f00d40035a13070080900449280014406c5416104159044411528011442c0201644144c611f8a02c01340e000c2120058208070303440f03108842a00c6402068085032100d02c07102d5040402d20740c0d00180341ca003000030762201858040350821200701ca0200300020300042803050840404182d0000c183d2072130003142103604507804642e492280000286c00710769001e900d540179070b500f0000103080000e00010385416007002d41015908803e10510390015018080030306801120015600da00030380010b080d01c00011003616460f0507548100c40075601c401170541c1280144414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 341736618 1250 341735368 341735393
    0x14040b0304020607210509040b0105040e04081e0d0506040c2d02010b13091a150d112d0d03020c10021e07240807271e1203020622 57
    0x141e8030b07620340d106d03000e031f0402c4200d4020111140c184602400288610041152215405540310240c00d6440080300034002110392503401d5003200940004440104421907040180140c0c0c0584d41840111640b80d4142ca00001d22444100080c580b42c86080c0d00003c5500880f044011a000001d8500c1d0b100340803402c000d001040007c0b003103840d400c109003004501b01c407031220901c0388102889241070040c00b10003401e144881040c0300f864039541101c24450680307449185030f0b400900e4840e21208240c4110388042c8a82c91020504116240000250422581c0c443d5603d61507400342400c120248100a1040c0e00b10280c50700310700c02c9000e144c41e41c2000700c0c0000f214034030110050805600c4d14002066049160303965030103000f42ca4907030605080d046051907402485034141810943c046607459881c4130b4400b102c0c00151612400c00040d41c0c104178081d160070003034080c6030f10002c5450380410314002c02e00e44c000a0050303000e2000201b01c000c0c41e040300c007104800a50701c66501c8206460b0850711111 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 341737868 1250 341736618 341736683
    0x103060b0d051603090b040b040c0905090f010c05040501170c070b040305180a030308041401150f1703030105010c080721030c080714030a0c03020c0d0504030314040b0304020607 78
    0x15520148500c0ba180e40c103401d03c1d01c07600e615052151040079a070322401d0400240008180c1f01040300405e0404c03c118035070001501c01c0550401551505c05180b640d80c41800300d04140952070081240a0103104030126419914103841b00222400f0321903180c009014010301d030748003451040c0445030001d903107911000d000764001d65032161100302d4000c641c942015088007a51050946030801c00002e03800002e0942e1240c0c001090b140b51407455003d4601620100e03046051201c02c10101240741c64880e003407941507501041d13182d0300da8448444580e60340e01c001e000d25404117404030208800165800000c000b12803003215401c1303101045080c2031410707202444a0310003080d00e820305040c1a5902004150740440c007458103101629100440403047c0c44058680c0443c3c50701c90411020700c03400380d01104ea04c0c2c0503210840e4241da076018001401c0760410f000440005a96540070000101c24105a03410f682046c40b495146885580c208512980451406c4401d0381f444101200d1118120f20400b00c1c401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 341739118 1250 341737868 341737871
    0xc0d09080d0203010509070c052d0106030c14030106030c05121c02030306010815010e040e0f16050a1e091805150405070f120813050603090d020105070c0f0209060103060b0d 76
    0x1410002003000d51b2800418040030400c58180d91000700e500061110320703051070a0690069105c0310800394040c4021030510700c000e0360900d000041002000c1008604690010721032807207000c2803804145c2030b02c0e140d10010780f00c0c22017880c043c0b2041c5040020750000c034824600725100081c0701904204000c40100501015030404010040b9658100c9600d40e802201c0008c5150460031210019103a0442250024011561031419001503041080255103206a0100300e50b130030300405580019101c0c0310300549016544850001038400981c010b00183c001c1d100b52680d003030342d0900f1300b9074008019105441103c82c02c0d409400300840e00034405000b442c800c40c4200c00040c941400c0c59403818510364010512030031030030f904110351003003c0d02160445501078519507076100d2813402c2c3d5040500035040103500840000c24810132500000e1180c003103054580081c08136a0350301006503115140302c00060400304428442d03a00502c4d1510420f940b00c2c5050400040b0300b500e80c042000c1a0308000da074110f01e203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 341740368 1250 341739118 341739121
    0xc030609060a030203101a04060305010f0b10080c0903030715091403030702100509010204031217101a0d060801050702030406030e03280c060f02300c0d09080d0203 72
    0x141001030340154000710035a1148141403031503010a544084024107213114a50b10400d482c07002c10300740c0d01c1079490b4000510501c605030300e07824440c1c02854603840c0510845d00d1b001040400f8249103503011800503164440962695036009100c280b0352100c018180e060008010300c034002041c02c80f00041b404175681001030740a00a141c40091201d40900750030081c2d00030300400980e258001020360289800400200e5203885400502d07004e40180e03080107007003000340d0114041055002c0da90580d0045011501c1c1419111010703030180000e21800b8510b942d00144026101c12105800101840e200c46d4400240041e07503409002c0c2114015200400141c00c00103040142c90343c103002d150050448000a58586154a59440c10300281c841903501d044000318034411010340901408102190403c2d4244421114090f81030000d44c004002c0340001c41209403825041e000e0600242c1001d440900b54070b50325111650000b10a130815507042d55100d07100c941c00c40c00164001c0141c403046403e0000540c49 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 341741618 1250 341740368 341740381
    0x302070b01030b010825120302011803020120070b06040203061c080a0210060b0d1104210213020918280c110604050703170f12040302010b0301090506010905060a08060c03 75
    0x108030b45950301d010b140a4011401c884403207039041e280b040380c40c07015101f2010302852a00303034003422041c22070480c100185860401890b8040d0050071046080e25103500404104a00c1903c1038081c0c8400034042c40c0180c000164241016401140c20030380040c2000f49000c015042070300a001420310880d085000401c0000c440380d0100519008582e29040030301c0041c1c24114201c5031030040380215100c058807500c1c07252010a541c0c080b2005000c06400400d4000041441c08080c559504000c90240c000d00e82000c000c1039843c030035120900401401c101d0030b1404140c0c81c1a4a110181245202c4000b441325141c2c1c945156001d2424610305070400300b00a0710400f000fa03c0d5040c076005800d80da030070042c04c0100195000c11a201035a81c072036034901542021100c28401030040405000b09100000340c603407090003040803003500c10b510950003406158400000d05083c2d03910004002c1566202c1c00060080c810950480c550086020744251401135980c91003034a000e10a17520302c2c11000300003051110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 341742868 1250 341741618 341741623
    0x80406022b0b060702010c08091906050a020d111005060303040503010606030b040b030f070b1e0d1508010c090506250c03050606010206040209041509050f030405030615030604120302070b01030b0108 87
    0x8005500301c81c01130401c3e1040d0006048584500c000401500700000e0350030f1165505c82ca420303281901d482c0080b113103580700d44001d003555100b403100c0400f601c01c072a00001101e01c11500c80c6041003185001d0b042e0103100d403255a025000140203254940018040801c16031800d104040c010041c9a90200d408070f040018481168400014a400381d0040402100c08003070008910342100d66079100d850380c81e80e0403000c526031450300e840585043c010000d03248000903401e401410802c011100344c894101e0756208040e080350703070075000340b40401c4000c00100315501d0f100002c4e0521070f440c22801c0744101d80500005c88050f05403082191071424818050040c040e041010340d502c124280010301a600b01900004c80c1e40500601c020903c1c1c11550415204014640110541d690300c00210303090401d60780420360300c2ea003050007075600903c602000240000003a104040c1d10b42c0700034003d0015900c81d9104d4130107100030405040203040d002c10061000600b0b03840458025400303194043c1842d41802a03060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 341744118 1250 341742868 341742881
    0x4110d050633090319062901050a0203090415080d050906120402010e0a030c1a0711040c021f0221070f18090509030a090506120601080406022b 63
    0x1e000340b07500380c400d030000304101103031609003a0301181c144440420382c0d500101034400e00400942501440b43c01d40044041c940d800000b10f4495103051001c000301c4400d40804090401039415445c00062030100154001c40040040580510660746010b44010108068a0f0045140d812543d103004e0200500e58091203024520616480c149140c1541040058500d0045200e0803003400e20f40004070f000c583c0603602c0940350300380107001201119501d0828980b00c4a07144a056100501c2040403602140c1c00f80c2201e07035460303011140100d86810303d014080100002d4461100b54803683c000b82881d150303015074102c8640007041d0050380d1011440b10309080c4140054441d80c0507040d0100340000c403504448400800803040c50624004e8658140c480100344543d44841006880c1000f409428600400100301d0000760f6100d000c0a00d9484060101500c144104184428998404240650b114402407900f05002c0d032800741c2001d496550641050322a052185a200b1402c2c1481c030b810103c44c007514 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 341745368 1250 341744118 341744131
    0x1003060306060e061c0308041104020418140106172707082a090a09031e1206080303040b01061b021002030304150e190f0b01080d090f031e0501090204110d05 69
    0xd00c843d05d1581d4015100c000301400051104540c0c550421a9445540c1600c00030095080d01c145928035100701c007001005954501c00314002000000300d0314500445c0101490010414071009a55071040720010444101c1180c08120320400c440c03081f110070410201029140410160005281c02400c100e002000c80c16460400c191800c100c010b04d40e42c154040784c1c410680f90000c00c05100a1408440c13070400740e8401c0911450600b001c002e40c940c42480c0e01d0a024000f202007260343c0c0c880e40724039543e01007190000d00f105400740040c1b148a200d26000440d9101e0140d1220401d80e850340050800341c42c04605a00590010007000184682d2a03d18a0b066000d184100061116040741c41d4903000e0412182c0003070704600c2940400c12040b034070742c2041c1c1c6070440601c00c01940c448520750340316406400a2000240040c00124200035102c0e1403000b1a988107090101c0c0c04000340c050408407a2410040d1155580c1e090031602589170f0303004e02075030405c21441080d611212550b41034103c0c0c0c005000d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 341746618 1250 341745368 341745409
    0x4320a060f0f050409050a052e020405210c100302030403120608070501030207021801090501030203150c0d1e0e0708011512060b15041203110c0f1003060306060e06 72
    0xb0000c600b00158040d003035500680d004540c41d44141130503854051030603c010814801c44c0301540000c3c207440c0a0004158010343c0d80c1d036801d8980d59040050340603034041c482c5c0c04074812040b1001400c0600808007542040e0b001c1d04c40e00e00c04900043d01d005510b00038800440c0d0000100410164403500d2215420441c060400c00103041c5103007680c0d9034482e0700846040c5940000e022046d55124034122042400c1c403e50703240a0340e156145040505001e200880c040d106050849021611340002d00748544000038949043c00301010003200507000000036030880c150140d10f4140980303480c2c055009455069002060960315003820582100c038881070840710f81009140510081e92514400420950031030004500030702d20707000041e8a8422051300b120404400030f400036440381c115042d10714113406034988001038034000207496200c08580010070351101d0641071a99092904501851041403245400500d850300c81d654241280d0f1540c00c40f81100c0514810054035180102c5c0001071001a0f038030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 341747868 1250 341746618 341746649
    0xb07020f0718020f210906040b15120102070507060e27060616030e0a0504050118050405190302010b0310020f0412080712081f08030904320a06 63
    0x65181c45403520b0181c1c2901095002038021012078640503556a00c10701c000d42e40d50380c810310f55100030b84414440d5002001101100090305040c02242e1240b08a03002002c0c910582c0d220800703c031498003581030360703039014040d8102c240004509201526201d40710703900400e640fa0030528094822013144500c180301d07213600c0000c955228140490901e034842059050101512124001034139401149102c0ea03a0441c0000364800341a480382030030040c0c03075040e111400c0c159210030902c01a95400d0240c282d8140f5072420503000b4005552103994060701030310980704801c45052046400e1a152501900103079103810b10b50310603180c2441010280000e006086241003020002c0c0001030050303106420100e4200c001c00304c280001041160340d80c40c1c0c846d2540103844070140f806812100c00360740045d48c0b138603480a090300a02c900800301d030a5600e49001181060000010080500489505403080280001450301c0c542002c0c40140f0b01070fa640c540480040c60a0100603086856580c02080d0312070f0780c2c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 341749118 1250 341747868 341747893
    0x3050a03110d050f01140319020f030a03120501230f01021e012313020108070c0f03030e0c01020f030319020409060b0304050f0607170a02120709060e01020307080f2101030b040b0702 80
    0xf0b0100c0e18000e01d03403842c0c00c03910482e0000401254052b071441d6054041c4908400030903500040c0301c1c001e2480031208002d1642c8410082c2a0100351807506c20041c07520b040b40789481e00e070800094400300c80510449070307102141000041c1c490741d105105085a034450044510948988201902c50740304400a20300929084503040d0301d1000314107000e81489030460201e0001403050100400c119040190800b0310f03016494024010017141c0681103ea0188144108096102150032400720507604015411030302c90308400d00740c4107610a4480401c035820000000c4040282c01008014594070b52019124a0642807107818409621543d4a1035080b2008129110307400c81400c01d10300258412055103a0f40d421040002840703a90320441c0590f02d013904001d00e640c1e1107542e000a5407115a078200c511005000160307a203011b1420002c0210200b841354940744506107024100b00280304031030180c00204a2070b040c0e0f90420031f030000d0720900c0300340313040000748442100480d40000c0e0602c0200001c0e202c0d403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 341750368 1250 341749118 341749123
    0x60201060e040807060b0102190c170d080403051b070e010501031416030911031603020a080a0308060904111903030e0618010e06040914060907090e010303050a03110d050f011403 78
    0x120f80101300551b80c081d002010b910802584415040541c0c55503021041030400840342401d03403080620400c00c0c08010407803c032021426550766002a00c94070305e41e88880c0e40c16542138010b0101d90380500e40030414480c4103281003101500130150403520803031a5040c000010240c480310807080855181000078801c8450704203d2000610f45146000030b902c40b400c2c43c054050034407002d80694035201d4910041e09142080c00084220780c42202c3c282090b5070b0381d62003070381c03a0500b490010b408034840f4000601641400c150055102d40f103a02c0744440c032481140002c3c04044001014128840624001d10816810400c4032020000890302c050805524802d02d02001d40c04400f5107040107191801940d00340c40311000d40340a090208000e1094580121458a035000704803041e034855281d6030042100f8502416030502036404081d542601a800e6482c00c0d241a03110421800405a44404a0548501070400f61103c030700140310101e42410310044c5003507000c0c0c042c0c01c0407924110055004000d560b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 341751618 1250 341750368 341750377
    0x30705030d020705030913020a0305180d0c0203150903040f1a0901030914010e010f0f06140607050703120c11151806040b0c0105062110050a0f090c060201060e0408 72
    0x44500c0543e075400316240003030a50281d0012a900521900e41100821215401801002095a4080207030f503032440c4030814607640110118490380c102d1003030145130a10038180015218000703000c9882030340d041900c286010f01d04071403101c40c5030008034051000d0b8401e0110580202501000d00440f415081c03000d400c18030643c01001c0c14940d03562090300c104003103468040240750070a0020885000e41d122454040c010492008648a140901090116207603100b04400c0d62402d00c07400071302c200036500f404540c4d1300407907098a4520880c5400030004004150040741c064bc01e42e92102e800041d850581603018401c251248500280c00400c00c042034880191000c620307101d8007480300d880c0e180e03012554a11443d000780e05420000180030f000c5a00542200e40180003d603481222032640040501c07504002d840c42f9241a000403841000da0030442c1c2010b6004038904200050340142480304000700d40540d1800c0304c082c1300c55030040000540a1003550013701c202c0e010702e88907141c55580c0402ca84038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 341752868 1250 341751618 341751637
    0xc0d09080d030c0324050a060903050703030c05120a17012306030a0905060115110a05030a050a090e0f04051c021c050412080d0c05090310241d060303070503 69
    0x180c0d0882000070500c13981000e00007108001e8403010303811821102c4060384d01140a101e0040ca000e03800000c140c0d10440340d440407290480c002c0c20080c2c1c19075500b01c4442c1700603002600d0070302c03a0024042403c100304009280289090f00c83d619000251a95240480c034140c0c803c0c4c0e0b4141603003040440244035465103e803510030499080d5a40d54031264600b005043d0b00c1e4000d0014825140081540041000c0e4101000401c1d250340e40f054862070311841d0744081c40c51000701a500300303100c4c0340b02d00342c002e102601c0c0c2d20310a410014203198540d00f40f10340801088941c0c0b464400203109020a000b02405490111429a05a803a81001216010350f070384040704d0b41d020300c1145404d110980c03944030394151806841082c94030b00342e44555003024501034001400d1401001d00c0d05c420340401d01e004800301c0300c03841c0000e00548244549140c00000907c0c01c22449100074000756810340081080e00e291030080c12101a4000d5144451500d040b009070b8010103c41c01381e84100b241178041203000050307602664 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 341754118 1250 341752868 341752871
    0x14011d0411060c010903080109051b0403030509040f090b0417090a14060706060e180307021003090212100c020c0306040f020d080c1617070308030105130b090c0c0d09080d03 76
    0x1c0c4035002c21800d01c108001100c00c0c3d40f9190f4040304059200798128102c4451104c04d11450f122100c412138425412802c080141e0410881080083d006001074280070400400000380291210503007020f0b191031550840b0020520001c020030814a86990310480115807100744c2820b680a0102e01c80130601c2c05035200103860102d120030351781e40300000c49014540c403120a020383e0b540e484800c40c095200341e505440886904c846552201c00c00030684035003c0d001030141003004140f40080c0c0007440214010ba1b045008a504501185020481c1c404420041c00c0002144150b000000b81007030207528000d80310ba0404424070000c0b81e0b0080443c103d031a0110780c014003942c603d1418054501c1610300072041401405490702c404401c0f004a241100c0144010030b2b4114942d9510381d484001502009244407028001484241030508625182c840d130310303030300054031944000000c003c008100e070140c2956000103041e070031000c01841026144501800c0011a060600c0702954842c0c250030110b10030103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 341755368 1250 341754118 341754143
    0x21040209070324061e0206070f03020a03180c05040b04181101090306050106020627060103150b061209010b030712020906010e090a0e01060f0b07061808030a14011d04 73
    0x181c404030389019103020450281c0d04820f955800260241c0f17103003000d100d038a0603021050302c0c0d82400441c8181c07040c4025034a82d2580d21441b00203900035086441d11108242d643c12800c002011a4458901c2541c002d15034008418541010401903524266903e401141405091200f0001003094120500c3d0701c49035100d81034648000407a1171031055400903040900b46800047c105030040b5685024140b01c040d01645424041c0c4020f020a240340019411580124010000304161544040e00c0e0b0f502420041603003081c0c4400a842d6802541510100410031000c0c4000752109100e07642d120038040c2d02400d21149490b20030310320391454202c0640a14088000600960721407034074960741000041c100e5040382405907054005002d003246424541d0b1800d10041403000496000104503a05220f00c0362034040345542c0c48000d00400c5550b81c05004002031400001004400030b503100d21a030020000785007402404502440a061b84400a18031401c090340000c000e0b0719040c2688640c100c428000034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 341756618 1250 341755368 341755391
    0x15021906050a090f0b090606120604030e061b1c020604050d0e0a05060406030e1e030a0c050705030703032c0a0e1005090a09020f030706053408210402090703 69
    0xd801d901c07900810103804110401d0402c170030107580c14040d02082c400c44100c0d50b5048240a40e048100c042e03645036500c1680041c00180c450b070744880d41c2c5140604143d007008032007036400d81c2c096a0b50180d010f064000b2181030190001040b0074805c080ca0702d00c0141414185038035095250075292400360308100020710411000d07211021072600521010b0320702070b5190f41d00d2500038020400214005e5060241000c806049020071141003216002880a5864544000d20503203900000c044101c910740520080010030303a4060103218019400303902c0e01c01c0c0107200c2c0e61160f01e003030f9a140b1940b840016030413071000c11a1030303a00a0f10144e80e9441908a540d8560419800c1d141c9910350105038030865000401880e0700c0b154000c044290b10030b03948000020407820805454a20078011030001a0f01480b494141c10914410001c07010000103489404040d204043c0c0444802103000346d8521400103400d580c43c060707801e01c0700349003425030305d840a040c1400d034002448a0300c042c100e0420142c440c1c9400c0403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 341757868 1250 341756618 341756621
    0x11191103190f030209190501081311010c0c0e10080d030e0c01050702040e0a110406050102060130080f040f050f010e0405100b04030609020418050c101707080115021906050a 76
    0xd0782170010180c10846100300d040c80040002c40c001c1900003071110020622103404210000003d0b94072102141d011002d1100444805e15048400d450388482500001001480e4a03040c1740509049000b600b03038a0f0800301154501a07a003400c080406103410803c0074a1b4002040808408100b4030300665507010a000150190800140c00344090080c1a50a01003180e184c1901e40c0740c00c0203580c244030b00d50fa100010b90f102c100074030450704441c2c4003034038003208415000c00e01c070484010304000c40301001094503500104d4210108080f01020001010b120b008155001040281001c90f86121510140c5000804508162410ba801180c03500045020020366543d4035001c1c240c1c07962071545496032400e02201401080400782d00644c038050211a002c40d0b050000043e45400a0080804842c210240f10a548007400d5600802c1001940441d0b42c104480070f56005440310f540340d04281d4104a4004036000800d00200e0642d0b0004001c00404840d404490503041e400c5000041e0325034410507a40e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 341759118 1250 341757868 341757877
    0x10b010f0230030f01050f060c06180120031905011d07050d022d090d080a020709051f140a1a09040908130906030c0302040c020111191103190f0302 65
    0x3501142c0841000310407450805014101c4408445101c0340412600c144401d80c81780286d81e100d250400b8000a038885220901d12144440f040000118070000742d5000b0b182188021016224035000400c0c407004400c0f80340342030494070b19940100300079490000c011030100004449840030344c12a00000351158090000c0d105d211200d94815540d45956044920660f40a03001030f0350322103a450803851f1000d0800d400c1e0b5010007000703410381d0301a29847e00c1d2444075030019081b1408501c68000d001c1600c1c1c0070303806201c0c02018031418003070740c140d03255141400415160f0405005d2103c2501c0242c126680c000150040f182507240083c0768090a481c8031129120301801075400a0800d09803100304051140204102e86401d11180715140c1c850716228240e40c403030310024020024a03441400940f40950040c1514a160f00000601410320b07581c27000c032a04201c11140580080c09503200281d41c00644d40444062801c0107549050300b681420401249000c442204100304154075045030b9019034101c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 341760368 1250 341759118 341759203
    0x6110a0b10050306180d05070c050a0303080105210606100c0b2d07050a0f0c0c091e0b0d170708030c30072618010b010f02 54
    0x3000946070105044112020030b1140ca030007442070740002034903d401008102803c16405000d040040552107084401e070b00502820303611212850030015169941c016034600951107034403143d101d0340c0b40004000d043c00040001c41d000c46803803041812106400f04070310b41c0c011f804462420390040d001008131200314041c0001055020181e0a00c031207004001c1d451452414070407050070092840d40814500d1203010744401d80410820721442c12003d01542111030f005071a40340c00401c14415455005107410035a0140c1801c075a103c088112103000b8002176181400b50002c14081042504007040e82d6120700340c00036005907001100e4440d00c80e022811229190381000c1c046440f800c240134111400d901180280841061040516400c0d60410260321140809c81e00c40200c2c9668014003030f11044246001010381c10500d4543d910b2100e0f403010014040e084803038101442d0a840a1b54a0840d254194000d06018404054040030b5500041d50303031401540410914080342c420514100007000c0c1d00c4003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 341761618 1250 341760368 341760383
    0x5031e0108010b09100608011802090d0f0b06010f05070b0603030405150c0c120d0819060314060709030c090f230f0c130b130b040e0406050603060c030106110a 70
    0x2070305800c15044528544402c071013042c50b076252030781d404003040f14501c521008151043c004200380c0c98114002848420030010161410f42e001c400241002842c0b1812111401d0280c4048140803070704030070580c0b0120a09100700001101d410242050080d004014034805003540001d0080c0c0302481524014500a4460940781051034004081038104040e06880c078411502707600020328114203901d80402c01c0b24040c01e4407840207901203c0d048070040c0513640744081609950000341407031284800450162307014030400c4a008040605090015220341c042017003181d001d1010811010f24031085450400c0700144c14103501040c034001d440f00d4262001d1640c00072103450b00300034049894612490b0310889850003079480c0c000b051603034056150380d00e1000d9030803002401800603407002400c1d1101069640100300350b4858501d24158010b40107580400382030424401000224021315410100c1140a802585025403406440d4081441303a803080065001090a403120300384094418150030515 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 341762868 1250 341761618 341761621
    0x7030506070c051603030e10140a02071a19050c0a06060b0a0215071d06090402030109140a0615052101090618050f01030210051b06040311010504021005031e 69
    0x1400030b04803444150f0381800b8258003c1c0d0300040038400300080d2541a222030481003034034000e0149107a00d41403980180108500602811401c100182c2021403156009001c082c0c244400c1e4002d501e0043c07621f142c0000b06105400000c0188540c02003843e00d140361003525405041d90341c41c038010040d04050040c519004010803805419001042a001c9603002c982d81d180c1c501103e00c108403412a05880010b604000e4513910300095503112515510081083d410181202c0c0014101d034420390290003281d41e9000d84e103031401c15605880b85c0c01032280404011007450b02217611031500c14400d070308040100008a4281c030504419501304051040c91203060b942d80c40f200003c008084078000e00d11001041d0301000c0f030000280c0240e51085040244502d45a4a1760303003405000798946007002c2c14082d06010600380100d07170b80410103002421000514a82c24203040290100707021b01c3e60800a13904000030000035840350315504980354803a1034881d0303481c2d075000c01114180d501811040500302c010710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 341764118 1250 341762868 341762881
    0x307050a050d06110f04062015061021241203080c19080f15060d05090111030a0501060e1509010c02030c0a09020319020c1002070204060905040503030f0705030912090307030506 78
    0x4042040f80650188448c1020106c01c0d640707585240c3c103e074202603443c21900049490410081c80c11043c0c0340303402d0112210022120b845c0211040d20306444100e651074100140ea400017402c076940396800080c2804c4001d09010065104111851000d010b200c03110020501d071050001c200c441c007610511020000481d00c2070000c02190042c0c07003d01c4076800c9031000c80c00410310405010110440201400e01c0d0164003043d00001d408000c2c07140c12555030302d0f22404110070044000350720811001d040080c0a44c10900003410908039480340c40c1c000c800740100842010030160072603140142c2424a025074401500c000380c030b8403243e1020543c10011040000641100f250003031400341d02d28860710200d005804078003000f2030142d600c5111181e4030808035121291155030040035520f001820100c0d085032200c03032400556406580840710f0754000410440030903482c2d504a40c000a061404500d9401d0070f20526548001000c6401c0309860f00045035455550208040c50045a120b01a52054600031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 341765368 1250 341764118 341764127
    0x30a0509150412090902040b070f020a030609080c06010b0306130e07031b0602061602060601081801090f1103010605030d111e010203060a0807030c03060203062d0307050a050d06110f0406 82
    0x12075181000c10221130000c950140c9500a0342c0135903405040c0f442c104051920f440442c040d4041041c1d8006400b4280440803544900a401d409030240440740ea9501134000001c0c5000d40503888200c00d0581801400740720b85d59460f60b00040d01c10460302082c0011144d007040e00b0b10b60359034001803100101c02115441d58401e1400b0600310b17102d0740c007a24402e0303032510440e00103800000b441600581080c000a1403a40c007031196179402c01c140043c0000da1800207501070b82150714080080c0e0301c140c0000c1d4550104110301b002940046070030b0b40203102c610328210101c0e503504030700c3c3d0650f0f0034050400b0801c21080010020b031ba200a240e0007007aa1001044503245000b50310685102c6e010b54401d60020440d42d01c00600e480c11a940f02d100c0c174100c0ca1850300c0740030094102a15103a0300c41038049540b65040c40c08500d094114000044504008060070201441c21030258426030243c0041c450030030050395036904000d00e040d04410040748020700401e0321b245d2817280028040e4202004107000c500190701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 341766618 1250 341765368 341765393
    0xc0201060512030301050a170a060906020d0c03020903060c03220606031103032d04051215130b0a0b0f09090304060807030e0a060c2a061104030503030a05091504 71
    0x2c0d00e050111402c0348a07402d0712844240142504501104420071104040120b10075808140b03c0a558041c0d986640e40790541d8012902a03840741e4012070130040c024418820100162020304003145020210030100e82c849100614451a40002000040101c9a184080007640c02441449000d0700c965146c68402002c0500080c1d81c0c0a1001159148a04001046074002c0c8201c043d805a040b40401d60b071882600070f8500184001030500001a95844401c880c588402003000600001403003d20719604900d4020300ca44151441e000820700898450000c00380c10400710300c4041000c00d540000b15501c80710301141c241e0881803100810040d0b08020001c2c0080c0e4285a40b02c40c001c1c0c441110440030f0710b06038000700c461034001c1d226100008a00d030b031051265029030b050880e00e03c981000b80b202180c1a104149251040702e00c0d01074100400c511a604c866158070004c1404c00f41181c4680d039803400002d200415903542c070070128280c8801000820110740702151540c03c5403410780762038079141d42c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 341767868 1250 341766618 341766629
    0x1d070320030f0906060619050f07050c040509031809060f1f020f03070b070e040603080408010c02070f0e0105060d2a0e010801030302060a020a090f0f030c090207031202030702100c020106 82
    0x70036000701e00c0f8400b01142d414080d810091402d814045100380a2000c0090040c024007801020400024201043c001514046000c0c0c406064024251000d03c0147c403002081001c80740c20400c50304512040349001041c2400701950740c0741c3c0703a0381c5070004108486002c0304036a40c003100001d000908150703c4111540051000d909882080d81c000c0c040030307581d024110009120b40f84a0b0000303015140710f121203007420100108042241c41d034907200c02c41c0942c4203030014031042e516002c00001560f01004000c004041c00421700f02d0281c54490081e200d003030b0601495116580009440d141c10300c0c1900210460034041c28034a404990251003401d61a100981070b8000c00c40c2e0440341c61076980204000c07412660150060031043e43c1c0e03000000c000750b1000b402901804080140422440d801a400304040c0620a054160482c19800c014400c00b44039031104680c1070041101d10700081d4841c04030b0201d884e5003940541c40ba01d07000320990400441c00c00815126140004070321502c1c0e0305400080442e178 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 341769118 1250 341767868 341767891
    0xf040e160608100306090203010912020c21070623160605060609090703020a030e0601120308010b030c0d0f11030f01090606020a050c19120503070c0b03011d07032003 73
    0x240c1d10102603030401812120300040c1c007110801040402c0c610f4100070141032005000046250040d600c91001c803030300c0c03800b0b84014bd1207007151088604051801038511403480305280c01d0300c2e9040003813666441241c09402d04000061a05904c2178001e03200358030340803c400101c5500c1d1a050300844004605904068030040e0038003000c1403540c00c00d40d0481e0759090020b0a0b440c130a0f40c481000368081d5110b40d11010807d41c0d92081c0201c801020f101039406024040c000c40c0d0303409001e0400821041d0180c0041102c22001c0043c00407010300301c41110144c00070844041521061103044c800100b00786c841c0901800340c00420029054000c000c0d0505071801d0301d41c104041501c40f2400c0782c0c1c1d011490001000d0354004006510540740ca074100c2d40c2240e050b12590304945407241100c44010142801c2203d84e80d001043e02d0b0108501540c9010142240c504040d0640d8544040400121b0800200510850b454404a0980c2d03219400810640c3c5903401a41d43c0101d1140c03901019610484040c840607 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 341770368 1250 341769118 341769163
    0x162102031b04060f08210d0f0204051201050702060403120f02160224070f020a0b07030503040c06030c0f030515090907090501090b01050f130503011103041a07050301140f040e 77
    0xc2100b80d11503825114540d0086c226030b84240300b2418480304c1807410042c1c001c014003602c2c0038850345026420038004200d17809601d5070328210034814080c050048007401a41480d042200c0c071a80015101d41c01605841c0218904030b41c1000c4030000c106207a0600000f9000103002180f50200fa04262400380c0b0035903460701001c04501ca000f40c1c107124034501c103200f0300d000c2007444041044006111000c90000703001004250f9244c402046661080d0406c41c00301d01c01004110034880503610781801411281018130040c0b104180c003c2815607800484402d056840307010a0681642c034040d8190240050700e003003024100140c41c181e0324082842800030060030600085440041030165240030541a100d4506281e0030a6030401c1941000324052181c114000c4e000a6030341d400d0007408a00c1304a445400c2e40c909081c24420508513070340704e50000e810f80c80000d200c0030703603842800c61341100c01d507640003440408250006800200900a110307441420002d59841c00b44003c900c106403100081410b0282 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 341771618 1250 341770368 341770379
    0x1009211b1202191122180b0115050301050d080d14090d0513090207050a06110711040b0904030302030a090c031208070c03301401051002162102031b0406 67
    0x401d01c603010001c1143c4c50b040050710290414020204091102c884c3d688244d6040f803040904880010066840d403030341c0000c41d2000c0c084580070148c0035244a000200d42884103240203807480c481031050500402c24103403403109000d400c42c103507007054404200a2003600c0400c1c481000c0080150b51800d1103000c0e17802d210040c10b0265080f1380b1840351442d051100c203407410004400079044180260752034041c900010000070712030322a80103017100301c1c020182c98070303103504011b418500321200d09405a807801482074020b0b80c4031a10150710592600c0c0240e131340e0b5110a0210068207480361300800341d61003c1400b20821070f0030b0304440368400c01d9503039118542da038040c41206ca198021380d008d00401c019001807215031400350001d180280c002c10003a0118100b00907583c0440d4201c0b0420b0364400c01d048d00500c864504000c200d4030000c11440240308402c4124808156201d243c4606100f4003480d050450103201c031401ea1280d9540c004061312185011240116500041402c0c010311461601c42c0c00308070f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 341772868 1250 341771618 341771653
    0xb01020703030c12021203090601180c0507060509030c0a060b040c0e090406090c0e07050901030b270604060e07181e0605031f06111009211b1202 64
    0x1100d0301551a042c990a4136160101d04400300943d1504500410084040521841000303500a000300802003410707616000540210b004203c0003019401e00344502180030079482403d5407a0300c0e80020b40003800361102c0341204d18520409000044031700400c0c01d001e05201656100280e100010f40b028021041c00c0182126661307520242190b00240c020082804681e145d84020803952058104c0c545154503001320001c0c240c42150340c0c1c400141c000418000d1968140501d003221401915101460b201000440401040d19010300ca100e06145000441c640d4968014000800040b500c0880c0e0f8140608002d00c8000c2421800034400154000050750044160036030b0342c2840030190545043d4204541141d6a41c000b80000c103001c0d11680a81d40c0104610000300020101c40e220951007e0a04085c80d04041414284e850344030314021031131002c01d2040d5048040781214001076902020581d07001d070740078401c0c0c00c0b034901e221446071000b008105110388986510b0026408403045298403010030354 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 341774118 1250 341772868 341772883
    0xb150105070314090405010f080d1806030f09021e0306010b040305120304060e0f011e150e04020a0f03050105070908030304020109090c020708030c06071e08070e06040302030303090c040b0102 84
    0x9000400c1088110080380c400c0341d054200000302d48200e8982030300040020252102030f001040b80b885808801c20040c40e013042503400e400c509040190760050341010700340d0109440e104050606803a42a080000391055000d003246a40c003c010548144150a551072040e500d03201e202c1c041e2140e14008a07403941444261802c80398420000d1501045010700b80030b940d080a0030482c3c80395210701240c130f400d01c1c0501c01001da03040352100020341951505440300d5550303004003801d49540e1912103000c0b035103a1059107039420703120343d6000c00107a5111440850300344c403010340c811f50300a10501004000c1000640000d03005a41d0f903a5989100f58603075035501d803603100a40b8024041400310f44104030003400c9400c1492900351a00503545090740e11440d45007980d015045008940d0051000c0000c21a00300c0c40341900b0500030300e011400700e00c1068020340008000b81c0704c1010300c038080c4802070703041e9580000c42d0042c1d81c0c0901901d891342883d150741d40c0d490b000c3c0804a4412414100c3c0078074254400074520 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 341775368 1250 341774118 341774161
    0x2070e010311010e06040509040f021011060123030307030f120b0d060c12020a1211030906040605060316030308090c01111b0612012402030a1d0a1509030b 68
    0x8900001502e4010b40d54810415a0310b5000752050200041554078440d81510660042c0004141d03022944100072002041c003140c0800e10081f82c4981d00306000004000341900c072007440302002d03800f84041c111000000c00711001d9041c0700004000d0101544400140139a0340c440d10b4607050340420522101c25546d400780800e1b003000003d100c460101d0904c0d00300700a07003900c909215601c130f880b160b00e0505990080c030315900486c03a0540310014001c0f00348114680c00b070300400e1440c194101001019168040a40050003050310358011030310384e035400d0154142100714844001e602903076900d0050069401100c0d03580023402a42c140c1c000c01e5014204050b4a0007003000034103802d25000e40c164400355007050905804c90004e0201c4d241c2c01c0510350540d40a041d1041451100251801d0068840300080300702404541061000c0a0034940040c0d00302051249203101c03d81d4008000c0c08125401c00a600104c40e07040c052010310001c6401c2203021003941d0050100015943d02c60800d100c5841115184 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 341776618 1250 341775368 341775383
    0x105010c061a06030c2106030303060628110f0615010309030212070602070512070f0210110a061b1b0b07050c060106030b1c05070501050313080f04030302070e0103 72
    0x208000340035070b40418410070000911004900228000c640d00381c00c1100d15013620070002600b128142c038003c00003404801200c3e030494503840c140011070303228000500355034020300001c00c80409540b1050b04068090752005c415550041442c60001c28406c004540c00001e07024a41c440c40d46158080b90051080350710a04040174044500011401800441c1d020703411402000080021201c1e61001003601d1030090b1307409610380000e07043c01420140351031498000d0140270031064001071030a40c1d0400c01a078044888246c1c074860000f0999220b0038052650000380980304408080247da43d014965014004003e0707801e081ea1a2030644100940256882c00004a01e01c0c0b00d00003003440f01c80540c800805e2801600344050030400f40c0c5800020b80242c0003082d02d84000442a050001010841c80b8804103030403100c030b10503241c0e607403107540d20700500d410800c2c000001550441145107188540b0750012805540303403850010300704907400070b000031001405201e50000d03603085d1514066041c4d07500001c0703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 341777868 1250 341776618 341776637
    0x501050d1113021b1e0d0c060203060d05013305090c03060103021606141b0a080702240405061602060c03040606030b01060509150f0d0e010b0901081e06010501 70
    0x100b10304802120b401c4224103400700108a20342d0303141c410505206460720000d0808807081500c9500000c9101072890036907121030180c126080d4013488600c4540e800c50001a07481c0c0300c0d00040b511480d8001406813941d030030058203030100c03c0d2440c040362802020308040351b075000c4800c00300c0b803104869218080c2d03c40c90400c081516180010000e507002201410014609280c00304183c080e00c2615400351410340c0e45e0b22820b824500d8031950a0f41c81941465a07080209100c600c000c00fa000e004c0101d810090004001111203000300450808a00030504890f4608004040d105481c0022201158a07002d21400702d071031a17060001034101406640c003d00180e95401c1121502900010010380b00e0a880d80c00c000302050006d40c069028206965400e07039076641041c140301100441c400710350304000b01041060a542458810344107003980200c000b00d140e12203c910f0134050682004115444180d80c000003842c401c000640314114060030000e01e030f450b15241301c000e4503850300744207440c04500c0c0c014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 341779118 1250 341777868 341777903
    0x230915130b1302030d0c050c100c080705010f0213030302190f020d030203070609060c0305060a0608130201120f0c27030b040312050a0204090e030301030c2c09030901030501050d 78
    0x1c0519600c088110140d1404075100d8000a2902c4541c40c1200c0220303101d9800c20090240074403221304200c10682d100c0c08907001d035401c024203030600c90070058000b090100e101401c1000a41202c0100950920150745545101544c8000844540310032009071140410500c481c1c0169074901c120140c001c03504964002c40e40d000e0052606a40808804600080210100007000703882540e2586001e03041c0064050300d28680642225806130000d4841c00d443c000800440e50b003c4591548200141440240c0124600c0141d8101a921618060306800c0441d182c04949051b4007400803070599030749080e056210902c1d010064a038041c900c0d00000030041040c008070340210b0000d0340003440b914112040c0a03075014807500b110400e03a8140565500000e0402003176502c2d004020924003d400038520b517514582d100560500e0078441c0044440743c003018418080c0020f00310109601000406006d1842c05114150b201d610090000d40424541000480c442c10301340b0703507202c0e82c550007814142c00322200c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 341780368 1250 341779118 341779133
    0xb0a0501020a080912100e240f0a1503140102191d060f0c1e100c0203040504050c04120303090b0a090b040209090f0106030503041a0a020d050d23091513 67
    0x180d080342007920904140801406c1c1901c01c0c1c101c2007480802070040e109449070b01e080000c0e184c00881040628810500804115050146c0c0d046506144001385100340e01e90040c003010300c2540040c240c485204071400000c1c0341900203021040c29540031000c12401c40c90140d61903044943e5921300030a45412786103031818100d0042c291030082e049c440b0300340320b1820401d625043c5803001da0300241013100a10b64001104114002d00c01d401c10b1024405041c0240c0000c1d568041c0e40310f076034843d40e228400308501550305002c413030150041002032461072165007000f0700685280754040fa20503900030002048200c0398480c1084a5500840c0c98041c1e850320703000c02400041c00b810248480c095418a152105000d20891006501c01d42c0615151880e106800c51001e44c1d0044804c40700404101300c410b0154041001c40141515040c50b40d227070f6102510304002048034040d488410002c0c08540602503442d49922440b4040c41c1c0d04884000079020f6445c0010003054900c20150f00c0d18400000008190 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 341781618 1250 341780368 341780389
    0x12412060207230a0201111b0103050c040806160207120c050402070c0e0a0e060606040f06141e190e011d1f030203040c080c0105040b1812010b0a0501020a0809 70
    0x4503108080800352000110410760030001d101219441301c0303c1c843c21940c000110b40500b00c9408090141c00815598682e6400c0e040c0b4030f130358101640e07003001826510800081e240074120440407030308503213810000030f030003844052400d8005d8032920100144082c80c01c2c2c5e0f10013000b0303400440501c1251511003030101a40190300708480422040101103504007081803594400d4080e042c001c2244d4008042c03da0802c00f004d0300c900d0165000308401c0c46404000181e1804684582c5401d00b60118499140440c500a940da40800750300c2a44201a02a15020140623624090361401c2c6d0017910640041d5810854016010b020500c0b46030f901c960240e10180f14401e5400c00b0b49040130300d030343d1400302c140c03010441140000821f03030200034002800340310411800074140e18802840048070140020384540194450034070180e00009a40c0034001c0600c0f001e01403440c0c050107a03c0040001c1030f52901901005071118010012260700003180c1d07100041d10a06c5a400030700091500386a6420300c40007006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 341782868 1250 341781618 341781623
    0x110a0f0309290f27010906052502030a05030739171f0203010e090625050d05070207060201050a020a14071103030a0504050a12120c020118030302012412060207 70
    0x14803210268103003407074400390080f40724190f000c1d41300c118000142104009401c02c40400c0b206001020034015a0540c00c1180300410313031001c2c03580c681440000d19002d0183c50040c014040440ca203000c000e092a442c000d00c16203844100051404900c41e01e51034210a0030500e02c61400b50300070410008a90519002d00441d041070390040710380302d0305e900c456511a0030400c00095000004000848000c030f0240c1d004803200b0701420320390800406810395031480c10f001d0750900c803503014030000580c0158111150080c0c41e003424422803900a038060740b925560303c60b90016500f0807000580801d4540b00311a40d0140b01d440d10001c0749001c10990b20b5a0b00040c1c011958601024400c0180b558100701600a001450fa2481d41c0c4509100030300183e424507a0294000010895455000500145140c3c5244006142807002c1d003c0d80d0004a40003401c280303240c1420380040303070040203055064111442d016100c8040d02644422a0040156490a84030380c00d510a01c00200e10005800e60b0000c004850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 341784118 1250 341782868 341782897
    0xd02010203070b270303150303040602030301181b050304050d0f1d0621011508010b09010e18090a0303230601081806150f011815110a0f030929 63
    0x80c0d05131a01510070b00c0141098086a01c007104000d030102c000c42d400c103610003069016500b031516042c2e020795203000600420102c2909418003003000c4180764484c0003200d2221041055108015002510b680c0c815581980c450294406111146002e5183d008910045d55a0840215008840e0748460b00002140c00e03131000042040c150603c800074250310301510700034140f03001d5500d06034078000815405031050b0148241c1c4801044034515003000d540c00311100f8200f1040031000940000c56440c0c0c003140c101004d078920014041c04c47ca0008040440d01d100c2e880402110b80501030341510303602c1964910102c50701c03810000701d86500c59220706420400107222654400030003650141005001c407074088011110b441507480c6860140d40c00586824203080582c1c0c0c6071000404010b141040b805810b003d07014002d142e4116a12030500b03645014003980c11349001c7c04181c0b0f0801810042010140c0003e45c040380081014054907032043c0e003017242120512143c90000403031100b541c111869450001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 341785368 1250 341784118 341784151
    0xe07030b011205090c190f060c080d060902092e0311040e0702031218101a060403060b090f070509010804060b030d0801090c0507080f031b040b0d0b0d02010203070b 72
    0x460a83c09420b01a58030704029007034a4220380f05200000710b81d204440740075489440b007005035105603214001034a80030b2500690003d642d0806e04035610992620400107460400001201c080540c0600070f030740d1084405004100000f0310b0a40c224603030f482c0d5460111990481068050b002e5400501c94220400b2692b0030a65142d25200c84000c04460030400360b00000f440f03047e922903800f00980c2c0158110a2101c0603031541d1400c960306d06080c202c46101d10341c0c4480114030030081c4028140300702da004044990b510384078544503001d0008003081e03078010001400070546481801da01c05205245603515030307042c400900300440d182d0b180034106955045d82c5d164447d44584090001c02e007610082c0c2c40d0141503516180e484c1c000c031640a5011010070030144a0b182c001001c4008030313038980b00c4203115a500ca8980101c40261410313500c103c2490f50500083c0042c0040c640409001c110a045008000d000ca000c410720224074222a4001c0c01030708100082c40008000340f501540003011200140300a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 341786618 1250 341785368 341785397
    0x80c0612100b040f06030b10020a14030408030409150501030b0d03140f0d0c1119060e07080102030124050a09090f110f070507120305040b0d020705100219090e07030b01 74
    0x2a9019402150750880742c1e040912200da0103001f070000d0701000b81c2e002001a90348070030094a41d541440014000c07451070201912042040065401606c0b031700c01504d944a90742c0e030034200241500c90015880d4071035640009145d6000341300c1e0380011400900100b80d921404d80c0d0866546c4e0400080545480d828000307a0042d00c5070b00050484800406000140d0414020015115007015562001c1a50200c1d1300810212a441700880d1003990040d004201040320250542c00d028241e04803050360344c80400000769040c006100350450704140042d0a00310f5030580f0044410b8450320445402190300090200903090080d0f001d00d600c10700103200050000c91504080b181c943c00ba0740b400c052140c010880d88180902404140002c01c1d0300340e4007503902d00355980e02500310300841c424850286804200e0780c0d07039002c280d01160003055102d41610840036a0507001301c029000040c5004903401d103a08000345081c054100c190903600f0502801906640e4107034100c0c00703000e80d88821810400300420141c107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 341787868 1250 341786618 341786639
    0x302070b04090209040506030606060d02090a09090308011a0306030303060d0303090b010b03011412100b0319050109060f0203060a05121002030c0403121b0b060a0e070f09080c061210 80
    0x15101c109400f5a9070b46540d010001a1103011f49003c0c825003018040c04540c6e50b51008a807000c00030610096201e070910800540d802c0701c0e60780103071801c074104400541003542c000c0c034450585010910742c0a01490400810b00035001c01c51340190103034001c102080c4cbd9803800b81c14842c07916200f03140100710000a0355421492603401c0c1d101a0303040101000500c42c0c1a105001c40002d0340d0207030b138040029034609102c155503141e551a02c0e42c8050340d84c02c0844c0c90303481c14031458583c0000304008208603812071401c0360081000c00c005480582c0f07030503400030f101c0e4110b008490060100030300d018141c84c00c14007004006a40810101d034688a404244920b04d403590010710320070400444250344403440c508014058041d414a024100461410f502032091444002c6d000d200790420701c64600c030b03920000815460141034001c26440c4661204100c80194400346c60714404001d691960002543d840351141d54032004007269902110901404070008219090580d05ca0b4280301d203040c009540308480341 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 341789118 1250 341787868 341787877
    0x80a09050d02010902100c0302190812090a0b06090402060a030e0c0d03051c1517011e02030915091e12040e04050105070c1101030c0c08030117060a0c0207060c0302070b 74
    0x40541d444d80240c81c2503151944441050004500707240881c44001d0390000d460b060403102d00480c8125110402c01800040002d4a02a43d08c54038443c40a040c01d00810343e545040050031078030030300d2410000300309042100d403450107142c0c0540541c2c18510004000d5001d42a102d00584051180340300c0801255101201c101100d03019449441c0c2d02c0e0100d4102c100300c1d411109045e940342c0d0600c400c2c00003644805540750115401404a035644460014489001d090101441d21507007412400c41e40003c1c2c455401180280c1010049454990b401c42c800540900d044441010740c2c0c01c02085080300c20030b2410151080d40c0d01c070080d80d8083e02203001403140307a0429040024440318400410003040802d120b0305412000705e00300058110300d29615034400a0680800e107040540781e042641e4810700912070402e0745c40e07200381c51640369a141d403220f0095010012500100384558408550410018851051607141c580e004d800010b050200a50b1003002c0040101c2c1140b01d40c0e040022840000000f61 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 341790368 1250 341789118 341789143
    0xc101d150a020f0c060f07050708061005040b240a11151605031513180b0615192114060103110c0d1b140c030f0601060807080a0905 58
    0xd03296454044001e107420409082d5442c1c513800000c0041003560b580301612411040e00f5480e036500c250900d4203500703201c4164403081c9180b00d4001030103048100040094240c44080d01c0030888100c0c07080c204100c04000d021400842040f01c1441d0010030390f0200107041d1200325080c00134442c008010303490715280309840003100f9080d0701000d00640305108a175061084240f490400d05500340742d034004228803c8242041d1145c120a080c0c0c100040c1c3d1908401610300e142d00c0c409d490000142848042d6010455441d48070301d034040e0071400c46079965016074540140c00800f0050301282c3c00b400355000114840d0082d00131008511107020b20000d4001c0100007030b00340f081e05855040c4800054151500382d4502d42d01c540c418000c0110040c2d0000f10719079090b04501e4140b6000500d10340c0120300155205026141400603003000981810000e4156a02c200a07400c458460350b800c9403881d20382c042070040e80d000644200200e208a4456042a03800c50841c00000940c45881d6451520307095003038814 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 341791618 1250 341790368 341790409
    0xa030f1109100311060319020309010c110a0804030803040206190909141e15031902270703020904020d0612020f03160b1602031614030c101d 62
    0x400005081100c0d0140d005481c500c40c61000c1403c60781c4c0d07079900c150a03404041c01201c02000003075400282910031070058514000865807414207054040c040d01c160700910004c2035620b4101c0300180300010385a1041c54004400c18201070031991411680e82c0b010700b05aa00035000d0040300018034000081c0030800d010764445000c0741d41b4000b0a001036440781281c55020068440070488018000400c288140046002c000c00642d1a03c1c604c20800c411005107580510070340c0900c0b0b604e01a28603007468128000c40b0326030804400043c11550710304015005402c2a1401008684150302940140604070f0b0001c101504061003007454008440082c3c1c0320704000a4400c2c4500c041d0304040601d01004c070070640141000c406480038860b400a8644610040448001242c10318050041001601345500500f0b480040422400a80c00314040b4003d0384141624018100f51f14a0001041101c040c406480d42600400d00c81c41540c10944584460790401048000350480341da403d52903048880747c1a09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 341792868 1250 341791618 341791643
    0x31d07061107050a05060901080604200a080604061203080907030b0a0506090717071407020a15090f030f1106070c150215090c0918120304060c0309030c03030203060a030f 75
    0x1c014900385440d0b0029014044040d020300007502c541080340c0c00b4107070a0802c1d401c030742c580d04080390044c0500d180c41681401d503810041c1c806c280603801005c50825035914809030346c4542d03007004211061441041c1907854070a00020009004203951603004010300244c684180d0b1341d40302c003141100c046406015180da190100a01860710203109908810309240071841044244a4070142c440c1c003800c050141b00300149540d01c01e0407810708035420316034040d0800e0342c03550755001a03030402444919007601043d0307904000302c1d0b1032503201070190071207410000380d566a04040e107481c20440b40b20541aa00501d0030040c41000c5040440c00701c00a0070300c282d0000c3c07205070440c1c00909001c1c080d107000100e096a0b00602c010701200141107000c00c80125801001c50322200000d0550b8500b201381c442260043c035507030000019004000e0340c49240618818008125141c02c1201107039aa490020b004c16000040d1002181c882d41c00380da4000b801608440e00300b078a80d01c034103965030380024046944004545 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 341794118 1250 341792868 341792897
    0xf03140a17091504170c030c16050306040b1f0302030a0c0608010609050303040b0a0c0c23040c020d030c05090a0e0604060905061c020109170a0209100f0303031d0706 73
    0x1215032040c1181c0c05000111007592985140003c0508050302000304240c0f0352140c580b81004480100c01c4040031030307035a98044100c490b04e56650000c807080540381c0300f00010351400d011981030700c50b40c0e1101c02c05459035181450800707155212007290b0041c1070700300c0003c00161002c02c11200c03020300440c400058145408030051a08405030060340801490100400281c3c4000090300e040d03e01c8407070500d842c0d004076182103541040c3c05101404021041c400065200c42c690700100c44d20700812280522004908107000a6074032500700000143d220081c003544031361003548084c02c0d1445515000d80307032000b44c10001d0302184881d000144039807191801d0000314070b020b2050b04010813445100340003910303260700050a00b1401074030381440c03502c040186004680c41401d540000e0f003200841c0c001c19040c0e15080316910781211718200d001e00502c1c8003080318050100c0c0003d0450b518030403c010540d003181c2e02200a050404d040709100340c1d91400c0a4414802881806e016142a555041c42d80046c0c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 341795368 1250 341794118 341794157
    0x6030b0c03100f0503120705190b0711010213030b090a02040c03020d060f060c0816050604080901020f0601031e080708190f0806030a06050408120c03160201050606070f03140a 77
    0x19441192040f1500f102080280c401013000020203546d4000039440e07041c642045410607031302e45e0001c10b594804403442400c012554070b2030b600804040d55400c041118840d0380350300301d2041e13400c4c0070740301204400c00300300003410f0540c400e512800350310544101250b01d50109003900d250030a800c0200307401107242c4020041900c51500148140c000040c0f51030718101d0003403c1560421f2010b00808000510898841c10044900c4021980041182c50314900b5081005154100c144d41c1c40c010700030200f41c104034090010300c15069a8115201460701d025a01c48804481c44031071040f50003000c144480b20202d00684068070034400a000c0c2414080b09102c2d008000300c031000594030922901d1010302a481e180041e500f01e0643d401a000503c0c0d442d82e0a184189001e040c20894050308400100404d488c080f00c043c50248031140faa9002c0c2034a0031105a00780c91040b40d1954000d50240b02810114900d41c41c0740842c14082c0c00c011000c0b01c00031103a040207138890710629006ca911100c4071005074010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 341796618 1250 341795368 341795401
    0x903120405012607140f0408060403030b091905150613260d0c080d150323030919030f0c03210f1809020d1b030905061906030b0c03 58
    0x1180402d000700b07600f02070004088040940b000003040a580480a20242c1000c100c0f000c0c0000c01d4100c84e22560380b2900d05135500c00895048000a0a24403070a0346420604001800f4000985503010320344052000d41004240c001d0110a03580f000341598030a5450703141c000c06554240c46501c4289070300780300000341d1902030300b01d840710100b440701101c00d8031680116003100c41c1d404614183c0c9400c2d4007410050402e000e440c0104031024034041c080da015114646980d82286d100350414800303595141040340280300b048100074150740080001048a15241c61980702500d46501c102c65866100d4403900c900c54071180c400c03a031025840700e0500c288012501d00c0501c02c9003504559180200c2103400505203107041c0071040c14048802034400c400301d23209100c880503041c2c2d80c038119105e1940044030009400c0e4034480348404042106550a01031081c060003a10503006801050700ba20344942c400c00945440d0148000c495541c040807002600f010949401062402e40468a81c00c014400c5126082c0c3c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 341797868 1250 341796618 341796647
    0x6030b0105011e0c0305040911121006020a02090a090b04120e06041409250507062301030803040c030203060112020f01110d0507061104151101020702011b0503090312040501 76
    0x20f43c0e60901c032160620119854804103141c840c1012185280c1500e850242c0e4000561407400c280c03150380e5003910640909046000001f0403207460300c0d542c41d240d070b099200340034840060b0031140e112400f505103c0641074008a41a81c0000c2d070940c5178440d142e0400083e02c0072200c445020001d00c0e43c440c0e016444014204045507264605494140c0e48900071400b8541d481c021408000000c0032081040707400100c156049400c50049140c0399001429070707002010450790585082195034030b50710080c50001c08950050105486a401d548880740316400c010812106001c0034000440140c03028020719000300a145c10b03940307401c1c40600c10082a201b2510547d81040704441001104004c0001c40c0d140044041c2041666603086050074009050b1500d02044840c41c0003800044a055040404140d261180c2e120705209146908517400d038130401401a000980025884c5c501a180009001003188203034101c0c6d00d81064000803a044c030001ca0749003602501c0103e410043d41d6004040d580341d000c1e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 341799118 1250 341797868 341797877
    0x120a0c08160f05010c030e3601030c09050c04030c15140703020c060d15030b06091f18020909041b0602031c020a1803080307031404020f0f0103020d02070606030b010501 74
    0x1801c020720600d5042c607a01c43c40741003060f034000c0401454090088a440d0742d4010301171070501d80d12024050748003040349907030707190b080d48848100d150101034054a5060301d42c00400001a6032074008101301402014200c08402c460401002002413016107070710004001854000c07200c1010101c01808203a00001c00703109030b800070014034000176400300394400340300c40c101d130071a4954a40e0f848800090450742203490741810f68035004800d220a1320b113034900c1004119690003641c0e403100d041d80102107044108268050349000d081c412201c5072602803100304a01e5800500b44007e140000c0c1804c00281c03402d451031114500d2030100700011001d41005050240010b61410426511903000d0b001905400074070b099003ca54180f5240c810100c908901c40b100042c50308894981c100030f05940d20613243c210110349000560004407503901e100e00c0c0b1858000b0000b0002c03050030410b0182d0040040c64a07410180d081042000c44000c902c0035000140c010940013031240d0852412056540301030700002d0504c07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 341800368 1250 341799118 341799163
    0xf010806060a080d120608010204080a0b0924040305190e04060503010c0c03080c0903030a120c030911061b010e010f050903090a05060706020904050f091b030601090b120a0c08 77
    0xf010f00055010b00540301d440c1c00280b4511401c02c481c001d04135500b100c07180e5400042e001411101c005135244200380543c2c155009a2500148603964080105440c030a199000004a40b88031440340f600e58040d0003801d00c03500c1c01c0d08101060b01f0340300340c208810b40030614503240c24505060912440d806440c0c160000c20512207031080151070302005400c02001c01103040d00203640100400250703202c030310001e400c890f161000c81002502c40744401d0310080a8516081100465520a000c0c2c1c0d04d55030f07000401801c80742e80030414081c00798000e000700a111201c2c05c2ca40300d03521400744500d400206c48540002603549500d03e02e40705682000d48036882daa4814001103480e82c0d583e00991003128402c8940c60380d562610b1901c1400380c000c890400b030303006143c5801c21038501c40f20102e86208810003001e845000002c40e00c10740001081e140c1a0750583d0007813006001c0e0001c0c6900221680900401c00708804860a0030705141219498084520144075041001a00300c1082000085406203200c810030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 341801618 1250 341800368 341800379
    0x20f0604080d020d02120408041809021509010302070209190e0c06090f01110d0c0c0909150509070503100603060c050a0516020105070b090715050c0a06090c0e0f010806060a 76
    0x442c0100709041074843e0303001504010000b502e604803080d041110000c081300d4906030030300c0c001d290003910420715040e50030400c031580e041c071f1482640740f0254020080d40ca5030b440200c98046036001401d01a0505a00f0000040503a4628141502c40c01c0b1039046c0c0c8001c40d681e812808292001400c40d00401d500904500003117541e5141540c480d03d4040d10090358042e0003400488196814010b003c0b21409039140c40b1000c154001c00740c0c58040c7c040c401316240d06903103443d158211242807002400b044030310042c56403104030940044e60403408081c2198100ca85510009042c2030f80200c400c5822070350f950040003041103501503044101c02d2414003d0030203101c5030002c1c00c984200c0700f4104c03440450316040700442e0f01810981c2c2c049900302005001d949007440003d40d480c0c40714014000b00b5501010050700030b038810412900345010410203010342110581d90b002c00742203c1c1c981100ca4203c664404194440c41090f160311a000501d074036a29549000409400c040e000341c10280076650740f43c3d05008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 341802868 1250 341801618 341801633
    0xb0f010903111c12020d0e0a050102030306040f0e100f0501090c021e010f06090b18070c0f0c0306020a08100b0702150d0b040e01090215030405060712020f0712020f0604 74
    0x3a0120a4031243c0600c54030003000340d498103080c4801049080040d24132914140e000807100c4819000703031150702d402a010030801c000079110348a21401030384200001001c40c100f03501b103030340f00c40d880c9500807943c860141c0c000c034140074486480c40c3c40d03980d40d003441c0076401005008071070040242c40303420010341c2e0071440029168040b00c0d030301250302c1c03c555507541e5403c0d00942c0b0007208900190310403c10390391503211400252414128a61054200603161a401182004114007a0b03c1a40307034420444803c2c0e490040f017620340702c07094454800940000022500f180002c0c03034041c09595500800e45020744900c5e5208106800c00c2c0d2451905121441c01a198010700c44590860303d2411070b01e4a68000721500986002c481031900a810b02840d4034460340150018045140308852150f003900c01c80340c0b1000580003c40300640180e0000d0085031040f4002c0340c1d40c14588102c075401514003030200034024aa135100810850b07006260100d0709001079414420700b160385004801030f00c020b0805454100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 341804118 1250 341802868 341802893
    0xb161d01020a0803071e050405010807090b0a0c02060c07030809090c030402030a140f070e01080c06031006030c0207030f0813080313170309041b110f07030f02180a0b0f010903 77
    0xd003a940f0010200782c450f8014000c000342040507620304014400000d40040098006203d03d40c0400c80c94800300d10110b005018040943d0481c071004c500301140176104132050304104401380c2c6c02c4081000300100711102031007110040d50080c0e629580da00303502400c1c041014002084400e0760001030052000507600400c1149101ea04422001101100c08071141c3c1001449070404001e03229200c400211140040c0500381280c18060035210f83c6c0a499080c4049803100301d4500c01c07140c40d210b00c1440020b020364049801d40301e65104031070b15a5101c0c0c5d15580e5002c1d05c030009646074030010607805041d14803040c4100281c10560051801e04d2101540d0011504560145000c9080580800044d03860704000340c0c0da07542001042845180c42d0950540000d9000e5010000050742e10000107401c10000181500030707110020040c1038407487d603183d110140300b05401c00c0f64410070f95801901c4101d05410454020900043c000800304000c10420000c0220100c10906114043c1c3c81040460103011400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 341805368 1250 341804118 341804123
    0xf0212151e012a14010b0414160314010801270f060f110a0c060e0a2013020712030b2b1b060c0b01051504060f0207030b161d01020a 58
    0xc0c0040780c40d40d00034900903060b071882e80b02c9141c40790304240622100030f2001c0d40d5800303c54000c0003004e00c66400d020540f01c4405003100006400f00119032251410271311450079280c0703480c0c0040c94041648088000d400280d0001d40c40d40e440e12151002d9400c0c0040010725501401954282c6550503034420b2080801002c0c06041140c5e1100c0d404c00403203681e0041203180780708001d100c2e50783c1d65882024008107281c14003902c11038609000d1000620380080d07140070300c0e138000041c040412524080c464006084081d91600031f010100b2500c0190514000340c00c0301403003001c60543c0000303041c01c0101101d101d540c610703108464114800c0a13a1006042d81e07800c000201c01c1c00d2010044c1c1d410990750030340c1410700402e0104080800042c10079400201c96518512400016901e80d076103000300080302030140320b02c401c0c80c2c60401c02005030b035000301c0300308450001900580f20203d0303982c0c6034603141490031201c100100140c0c8440e02c0c1850381c00703600909686180210080c4440600c00003e5440700c210000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 341806618 1250 341805368 341805377
    0x703021305130f060902180f030c060a02011401030804030b15060d020a05070c03050109021806090105040b120a06060602010e030c1504030903050a060b09070e010206060609040f0212151e01 83
    0x307009040d8601c0d08950f034980400541846a640d549005074000e52100d8004d40c1d107943c1300c1c0603c52407032600a07003165a4000c01401044200c00b0001080100d40c040300580040d90b680d901c3e600600030304000454021805828101d407150b10b9400d003001d403c2c0700100043d80d00900344000d0341c5079683e00d005890110106000068917244501019070b003610032010060544001c692000040000540005884520035621080107010407060045800d01c00c1d81c15036803108a80c00140500e04041c0c3c0400000000240200300c0140564031031400c00e003e4070400d8440944a50341404501c0e0240122240181b50340011032511428410785030315010b01e115554113542008010401341441500c11201540d040b805403085201035280c036a0042002981c6640518055000107012500078815400b642c036040e00030b086585c1d41c0504001c52503020074a02d99000f9903910765190f25180500c040c01080825045983c02802c02d045c08108201c0000c0845109207124290702c200f001c11034840d5550614213003003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 341807868 1250 341806618 341806639
    0x20f04030c2c1006111609060302040b0d081207030b04150302030c0d0203030d0b120304080105150a030f02040b1207120203150115030b1f0f0306090507050403020d0f05010608030d050703021305 85
    0x11070b50305107410b0040c83c43e00085952800305807c0380342d038801c1007164030071942045100d9005082c80100d2090301e00103030442c4014031203401c020088003c0190f0102092400017529805070001504584410042810901402c0c0041c011418200484944610120340c01100d00640c4da000903501d100d00181c098649403620710040e00c81c0c4a0700740d0900d05503111002d80fa00c482e150000580204000c0703400201203032242044032000d040c0604444184d81d040000c0081e80c00054003070001629000c0c80640d0054a01c02022036081409d0000c1405000204001c004014141c010146031050b00300c7d951809001e038000412009500b1103041107040614200419615941e0700090304244406a40381500a800440c2440c0c465020700301c44041c5c50a510b0400006440d1010f2000700c035803c99515001c10800c001c1032000d4507090035a906982d1080300c0302070039040c00e03a48450954a143e4480d4000341d001113aa0203080740c090140390b500c100c003440c0c11420b22240c980600c07582e049512445028911100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 341809118 1250 341807868 341807897
    0x1209071a071b03081c05060a05270c090111030a0503160e03010204090c081e01090f0b03030c060711010e070302010c081b1c080906040303020f04030c2c1006 69
    0x4110b10a10000201862a520300386100e00703500140d03038681910607813880c1c19885002c9205490140101900e4000303642c1c1000e0074002c010a141e812001c481a004400c0d03801824140040e0b0310442054a0a6455401e034034000341c00fa042c02200a85c0ea030700103200d120320040c1d11000366640140034409034103a00d001c115054904401d0b4000807909075000050108140040e0780000000e6015551004580d0356103003500e19841c8a007504124110b10004010040001c46401000111000240014030f403001c200c0080c0c40c2d984500241040c3e500443d0800c895903401c68404002c80701c03010f00074454001c030800c50320b84806950000a0600900c500d02034240038051007594542c01407200000c1148080300c546130341e1540307408145013060f19154440c0400744d228100d100d025422070001000262901e9030158041d41225501c541045018440080401d20315100113008015100485001c5803007420192140c0d000c100d02e00141030551414421038000c4498100121501d501c0c1c403240410130075 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 341810368 1250 341809118 341809133
    0x1b07320d030504030f1109090c01090905090309060d050106500c06041202011401050603060d120c020a0e0103050a2d050304291c090204060b1209071a07 67
    0x2e4001810700136044c1e107005c04010462044000b07403d41182c4c03514850b52181d4006980700300e4801c03003078006140248200315460264000542148040060380d0900c007022000c01c1c26030300440e8031242030716141e00c010080290801c042400c03070203400e19403142e2800038440403042e80e02050090203414840720361034203c01c081010030f820004a5603a801b5540d502d2480816900c04041e1401d8415000814840c1000e50051181610010801003181e805a18100070418103400c0144803580180c42003c2d81400103250b14101210036100751a1408208814014460f60701803580103990301d141914014804941c0004a80090710b510000c56024444a85141040441207e50030216202603004220801501001800903078000c052032003100784143c840115104250080541224070400c55245080d0034410290498070125001080490040d40401c040369002c0e80643d00e04100420b0010200310507021300c0c1d8011a5140c02000030701d043c00b20302c4408820001c00d403414520002000d03000c00810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 341811618 1250 341810368 341810377
    0x270d2003011503060b0906030f070920040602100c0c020904060f0603020301020a03021803030406091503142508040b130f1a0915010308090d081b07320d0305 69
    0x1010b14200c03403140d40380b074804090403888440600c00c1c14410005110740c203001480840f00c490000c02080030707a1405410500400e091084465412013000625201c40c21000050005010740e600804400c2c07a90030801c01202c01c5520410308004a0b003c049006d83d440c003540740e41103600002c1c00641d09110b1031509005180c00d90009406500114003d4102605a030152141e00c0e054003071040881c0794401050b8481c803070b901a800c0820300c1000c0c20310800009800c0070224068034207002810201c840144034081c00c1c11903175035151402081001c403440000720b514242010940c1002451742c10a51307039903603c80500a1500741515480200c0c403081c0081d40d22080c40030340e0018807180203017040d011842c01c200c10480b9000118030440b002e18070316010002c003d9049030703000140705042410100801c6001d22842c00d00b5a005c0f00148140b469072483c000d80100500605c0c1c004214240c580bc5208500044114481a501d179001001201c006c581224141143c0b030201e03018040c00d011443d09450301e008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 341812868 1250 341811618 341811641
    0x1f1509170a050109080901090f05130b1504030b011403030c0d0f0e1801050f030715030203040201051b070e15090c070c0308030703020c0105010f03030219060b06270d200301 76
    0x1340040d01c0c4c1400302600081c10405802c2e030707c510803070b515000b507a4560003461140c141c105012400f49503d00940f43d101400d00b480044c1001404103400c8111a99078100790402d403a0580758000403c500340c03d1011001d08800103a01a41c1864070072100a030b00d600142c00200e05101c0002d522800a5100718940d400402000704010481c01d506183c168000000740103071381c000e10380c0c0e40078841c1c41e1030300155a4049071410f40d190b82c1c41c400d85102c204c01070b40000c1e0049040c480d090082140b44c03000801d100000d204000000c240042c9802d0055101c0e60018015107018403000c100c040554644104031039120590303d604565035070103441c0070701c100c081c81d910107840791802006112b0580e600d60020403403021140002c1c003007640c07182d0010414031050702c1300a0150340290341c20840c2240c00ea100d01c0019004030b400107824140314020540350392246040d050f00720040e0382c050361420883c01c1c03840001740c010303158840c50081c1a940c81d02c030580001c1d0005150040c090301403509940940203100941e0303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 341814118 1250 341812868 341812871
    0x9041802010c12121d011116030f05090d1101030b061921020307050d0608032b0603061b120b010905010c0507050a030f020907030b1c030e04051f1509170a0501 70
    0x107906282d1405d03903580000d1003a840c1d400d14108440c030900c0c810655041c0d51213015110603804070b940e0705581045040d0150070030b03c0018050f00805940e03018020b03905030300884200d80c00145100005007102e042111180c4103110901280181704d84142c03c0c110030b140c6505040a1307409022483d00c50a0844c000381c4100b8900000030070086036801009440c8000380c02a00f40801ca40703d8024980705d0041d64102c8204824030005160028102070703142c681990850340010b4000c0e01c0b503d504081d0f07240c2000304000e4543c403c0c9001101340d441100345007000c081580c10492100080002080b45070301d440b0315810800e82c0146282406000c0c0306000040400500302c2d00703c1c607503034900080501c140c1c500a0b0f114480c41c07400281c10600074000c9401e20b0100602680207400c444040c0813000303212680680402011200501c1240c0742c502c41c1c640a4459100800c0904c960307a2003000e071810041e0050601032141880080500340c01c01c04036815104144494045a1503d0701403d2800d0001e2901518a6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 341815368 1250 341814118 341814131
    0x504080406030b0607120f080c041809140109050c0a0e100308091f0806090703020c060a11160f02040e0a1703150d0b0f010506040f030f0503091509041802010c1212 72
    0x260300300103101c0c1040380a072101ea10a5850181270100e6004900c2205100c1340c050b00c08100b0403a883c5d100181580c820001010850201484242112004441242c0552003001501581d180c01090300004001001d4141c2651074020140e01c840407040c800101111000328582007295500e0482d10b032440900200000c50070302d003100041815000362481402010b5004c04944124864021104400601d070002c10b1640c40d04581940140381c03a002800000c0d6092246000f440c080320420051075000300300403a554503160040004407003050780304002c030f9840084940005190780c0c100f211003c0040a0654403943c494a40e4048242c140400c9540610008a03010400c881d0403540340c01103000442400d00340c2c0c0c858090104c248a580940d5801002c50f103800c01c0010801c6945041240c42042640d04000544000c42d00031076113a820305d60000c402040c0b08801e402c091140080240c5007000c8820102c4180e000039200b9000c0140140007c0718658814071640d0051480b600b11116410040044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 341816618 1250 341815368 341815403
    0x607120f230a0e061e0708061c0c08100b0406080106030b0a0b061b0109150605031207150c0c030212121512030c0307020a080f0d18180501030b06040504080406030b0607 74
    0xc0341866000c545c0310401e40418081889130560511038030025145022490070b50620301c8010f048010b00b20707a582c00220000ca20400140b201b541c0340c0d00c01041c0030030000c660200700001d071303000354200d50080c1e0b240040400120350f84401d507540083c806000000d01c0b5281d140490014811000e070b104014007a1040070b5030202d4150300c80a076250091103240d601c41010400001a00c985124269050307001001c0e084440b00004000d08101d880fa0002c124980c214641842c103844a01c2100000700318140d081c40240768050150a85031100307802e074540b524044215020180030050500f01028260400304681526065803007281112210200e17610b460f0740c008243e0382c0340d110100890040b801a00c0c00100340f040010b0444022603104050119880c030540115000300000c9881d0403100001c6071b0003c0c000601203524401c4520350304000c03943c0e40c1142030020130b04001a000030b015620701000c21001ca41980103403000e46170b07903103000f148003401c0c00000f0304140500480507195480003c50300c443d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 341817868 1250 341816618 341816641
    0x30207051003240509160e15070501060605040e010e160521010b1804110306010e1801230105070f06020a03021b0d02060106110606040504080c0607120f230a0e06 71
    0x120f403030407200c50100759900d507440e2546d481c02c903403080040340f0030602c1e100c503502d0020705c480024400115864101002504c030746c3d080d140598407010120340001024040700092341d080c0e9001d042158914403071402c09400140c01001c00b440d0001c20000d004c9601c49000803d900c020000d6001250b0542d03255848204400c1694088800c1e01600000010690401e007007a000700d8210700321070007890342075940d0b560040d40c0c1c0e42d0840351030135400400316260070241b91102c400180a00200d42c0d040c0c1058240840d41d40c04030f040f00c05100d060200510210700001d8805035020322040e40044007580322000d050b0300350080e0085820961a4035020300001c0310701c2d0b000044426801078640d007152841e076a41c19043c0c5046030201c914418540102002400c40d041c42e410850b08280700d090558030b05958024161b01f070000503551000000d49201076000981018010a0003050400d0410014001c4070341c402d020510102c200203400c02e848400113105550580d00c11903070304421030241e030818900300d00c8011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 341819118 1250 341817868 341817941
    0x70804090f0c030b01030c0903060b04110c0c03010b0405090a0204200c033a3206011d030718060308070b040b0c1306030504020f0a0906061704030207051003 69
    0xb000a07142482c0c4d01d20542c80780c044d41035090309603241d1440450650b101c04000c0c19070301c6121034210343c40e100ca007921490a100100020398050000e042c031440480101425a0030914005204da4207102c28040038203400301da41c170442c503811940048c04195000510381056242d03d04410a03c1300400e002110600100090044501d22104040000c0c0a038138140c200c00036092040f03125489840c044036100302c040e40304005016120400f4056000d416110300000040c504c601a2450520800e01c20706503041082c5c22021500c626102c898006548082551201c40384142d140c43d152107200031409034140e0303100c14082c51b00080d800d41e450105084c840c3d40260180c0d4126424001d00000401c00d446000c1038554220800b19080400351808004038040d000140c0243d900203990301c4600820340d60080181c00400103040045052403900c0c0010703001501510740108981c02000402002950101d40d800588004542050b022014000110000c00c034013211310101105c909840c402108558060343d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 341820368 1250 341819118 341819141
    0x4052505041d0304030210030f0f0e0613050d05070317070203071728030b21120304080a110a0501020a02210703210207050303101d0106080606070804090f 68
    0x5001d102c0d90042c141150300001c60300c450301c41d08140b00a10061910900c90b401480f2a45401306900b031004200b00c00311841c0309020130403a81d499841407807402c401d201156000c4005080d41d00c00e0001500c500d5201c40444d001c50301040b000264850406020f00c8401b0b0340c98107a06150156454404d602954a6001d00790589081c90700340d41c0001d040049000301e51010f62107564074542c9480d404400f00302080400c41c0c200902d61038601e40480e588944800c039900c40c010341c40401e2400050181241810f411400c580c020307090070000c12000c103480000701e43c005101e51400c00442059210388900300291346400400799400014880800d41c1e00040380c0c48240c0b00b010540702e05100d800140c041921a41c00004c0c0401e840c5070b51341e0070b22903c61418007050b41c0c17608005880d0195070703a41d481c11b6901c02c84104000c815094414422042c290a0b401400c41c030051428185504011025010f9000108400d1046100144c00340411240d03a064030014004c0e0030040c0407105a0030f842102600c3c1d500d089 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 341821618 1250 341820368 341820371
    0x9150d020d050906090d0507080903011e0f060b030118020c100e1504030f111c030203040b06090c12040f02040507020c0306060402040f17210a12140f0405250504 71
    0xf05541d0351001c51a140100040030003881007000458068403a0303000b0807410364038444248048081a2400e020325800c4500728118a40c0d4030040300310020445000c4840f41c1e210710b282407414000b8038101d404681c19a0206848103619655413080140070344a4002c1c00c9420780100c48a0000900054120106688071002503400c000070041d0301c44089502200d014000405200e864031080b03002d980704103510280c2c0c0080c1c2e11480c803001080c01c52a000e00b6011000a9400030030030050040c1020800d4029404a0b40d51905007406060341c40e5500070389494864040382c0001143c200007071016113403011540070300107100c54540f1100294480c0707140c1c1ca202e4000d01842c00000ca040c45d152003210146e80e04131088040702420560301044559141342450b50a115030a840511400da800b44002d02c4c040c0e11400c55507444001c0002410b1400140c0c10000540c00c282c07204401c0000011401d501001800394041c0a64446c24110b1611860b21880d02124100c8000130b202c903503c2804a0301900c105540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 341822868 1250 341821618 341821621
    0x4180b0a050a05040b130512220807030f1403041a251e0201090e0a020c0d030e03030a0b1f0f0e0904020904030f020721030912030903030509150d020d05 67
    0xc00742c141d0b082210300501c2c008012002902c1c07201d01e040b800c1c3c0507501070012108200842c241880c0c565104121039840112003c40001442c0201c90007035001d130444030040e01a56281d03648100715462003400040003035032040d1410078402030400503100108a0b60300404c0f61100c1c28612214654400c8020030501102d0000c4d004100c40240143e1400c907500111488110b031544444041105144038104e0400c5400c000c00101c0108044043d130060303044290060341c40e1300f401e8008d8900060324190405060500d03440da65100004801c4d241d0050000d00d020480081c00000190041880020040c1101303d0001c2407a2701c90380701200e00042070302c0751030f14461000c1905c1002a50a01218003e6000b0228800200024403403441c403134003a1090700441c3c00c4980c5910b0603008442c0d030003881c0a107290020601c10705065000001100070204000c50402c4620a03807001002c0341c6d010302004d0705010000590000949691541007481d4542243d4030761109941d5a6001c080c0d48403114001c90b8908240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 341824118 1250 341822868 341822881
    0x109020712170a0b13141608040c150c080703080907320102010b090103030c120504030506130305040803040b0d14010503060a110403020406060503090709020309031804180b0a05 78
    0x10180d079410300e100e01c4640543c0e6600c8220000d0300b40c00301c1403500700b595401c8180103407017640244680001a10390803c2035152851aa2402c2c850810a000c1042042c205000c0840d0201038140c1c26560307041d65004e60100001c106450307099014400a22910000524009140c6c2c4044003e0040340c03035000b44c4104503a101c20a00543e820010010352030300303002c4040c2240d030845100f1804c07080c006000205400002d200010203c140036402900442e941c404400100900041014462145400c0940c100750958607001d41c0d41c04014240a480400c1d001014241801501030b100184140c10032030355101c0c0c580007021101d41203035103010f25141c1030850981c484400d11035514140c607400f13070080415a85074120100035107444001426070000412021015840f0360042c070018250640b5499940d09191840a1070721109500204801d0f1052060050801c008411a0b25400c07143c031206121050202c001340051031921389102407050389402c2d000402c10300102945c07084414117020091580c43c40c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 341825368 1250 341824118 341824127
    0x5030705030c040b0307052707081312020a0b010f17070506030c070804091a09070306080d2007060206071e09210213020306040c020106030203070306110f030109020712 74
    0x1030140503450341121a504400b4141a48a1610b1903c001d0440d81c6e140e0769400403d922141219140034105403a140410b0381c1011524840e401c088a4505040380b0316005039682c0c21060080b070000d00f503080307144207140401e00c02c100414065810401c0d2841c2941d460900c030302034403014031658408003403210860440b10b0011408000b154000b070805441d6956002c0c56075240c1d8003a85040707454070030034040410007c0a84c480c0f078290502c0805480700051120b001c02c01c4c0444014040d00405050020134400b031078010900c0a4248420305004103100c002c0c900c958171103014800304c1346d07251085050000700303e80d001a51714058446030711200103100841400706102003107954500b020412a81e000c114442d58000141c401141010700419108990790000d0100f090b030720207440555070044248007441c41c00e4440c000c152129400200103036455940400e032158060321014004c29620300031410102c10700400c680c0088804c2100c990b9940e10b034404c410007504101c105541c00840342d5000701e5801c0c002d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 341826618 1250 341825368 341825383
    0xc0a1a0907051c060506010504120b07121802011101020d050a1b0503070203040e060d1407030308180c060f0415020304060306150c0609020103061203171e0406091b1205070503 77
    0x540f001105101a561180b601915024010790b0400004020018a5031442d49590003006d1182181c4641800c01e0303130b00203103d240300c85800c0031542e2030b000a48410f5103801403d20350999081c20001003040d4a155913500a001e00204001c4003400c280030448582a15407052400c42c1a40084c41c0c82c01e00400000c81d0140002c40d80c100c00b41e4010001408120808950107900080050a078640003413240e0b620000c014428456183c65401002e09004254026018a0f80602121001c0c00c441c07903114085590f5040e26035155024100025407000c001040c58100c4020303001680d50405140303000d42c4020355030b9000d4810080001c0c901440412500c400001a61455030642e5a8045081c8603448003c000c11204030107e05040d84c0311030019410114a845208107400f83d11364001411140c4110030303070150001d01c0c1e2640e05008012482c4071100ea0640c050300250844000210700d00d07145459100c14603201c214107100704500c80d0000e4400e5018641c0502c039031141050719020742d628410b01d50380d00071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 341827868 1250 341826618 341826649
    0x5160207030b0907120501330501031508030307110c040516051c0f0e0f030307140c0712140c1002060c07060612050703020312030712020c0a1a090705 66
    0x402001c001141d4903541994100c0340050950301c0c0b09940304410020b00040007400c0703890303035100e007010300c104145040c45001c00c07980c81c01c80c076580c14182a810303140211203004040c18940d840620101d10329021202d000940003e804603a541e040c0008003500040448a49545034031525445084c0da04241c007500d802030580c14030703020454040c40410340e5150006e81141e4000744840005060b02002030041c00604034481d0030004800354078502c568203113042c01c1c1e00c500850f4004c0041c070000682c0920110701d06560048034030340b40d0142d12030050900e16298449a0048010f900a4040c410b1202c401d880b111589001c0700d00d60034407601408101c134985040d04003d03800c01400180d142e03040380700502003207116600015840b070301ea0b6074092001c0f404000640d01940507030740c18800c40c2003c10030012445070120302d00d81540390400d401408407200c54440003035150003160802c2250b1080000c001c0e500d500c510951180c00c01800c460691802c00c07541c40c0000c6c07050340741c00901800c041444903c00728 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 341829118 1250 341827868 341827873
    0x10504052b0806011101090b09070611030901032310050a05090f160c050f03030604060b041a0f090d060e0c0a03080306040207050c1f02060708132d050604020301051602 74
    0x905091003510b0000300108054188480c1d00607821180c039003881034036003503440340e0103401c8c060070321005a40c07600b00315400a8061102e25036150080d030400000362408071000746400706000903030541c0403502484d160b40120340300c8000c90a1008403102c181101d000c0e284140c89002c0301d1a40d500401c200040141d56608002c0100750201e45054210301c4400301d000881e0a01c49520455640e40501e050b481d5040510303190004030521415180c80e0042c1d1340100020040281018142103a450f003a01d11280b43c2051034a0000e215024501084265168003a008086200301186070500e40c001d000200f480003554064031a0030a01440e100c914041603907046492135007540d0302c0505000c02075028180070b80700d0384a02d03004400030f0746d100c1186c0307217005555000129480b03810364030107854400040c0407942400030710000c004818004020b0320030800c2d003203440c64900045c0d100c204d03040c1040001540d40d045c1704422900c003d00800003501130046109070001c0100e030380d8003002d08000309590841000182c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 341830368 1250 341829118 341829193
    0xa120c091d0a060b040605070615030201080c0a0c1403180301110904020f0408010507020f060105030c011e0e04020a09060212071e030e03060a09110a26071701050405 73
    0xe09146003490744080b1100001444a40780c9140f030000390003da101c0d6002400014074941000621f008140b40e40702c3d03006200f43c9040c00c560000e072070088010110f40c01d104c0042802e480321441801280035a540000c3e03800c0002c0c0319030303d11548a074450f03001c0d40301d06a44290614140d0405210318100440c075183c6a41c01d161b103000400c000f0350300518041e20880010301012400314820300c0340038000e6020b500240001401c1442581c11308005a100c03d20941000d8139852150340c01c0151007101460010010a00144009064601c03080c0d40f20000c6e0403034404149410380b650040710711070030349000e13800300c0d02140543e005200691165640040000001101e402c0e030032810314100b0f004041c1329003010103903076083e003021a1034040c045403407060070f03911141440e05201e51403000c1118000d040c0c56940f107540c00c124440c0c00e00303141d440011040b11032265000c04008014004c03e00a0040e0782c07107620221840703640d641e01074503058505480714000c155600f1038400d030410400c21020f204c0310302859071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 341831618 1250 341830368 341830409
    0x31b0b1f180e030f0a0918090b0c030903130b0307020708072d0b0a0504151704080a0306050d120305100f0308030717040b0405010b01020114010510140a120c09 70
    0x900155003002c00507100c24030085080c074a901020b00742c0301c05159140303819145010100d42034000302c0c4501070015031406d4103c80c0840c10310502d60b58024508464507969481e403a00b41c80c41c500c20501d0f002d9000e001c44801040e050507560055000e86000d900300c1d0b9219480c0c0075080d88442480c802c0e040301d80031503200c117460141000500140080f030402e1000d02c165941d1a0003007958041c011004c000b403030004091000307103203040c1c84c66681c44480c5000032138044400c41011000c0c03405480a403e44c000442c4100000344030340c003c80050304002e0901114060545001c8401ca102540132038042420030000404864510110f101102d01281040d0891403854030344966585c8081c08010402103c1c0c1115261407003040c00e02800380e480340c22407100364a040d041240c00c494241014034116410502064031082d901c500c1079055801c100c44000928014140c191802d105000e1541605400458082c4103075800c90540f4444180410052154000c100e41c1201d160940f801080404070101d620482c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 341832868 1250 341831618 341831621
    0x1409030a1103070b040906060906030b0d0b0a0b310507050d0f02040b0301061106010f1a18090907060809070b030a0510030204060801061d0103080f07031b0b1f18 71
    0xc00718064142c0305296211400030120358800e0b00110412902c8413030820185511400340d0300100100d14041000c0c4036184006034010b078402002030060100343c2c007c5000c80210394046010402c00a111000b07060b00300d1200c108001805800002c41d0701000a0226040300c140141441545079586181c074041d0701000c044028404071071008203071982800081115440d00d40210b018002d1500c0b000c998070606424107180440580010181184042d4204051400010050441624800707000c0d1030300d180100f0100301c1c40c0c95984c034960002c0d200d0288510140f0119100c2c050b12081d81d204450780d42d9400c03007107541e80041d1040940e00001003002500401c06035201a800854001c0d48100705940d9400084c151107541c6c2009031907941d0340c4405c1100c050b40400344420038038080b0202116601d1520340800c98003840c011050551070000300e40d0205441210a20041c86011401c28680c3c9114140100d1000d001c44040047ea4100c100500180080080c003c0c110b840d0794691286c15403440c0c14000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 341834118 1250 341832868 341832893
    0x106021519061202041505010509010c050c0a030804030218041203021b060a0c0f110c06090613080a0606061701051c06090b0a060501090e060103020a110a0507061409030a 75
    0x1c0c044480740c0e200506804007030144200908040c035011501092600400c01102c215007050b0b048034241980811240c0d0700001038440181c002d080007404500107080c0303241805144c40c512640103201c50b00201c1081000005401668025035561400742071080308801602c80c1074902030325000300d0490004609100340c000703018010300544607a083c03001d011007491408100b51101c0071041d031200049240f20790300c52804040f154031841c000d400202400070017a1102070600700d20740584000640c02e805900c0b0001210081920300042603811035940c81c0091b12684490704c211600c1d41803000020328a48115602d440c0541c0c1e40d2000350b410703440c0808105100c2000ca070007103460480d00e44100701040092081803c42405150544414070300312075400100c65a40d04810305100103004184181c0c0d03440c13620b20b41c2c00341007030a0042c2c0e01c0c2c021013015104002c07031150b28070aa01c5a0700200040190208940046400503120850b0103c0071410114060180002d21a0160701030201100440d403080c0018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 341835368 1250 341834118 341834131
    0x5120a02030f0f090306090114100e0c03040c0e0405010207030306050604050f121905010608210708030703090c1205120c0c06090f060c0d1403070806010809010e07230901060215 78
    0x46240504c00d50100342807074801c5030083d8403659204400344187c24180c1880358005052280e04820a041040d0410000390280c8240000d40012000604101160990001034500c5d00c0c40c01c00d03540350914000d4080d40c040d0b07104400103420820b0001c0d03a802d11400303440517528003c0408680003070310014401042e001c1040100340d80f040d00f041e041030680c0071440742405400382c80041942404e203150549040708001a80034583c2c00c0a010740402141141620542c42d80f04450560702e0300c0304203046002c1c10325400d0140034608003200000701010100ca03946006442207055030500d0180c195601e41038014492000c4040c0c10201c07240d41503140030401450603c1b0000e00b80441b1905160101c2c0c0d560f088a008500180d12440005030f6607508480c2d02c0202d170001d001d985185103005c28009042d03050190a140c140078a80004c00c00ea0002904050003150f450340490395220360340c03840c00822410108400f1450f03020480700080600f4440080d905803400c1e0f40042140341e0301190300c00020100203111 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 341836618 1250 341835368 341835397
    0xc18060c031e0c1103030a020a0b0406090b13050d030b0604090e030d02031003140a022d0d08130f030c030f030c06020c0606040f05070c110105040b120405120a02030f 73
    0x442c06010300c05140308641e80143e40310420280e041c0b400c039024450b0800854402c0c2c0c014803a100c0001d03400034860704020b60200f0402066215407600a000c1c2544140c02002006050100302003241d61521800055001d80d040b1281e940c603959094084810000c0e8a50300720000700024040780c01c20350807d1503003044503800c8a00d0484203070703420f108031b0b0410f550198181d841320f40704009000c440c4031001302e00810503020f840d00d10401c1e800a20f030401100100c1e110350810460031a121001d07042002c0315604054062004241149450300c80d503803000d0f0309501c0d01c882d507100120300341850003d110306680c2e005144903501419038851803009500c0f211304504004a2010840c00038a0500140540f107001100802890500004002c15543c5a0800d0b41016280508001e007160784181742d0080c0581201d03203440b0300181900101c031107201da0b8005c0740c0344050000b144c0220ba5103103200355105a000b082074540c08003940041708464464103188900507403007400038490102420f8003e02402d1940c121 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 341837868 1250 341836618 341836637
    0x402010801172802030105060102031810051611040c0e01080c0f0f070f0201020c0126180f1c18170715080f0f01080316020a050d080703030c18060c03 66
    0xa404055800740107030f4a00c480c2024144003141024082c040d0016800d0010f182804605d421410000104003074980c0b003109040c209851141c0210200c81d00614201c0c0280c810360310f1801c1046807007500003007140c0a5442d01d0211b480d030600c5103d0880459070140e4800310b1070307111041c103510160010003c03408650340c10054000f01c0300ca00c81c0204941403250009014404c00d500029080007140c105141c10700072020b1100b56841d000c130f4007462400d203140c024200e07551202020266825010303500c0707a50502c01c25121031154800006e1089040206241d4601542c00c01c2500311460301c0803408140c08031550000c140f0002d09080d03050269164100212144c80d503580032607440d540400d5401c1400b2480c03402c14000001024440503030f0110010441102d10351401404c155a40315400c040701844c1d14180008085566485031500100002070a0881d840a10b051400b05540180740840110345070091814082d0701a2010541030441d807900c01514038545081902c440c8800d15088040008111 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 341839118 1250 341837868 341837893
    0x3010518041b031203060905010f091e05090309090a0903080f250f110115180603140d080a09050a0206030901020d0c111e03040603020c160602030901080f040201080117 74
    0x201e2400c02513004454503014101d003c40003038110341e0710742c12443c0f002d0f0804005008161000400c2070841303214040014540d8054298a0a81c0201201c6078640c0e90806050080e0520000080d103010802101c19410603200c208141044541d0030790005c011904100c0000c04181c0f2082c0c1e155480002c5110b10403c26140706401030388030080c000c50328040340410303000703c2669a1000c400380302000d02600030841a60009034481d8241828410308466011011a030480e10b03a20b030308480020f550000c014050030100703600d0036031110244111000000c00c05000180c01011138018a443c0359044000313459000441d0b001c3c0070300c40e88000c120040d03c0d0340070000107030021110700c01c1210f50301c1c85641d211802c1790a0300c025402c2070301700030640e108071700c00c1034414544581c04012182192160f04005071b90751504a4500e0908003000e58080078036010250000311a6000700003842d00781026a03d03c001540e84020007440880103443c0640015a0f05005000e8148541d8095840b03040b0002200e0000070000b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 341840368 1250 341839118 341839163
    0x9041b080319030c08040203060414010b0301020c0106030605072d051209060f06040c0813050f0d05070c0f3606080a120912120e0904060905060108030301051804 71
    0x10305001e591101c1c046489006250303d482680c031042c026141107800b82c10541c00003a03482901070f02c098186a084219640480d6096201e9080407030040c000b951a217650b000744a000308581e10080e1030890400000502c218070840c0040d101050901c00322035540ca800c107285c126030000e503485909000042010301c5200303840306c40c080e10030b200d008011301803490103100340c0c0001c1030043d02441c01242002c120285150b004861143d1100e65043c0301d000f801ca007802c22034075000e060300a80c107046c01f5004031444059404001024104d001d903d4030000240c1c0d40399400011181031042d0310422042000508000d00a55100c0000c001c8095200d00d4484000720103904a5203603a00c002d83c20342c0025041400c000c42c103140812000580d00f40038886c0d501d060000146503100d80d00040c51100740000000d2802d006052102d90300501524401c0640350515011009164030001580d8034800e400000903134103000811603050760310103040d2007a40c1041090769000014040d02c21210220405c003c1900c08858 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 341841618 1250 341840368 341840377
    0x22103060a1a040f03120210020307050a111203010b03100f030b150d020307080a1505010f1203050708030c03090f01050c090409020a090203040f230606150903120406091409041b0803 80
    0xba060000c111071290001a180403e008c0012502600600c10802c090b9089016a001c9881c141080d141c40c96450700601d00342100d21420051100c1c1c04000070461603400e002841c401d03418410080300382900c3c4c10440110058610008000608240000382c8040146844d1015408050180e5030350034056400a400c101654000789150b91020041c0300611902031170145000603400c2007000340354184162044805d501d4081c04d11081c10208540782010f01c51402c0390756407074112007176580780c0c10300820a6030294002d41c0c0e280038078400c0354a244800300e018440d49004550800070720703140400301c40a010241005c41416603204109080003d00c41400340003c5100740e208001e0031501d010189000d00d62000d03011171401c00111010790100041c80c0001d8125000035003124600c004802d5030510041a11074101801e426020342c060352113081500744050b00035a540c1c0d840c1c1001d201e8a0314000d0040320006000c40740d101703843c0d402050206003000000a026452458198541c80c0c9030461315255901 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 341842868 1250 341841618 341841623
    0x180e0a120806010207120b010504020c0f0312010e0106022409030405030a0606061b0312270c0806070e130e0a0c0609080c10080403030b031c022103060a1a040f03 71
    0x3050402c20120f9a414031004019051004401c042d52100752940858190140140b130f0141c1d60001d08c2c1644030741e040200f90000624001169900c0240590040c0300d080288203902c42829a0000400d450780041800000700c12803001d42a1902a1103540031115100034102d601a40010403002c1450348003400843c000e540a000e02090244ca0400d0040c1805800280c0c0e084015030b00c118040020351240314544060880b40c1c0c0401e410144c001c01c0b02110540c10b45550380113844446140c200801420300c001155142c0b01650081d50b5000c0341035402403090980c050b80401250f14070001880e1a40c0320031040c0c628441210180d60301c44d40e4081b0306040940140c404070b090550200300801082003501940401950a205045482d20b4003074181c0001078402000c0c551a0441c0889a4a080140d040a0704004207039030303a00d039450040039440b1555502d0080c28010480d16494848460100700ca005010141a2842552520a03110310040d40f42d14070031a4010200000a442950703040d0340c4c4044c50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 341844118 1250 341842868 341842877
    0x9100201020408061806070e1c050c090601030e0703020105033d08010227030a0209011502010506041a0907050c060103060f0b0910090c03020412050105041407180e0a12 74
    0x9060070f90031450712900902c1040c2c07a054000a94044170008a4400e0300031503e410412a00d888200004c1d58160341e040300080e15440245110f42400000030308090812402e86852400761070b03e90046094890328100e03447c5c2540704520800055101d000210390010448200d400401308030b00900c04010341800003000075030010303080440d0031184503486900401200c4000c600e406086090911441d2900c01c1d069169041c5140701d141a40741405440b144945c014442c140c0c81d0707120108203845030440c0280c40010b41c40c0100044113420706210b01103401c180f0102070011840c0b0001005000c6800802c80000c10400384400241000c082207064080c40c410040072480c1883c206149040710000340200348180560810b00035440c080040c904144d8250b2000814031044500c0c0030380282c4104c0d888042400000c12808041c004103500c4140100c0c4111414130f02211012803a60b0340d454180500b03501c00542c159008454803007948001d401d4480b0f401901c03500200364503078041a030700d403042c1e28000c40d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 341845368 1250 341844118 341844127
    0x501050f07150902152107050c070e0709080a0b0f10150f0f020613150605220c08010b032d070f09060504140d06021201030501020a0306060c020616080910020102 71
    0x500d01800000c40c207601d41710300907090420b100c05400345564110960011100c4141c0030030344061080301103a404041e542d04a41d5029500d1f180c2d40300c205003c0303c403000054400c0c0c1c004074903c01c1c04074403018200d42007682c3c595103450b5204200e0900d1005040310359481c1884100003102540b841c2000d284550781d461b50b081112000101418007000788000030215003000f82004a01c1c02543c4400800c1c6802c81d4007411940c06840700c0c0710080c00b640c0c20103940301e4185070290031086042c03d28044d800324540c90a20a590004a040d100a00e0a01428940e04024000103020882100c14660340c41c4100f09082041ca41807501d0b89134100095400c20002500c04108032076040d00000710310300600c0c6514109207054a007425081c850000c4140f00c07441400444100780038064181c05640881d5401202030f1569690b81c40c22031f000794407540030103010a04281000605500811542e00760a03000b40c091450118050321044440c40d1901013181c0300719007400b03000d00d26180c41b00000b5030100791390001a607a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 341846618 1250 341845368 341845373
    0x2301080a1e03080f0403050c0723030a0209010e060a270501051504090207080c01181401020301062001110a030b090c19050d0906090309151103040501050f071509 71
    0x4034188200a2041d40c0d500c00c1007031000951080b00140d1001c84403809410304d495030701e02101c5034421410551041d00c12283c1c003181980c40e11a6000e0300c0c110031080040e40380814024143c41b1060300e44080d60201e00361004102484104186960081c07008058405d26502c912404480240c06540920a005c2110310006440a5441498058401141d01d1500c1c070046007a40052485140511440320380c02242c0a030411811740191444090340c600240811070040381d0703041c101c00c514007090b140c10f600c1c041481c41c601d8040c0f08890507104940d481c0190300900104102c000ea001c03000c4500030b99039450f200d2950700340c000b000d020f0b1840a590301040800100e420008041c2d00503040c8001407004001d000c13401c481d1250720707480c0000281030850b00d604001400d500100340d1070310050131280c2000440020503600c42d9584c0b0503911a8400b000b6010780b910401c582040b02030200c0b201e10780c0200001e1084d58000e801401000b000010050b1030070070540c0da0340b890140c0c1200c40c00c1d217054540c0000002c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 341847868 1250 341846618 341846633
    0x306090803190e0303010b0d0e0f030c06010b03010b0901140705011e0b030114040623040602120711150903130e100605030c12070c0602190306091505042301080a 71
    0x202c0640c900d4207000c0b0b1040200b005403240b20600c41c0c0d40b0260400a00d214401c40250058546043c0e58001d6401020038004442c0c0c40317500102c4d0002d15402503078000b082a000b02c1041e2810790315080159810841c540c40152101d051040c0180307411002880001c001440900402010740350140520651103140c201c100c0030b0300d88400f002031103a418108500317040f42080c1d001380c1c0d000390001e4010943e003c00c01c0e0341c02d001c4110380300d40e49584090343c0208028050150000d1440c10f10f405108001f59407218022100101240401045500121404240c40150349055500074028100703891501c0044c0f00f4001003550f040d440380c4041c5c0510004c12104201ca0b0108100400040c00c190f461031030036482c910900e1142c0907035030501d00e030594003244410344100c40f0300c41d2181d40400115512628100034440b0140204065800207080c0036003c031b1021402e0044000c050890201c520545007040c04001c060308540601d5405812800464400b143d00410301c0c600808a8101400503088542001103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 341849118 1250 341847868 341847901
    0xd020c0f010b240f03040f08070516050a14010305180709060e0a0b0a170c100309060c091a03360705090f06060a0c1209050102191109100306090803 65
    0x94140504401d40b80700c0c0200141141c841621388a0695a03c0c0d80e645803010780010030f803101038402c000102d030610400c000090325132070118642650300c9855030340c4d40c10003218889070b020b00d15030310044c40030041095000303400250f0005880c500b0f80c40f031401010301c121b01d0000c01d07900100031079482d040200240c4d02e20a0046800c4080b03820140711a4440401041001e02c40d0f1040d84003000c0c0300240e151800200b8014100d40301e00c002c02191102190340c000401800c0e00e0b0000f031b101c00303284c2030070f611444e1300842c84c03081100e03255000d800840d00d080200a106800003003540355540908042108140d41510311403428221240c4c0c0c01c1e01514540c07001615000240c0c02560048100c001408290802c0d14441980054100c1e01e0f50350315070551304112400412590018002c2d040120414031540c1c112011409850b000c2e070807600d20840703d5a05d015885070a01014001000c00100d80419041048443e030b4001c80118455045030307902d07600c1d10221610f003c0c0907101e00501005100140c011b070080310307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 341850368 1250 341849118 341849149
    0x1410150f08030c3007060e0f2b0e0a090e16031502070203100614011103031504050408071b170c030601140d080408010507030509160b0d020c0f010b 65
    0x942c02d100405410307a5480240c03094101c0d004210440803c000c422192010103003000f039aa00c0c58030745805d8074160001d00002c1501c0c1245004d01000030780d1003100090003550300b80f000280e1420b28080042c21030503181a81a000c1c0c20440030010f525038030349410160b0f80003002494400981100c4c07955000e030410500000c19001e040d01808104003040711324039604c00f029816000140d40e01110f2002030301e0039012101d4101064100040080c0e603c000720b1180704030b031000b03894403d5081c04160303440d5228401140c038128540c0d11040c0403a045d0074035a210b0703503201e0320511a1a1600d02c1b280c8848200103803035942c0c500031034882481401074541c803d461b01e2032284000010700400c00c3c000001b03600d4403814000d02c82d00c800c07030343c4001c1007075541d00105200b915000410107035160707201c0c61118040c0c10f017240c2010203c0c0c103280100c0c1d08000005a0315150070b00c04078030141080d0405081e0318681e44400b900301c0000d9028000ba00b42541c040c4800a0701d0300e040c0000240b2200300105015620344095440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 341851618 1250 341850368 341850373
    0x51b0a0305121b1b040509030a09030807020109081905160324060b07030305010812030c030103080307210c0207090507021506030f0a03080109110a0c1410150f08 71
    0x108001a00007a02c1c020801000302d81c96224501084251a40d01e00e6498610143c81194800f280307021102810504a40066605000c15640e10607010303a00d101d100840000a4151401000400c80031000b0704046441407410007803d50fa07405a141c9400f5210004484100310486100200482000b40b6690004014280d02c0058a540c88000f001d4160302d0f9503080d02640282503440ca602245d0044000d04521a9a41e44901c80d900300107000b80800d0041c541c0c01d10503940203000c54100082624480c18070f400c0c0380c2d40f5503070840c0e5800b0034942001d00210300b800712440111468819950610309080300030074000510a030844030081c0b074040558040d80216142800f842948c0349e0219840c100344c00d190140640546551012a140580c8000c4240d601e00911840700105a8000046ca0403114000414403e42c000000d1881c07051140c6204a004565003840440000e03071a82c010311081e03012031055504008405014400780d40d070b007240c000b49a410021007840100281003400c000381c00000c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 341852868 1250 341851618 341851639
    0x20a0e010f2306030621030c01021201050d0206070f06180b160f02030a260a020301051924030e010606030506030d031404021c06020c0c0a0611060118090609051b 71
    0xc03890611000d4450f0340a0704060040101d1622071b40e83c1c0c445504110811a40d81e4001e00b20154004c1d000983d00f0f03191006040c000007060328003100d0402d4200d1f0020416850201940d07218841081e40c0001110220780b62800401240185200141401c1c01030706141e00c10701d00031103a004500d848065401c1806400c1c018400100c1c3d001042d17800304401800d02c0031a80d104014400f81c11050781c2d080403100304045041001040e0150041d5040300c40607a0710b64840c3d407404820300000e800c103010300f00c40000304013901e0072041e4024514103104081d0303007000104441c0003c801801d40b440c0b50010030202c0d84075820300c40141020001200c1d503030442c0c41c040002e0400d180c00e5450046024101130702c16082035203050200740c40300c2c190f0a002a8030610843d0340c0d10f00209aa6115800d50610510405131300320f00017001801442d00f843c40f810300d03070b0142c00c15a0070214070380f41030048400044800b90b40c034202c50001550521600c407416014100501940f0081c844400000c408110020301595141c43e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 341854118 1250 341852868 341852939
    0x105040b0c0f040302061902060c03251b050703110d0b040215190804170f120403030b040609141003030207152f0d08070f0309020a0e010f 61
    0x11005500701e822801d045940d01ca680000c0a420f001e41d800196220700005641010315026101540030b10003550203484d03656603904040383d43c500007200d421540500105c500c0c0385e141114500000c1c40302560400030714070420f0750003003528070480321021107080d400b0a00c00e0043c42003e609882c040b49040b1860300c1601c2c0c8603515440c1000e8080c000031700032008820b10380080030715007094590340b512000c04070841c1c00f80a42c4c010311000c0c0581c0e040e1025000420a42030790205c002c11155070b03400604600b440c140c200c00010031042d000810a404050762420a01450703600c5000381ca00034215448041880c41a1041e21000e80c40c0142c080074401049840400000c0d4001c1a8201160742d0404400e4012124000c2560302581c5413100c41006000c070b0001c3c1201e1808854210450002c02003103a400b0a0b502c0d900b9556000b05481010200d07440c00075603c20a4860741242101c02d02c0a002c0034041661440303000c1e9084000e0704140900104540c2c1800300100c1b1046845104003045174041d04d07004040d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 341855368 1250 341854118 341854133
    0xa0f0e0d170c040902120f070804030509010c1401020408070f080705010c02010c0303061d07031401050102072c0702030c0f06010b04140f10051c1407180f03031d03010504 75
    0x40751410151450300001d2040044007083d1401070480c190f042d50f4500300c003180d0600304c8800315808003042c0402e60100e560181b24845d8a4496a07150703c5071407030088404010350f95100a10402c031180c0d81ca0b1610900d0300442800500300a24101c0010603019003001d841540b8058035400040c00d0f98442c941c108507680c2d0002044848640a007422040808103050440c003070411500700310410000c40d100c22000840c2910130600c100c7d02c0d0754003080710780b09004c80710345160001c7c811a80140d002d180c007030008004200b0101e444107441c03c143d00030400d00446000c00e0103c120380348070140e0000311b8102ea49070003d00806841040300d4000d89040d40c10119422001d0199025640c40012405c204e00669241c400520305407030402070030201140903c2d04000d1995101e000641c20440c0e038241022400446405080200701d41601d2a103241c3e901e8500491f104606083c90b0798294801c0f080004180000c50740070f078081e6000e17903101450b1140c940b0441d0300749004501917034004d80c9400c01704030118022 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 341856618 1250 341855368 341855387
    0xf22151e0e06070c0312140903150a0e190209010501080c1606022110050406050d14070509040506060907080c090d03140a0302180d03020a11180a0f0e0d 67
    0x1541071012414001d5800300c1e0700c9004807940240034030100e10010043c000303030009102001c5040e41c1d8068a090025910514901511481c160554031040e121115564402201a40200410700c0021044c41c041c0910381b030025001a000d016040e0300031003405605000358402c1c054082030070441120306004c4145841403144059403101480300c5e40c4807030100005030301140c451082d45190001100d0f03903444030542d0315505031440390a00c640c40e440080d03142418022101140c2004000b00c10034106501c80313031800b07c81c1910501c403e000d2040e0100d069547d83c09094091070155000b0304040c9020310601040c0702c405041441446802c104100c004a0840c08a403031080c030548100c4905803051405680d100c9545407800c03a00100403036800032007a0b141c1e016080140540240100c0600740c80b0502190030038622014005170881000c260114080b0170003640086000780a200c00340c103400da0390800d84202669043c02c0c0e140c440030482240310b654040d0941c55454a80901201c01d03200078050b2503001c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 341857868 1250 341856618 341856677
    0x140916140f10120e28021c03050a08090109170706060f0801022502100c0f120503091506010e10030e0322060306060c02060f2215 57
    0x10184820580c588550381c1c81c41003030300e016003401152910000050b0000541001903224245000120519550002a40405505000303507a407190340c030005c1540d0b841032400360240c1e00101600403540c40d22008280e000881e5001e45da826403a0880c1c142c000708900c1d009409a20a681000c907008081501d4001c404204400341e0740d52a41c4243d10f25098003d400030b6401402e003180440d00001d501c28041d0002d2848809000d200c83c1ca40c0c2c00e0301c002429290280b140690494000088001c82900515081301c0c0b080c00340c40440c5110003c0c2c0d403010060382202002c00c0020b02c0200a0040c001420803014402c0400035110b00322a161010008222800d4091000e1051a41c020703070203c494040e40c00420012219802d0701e580b0803d000c1036221444550421091901c1c50000003e04c1d0351107845890151109a950b005041c00d15808208a40e00320108008225604020014000100c2401c0c000402140c40341c0400c09460403049014040c1d40340d00000031f1004408020101c104440c0410700e4080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 341859118 1250 341857868 341857889
    0x4031a0708042d06050f061215161b03090509010b0705100b06070f0804050922020609121006080607050a0206041b0329060121050c0f0409140916 64
    0x20415258454061000c3d80070300464908410b0000070885280c1d0310b44255026160103036211041b04100c1c1c1d1b51901010100c2c000d0b00f914001c0381c42d4401c4840c1520340342c0030510b04116442c0750045101c028483d500d00c00c6021921040040040c2d00301000d9981c01013120f04940c41c00d00d03001d070b210940c882c0c944a1400759101d0b5603098a0740340b9500d14040d02c075003540041040301c5010785441d00d43c00943c0680102441540c000000070048056a400007005495600c0c0d103d01046c0c8070780c2808203940055031819445408a075001c0d0b81441d04100703452443e1402d01000c00c0603468658094281200a0f0040d01042020844680c0c0c1076000118140c2041d0301c002101da40300e102c0c3c03030310303c0c508440741d0001002d0101140c03444401d06144403000b00300030508051982c0b580c403800010b541c4003181c2c8088032640c00c29449640f2070034982da40850b0b03001c041105141d244c25000706220b40701d40c0c015003158074407590303030b50151104135101070354642d01030003210041081d1101d45030b46c034009212502c10100c2c0c89 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 341860368 1250 341859118 341859173
    0xa0303090327142709032107030b01030c0e0105030915090a0506061c030809010b040609020d0b041107020910051003050601030c0906050a1803050304031a070804 71
    0x940b0604401c0c090719030424031030b44910401d24600000026610407025840c1004540d01828070340709101000180042224140342d140d0385403494001900208445c030745020510103070240c900d0b00800c801c0040910040c5007078500e804100542140d05800c6c000741018074110320710006035007204440242d4402420500d803295208000d503845c01e001d0042e82c000e070b81e401c2c0e818070481e10f20010319480268425015105030399070b0350043c0907541c4108420113130320000143c07103000071a001d0001ca03034000140c2030000c0742074144070340827400f40d0310154842e80c08240e001030410501c10040c8212174204100700d0b010f2182220626092150780100b40d00640b08034803400c003240c0c4441d11080e4400090402900072641480b48040140081c0411103925012904009001c5056446000040182c0c0c4140d22014144036000380c0032518400360a5081c0d02410b0845400701c00300c1c80400103440194403c00601703485070b000391141550944043d0180c1c06015182c4c05100020781040c1d002e01302c03241d8554a09021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 341861618 1250 341860368 341860373
    0x37020f070507082b0f0e1215090d021f02090109080118060506041b030c030605060c0a03110a030e0105030604090b1303020f0a0c1a07080c07050108060409050a030309 73
    0x220310030350400038228803501c68002100040400e100c00400707211a5005020480f429440c0b0858400003a40000541c184803200d8900e8010481103000303038006005c00d01c840d5541c450003031500c11006140d400d6091031008000f030b0031904000c21500002d40d032001d010581c0200c0e1200d40d406030a4842c660380c03148c0103d1529440d912950305c0c0001411120000d124004000740340c2c8a07071030014901990103a0030100015441d0425000b03003840c00b8000350150301001d1500e641100241200d010303070400c050310303000002855590a8094110381000780003401e41240103180241812180c40740ba610550003481c0000d01003a0400c560040b03102003800e00b25901d50751140040e006007144c20f4010001001103042c015803003800c0e540741d5880c620035021074035840c03854404d00350703560b01001008094650084041c00803184101100182b01e40c0141000d080401507610341e001908003e09203ca2030380722a034104640d681c40008030b6003020050300c0030094002c05032160b0b903c600040d14040c003416164030701d0808 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 341862868 1250 341861618 341861647
    0x2405060304170a0305090d05040501020a0f32010c020c030601090203090316111503130f08070819140403080328020a020708060a1109010f0e030102123702 68
    0x480107558001641c1d02c3d0003545000d0002c0c80240c030354094900c5211031145846000b5004c4900f0b4071416001003170710900c0b036580c81007154000f090850341c40a4210603c01c60401c8048015207441181d020788600c000c00d20100c1e4210382d15074100f502107501c0310034030000780d40300481c0d81c0f41560102131015a8035541c2060b09031a40c8901789480344141d10000b106801d103c901c1c02071032003c5008880300c1e01240388201e02030f00c1600040d12004101c15a02c040301001901204051012034031a030000f50078801151a5140316802244107104171019400d003c240075580f00038506100c0c030a0fa00c00f1800c1904646800d0100d00005000381518403c20104034031200ca1280c24400c3c83c01010750543d580e241e440c0c002500d0300420b105605091080102003a6000341c44d0080a070000690814030342003039503490045580d40d240014031811b100341380c8054103154900380000c04107000415140002c90400000a8084000d415000999842841000340030110801c40700113441c10388100141c0c43d44a030030103400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 341864118 1250 341862868 341862893
    0x406020712120e010e1c020a15061502070803030f06042c07060c1104020319060e070e03010b0306040b0c0c07080f0c01110606010503040f0501020a02010e012405060304 74
    0x8201c00c00400303040441c0c6074041c51682046075140c50a1211094050603507003070b0b0b05500c0d02c03030b02980c01c0b1b03e020b500a41c900c2a810381c100074451040752401041380d1a00448207401550032008681c4481c020702111065182c81b400d200842e10040c184d06142030101ea03101d0001400600c403244248004c20465503894100d543c01c0f50405040e01c8081e0000c00c2000c0c1002c1d0b0b00850903485e03024100c0000398081c02001c40d0529180c101082d114603220803000c00000b5440180101d1842034550303203111030b2205038400e2070041c041040403e0340508003600080c00c030541e40007149120384c0c10181010b500342c4001c034011f41c1017a84040198030a89400e0070500a03801259120766052050078400501081e000a0000340003103c442078032400d0b404000116600300201c0181c0d5059440140480c84c15441140215030040c020744a800d8480c1482d6501401d907031011a055005070b460311001ca030710b14400c0c401c041d07041c1400a02c01c0d500d10007128070004030000301d1041d2403041c0b002200040a1100d2010241c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 341865368 1250 341864118 341864123
    0x204020c0118020306011e05060703020313030f1a061e01020c060a0c140a051e01060b040605070209060604050a17010e0a03170708100e09120f090f0d0c06050304060207 74
    0x20312800d2036001a403040445460000c3c0e200340f05500c000502c0b0110307000e1017110242c404044140c0c05003480d09004a07540404022030440c4410818100e440801c407644001540c0300d41c1c0c0701411032600e8105000380048407281810001c900c41300340205556100d00f9103001c03031300b90b4410101c0d0760300020050b410180c5031401290032841c00180012040c2c1c1c04a007001c91184a80f0101d8503403034080300b010341d4a896612004010740d000100041c03004a229001348600030380000042005a00c0f60410300380c98120390700c40070200c6c3c17000c42c000045182c95614030360702c410183d0702c440c10710f85428000313038030132119110320b2150a20052a01d00b5a10003900442000c4c16800100c0e8140b100c2d92030010400400d5807002c1880f00e00c144045240705100705034aa0040c880002d15088040c2001d4142c0d41c00280509800303424881c0300c00c0344031811041c101405816074588025500c5410342c6003840340b8000081e010a100b0727034640d1a007200140c0807404c2c02055800c146401602d0390358601d003190092040c900e01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 341866618 1250 341865368 341865371
    0x1005190b150307050d060902030906040206071b0e150108060109140d1e031d010906030e0c12030a14090607241418030a0e0f04090803010e071103031009090204020c01 73
    0x7040807554001e401000f034176503032100c10480b035580c0d090350200b28001a14184240e411400c04203000d031801034003a101d001d00880011950340e14044a000030780700c99034000e09000d080c1da0200841d41d080702d031030800010028201000749152400c0000e0020000d1b0080704170310200c030850f00219442d40244907030741c154040d031582c2c0000a200500030180d03031450b004030001002090309030414540300c03444450700079041c0c5a100000b410880250b000d084040c80c403207000e1085400c40141940c1c0c480324011030401074805180d4442411100400c0c3c2c0428189800d402481000082903a440c0c1104590503660014022080c240c200c0030440c003002c0f0710158008426050503c40c00e110b402018005005984496804400303a4a40c0790298481c0280b4040b100400c03440c1700e11032600e0910003015456008002e100281d040d0244ea1025441d4000ba04090705039069041007100003500484601c08000c850b80c011819880c01c5038a42441c0c0f02306001e52401140c90300315040454840390151658103407080d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 341867868 1250 341866618 341866621
    0x9233706030c09050105030d080606092803050c0a0b12060102030418060e0f0105033d06030b09070b030711070b0307020102071104050709140307050d03111005190b1503 74
    0x1400e16000006010f001d20740e5241034000a218940006c00032070008041d20b410403280d5076181001101d803c10040705402c0045040450140705650001c3c00340a1590102c07500350b02e0035400c15500e0300c103000d440c1c136020720b0801e40c0500c085240081607030540901c850074160260f5800d00101e05600541d8400c00110786200d0b90618811140d0300910280d8886920020082d501c01c00c00016010017807203000d8243e0407400b542d0100705d040000d8841d24090b0460303c1c0300441e0003c1c21864860100e210381d0101c40d41d54038800d10030440d01d803401030340180d400340c0101402e9080204030100d5203c06031030f500c140a2580b5110000c81c000744403142c001c01c849016a503d030f140109029020b0f40c414403044a8a80d0351070303064081c41c5840e206240c01b40b50155140822941808d06c254038808003404015030510500c8800181550f5018015014612075035a11700c0d000c046c1c0c5011484c04003003e400c191543d0800041160008865034211007000070001b010501c03111000200c1e102000007007151182600000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 341869118 1250 341867868 341867873
    0x110322080d02100e0a020a050f030a1e02091f06081e010b040501020606120319170114010f080402010c03050730110a0807081e03010923370603 63
    0xa099401600c08980600c190f100c40341c0011303101c071607105d0000e51102e0740b103000380b1040c101207a003541d10500117400ca41c821015510350501d0741d114550300d0410900d45040341011400c0642840c0d40015600064bd520600c0d11081c28002c040c490048074100301c0c1c600b000a01840030072000b040410490310642005503110a4443e0b075990003400f0341c0740076102d88804100d56040c036100351204c102840d009141001041150032030342c416800200c5007080b201641181c045020b03401014005e0944040c891802c0107131100251103d40d0103000e620078840740b0707010040542d811850010b82c040c0c0c54544903a4592440c50102851036880c000b0010522020007140300d083c244102601d08820300c3c0d00c0340890b0012000d20360741c2d5640c1e0f03040024280780040c81030100041101e006401080c60480b090342d40f00c00c0f204050482e0303401c00d902c804251307038403030301c800e180000c41c250184180385800429403c00d203001c024400701b140c107440c5403021401e00840c0010040e00d04841107001c0320040c280611400303a030ba0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 341870368 1250 341869118 341869123
    0x150f0705030d0b100c0605060102010e03040e010815010e041e060c031509090c1404140906010303030b062110080109080304050106240309030e09010b030a0c110322080d02 75
    0xb68010044107103407010b20a840d2900d0000e2a52540c0035613107005040d001a030b502d4001d02000741c6098195921200e094000c0002480640050089290007410301c1d850100d44034506554107401180300400da80061114091580c400742c1d2146d089440715020158030f51040d00c1200324503002402107840c01c42100070191b8503820600c0592040c1e030040844035103c43d402d100710394040e800241440c00004041000c9010304400e0003100200820014100541e200140b800b20700845800780940c20200050040541511a0f54140d00c802e072140d50802500410040306c0002c08108440300980400000310712039040e045040c0500481c2c4000c0c0310034001450300c40d403179030420b0310102d409500384500030611500c0105c8120a0100152048841e0900c041c0103a0040c011802c00703900b0850300500b2000d03c1e0701c500102d28000c22469420581e01c0c60005610001c40700c040d4219020400300308900205403a0000c207455903101c5a0624680f510102400d040c240c91199020304900e010302ca955180c0320703401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 341871618 1250 341870368 341870377
    0x2100203090a14030a0e0f0f0a060908330604110d090b160207051512070e01030b0f03060a0225050f10060510030e0f06090d09061409150f070503 64
    0xf407814000c42c1c194102c01c0e00d403a8084d090502d000a880b88406074140c0c50040c0d4032400713480c00581032070241d01d1040e002c6000000141c02c1a004504206001c006140c5c080108010483d031260304608440056100d00020440581d81a281090302d03401090040d592a0b0000d6404503901c0e940547c0c51109005003c003034080310390140e82003004400000d03001407003040d010051f007005601400d180c17402c0404121212492540c0c241014405001c4c4280700c1e40d1800100d802040c0517194400e120884200060540741008155070007003d107400c2c11051a1400a90b0f40d0300125204800b58541d60900a4000407182d82e2414020142049954105200300820f600109030031000580785015241541c0000340c03501449410341100a040b00164481d2180e0b10016400c2d041d5010790305100412884689060380540b004c032541d070024005202007503049816072004100b00e0070b002c09500301031840301a5900543d0f1016020f00d502c00100100112078408483d4400101c0840d552101224205596039030007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 341872868 1250 341871618 341871623
    0x90f12060610030605060a21150f050303131701020903010f05060906030303012702040816090f06120602070c0b03010f08190206030402100219030503040c06030c05160302100203090a 80
    0x1c1c202c1903100280d2081c01030754207403640030303100c0c902d008041c82c001c8420300c1d0886100100361010420918507540351740900541d240c00c0c485c0024255050510103621201e0716403103240300b40d104100c07101d0307248090303000c4004036020307040d44a200c40208695240648105644598154600340c132010000040740d001a0107201c007900c40320140d64405040c180d40b0b01c0280103490380d00842003450000c0c40303010030a580980307800301009414155101c3c0010b1501600350924080040030f00c0b011301c4200c403070348119000d4201036481400420b00d8004201107075581150003611007500000c60006200088803018020a41c25499550380d69407100c1d4500e142c030140c05088114040d41880f00345e002c00e0182849840d5030014049032450b1607035400c120955003130b102c2c40c5d01503020b20011042443d41d1218184030039400303520741c0750741e0b442d240c50701116618880e0000000d262500369510150b40c0c0c4a0155242e4a101c840c019511034942d0800360329001c3d0080700f0740c840500000030071400c241e002c10310006091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 341874118 1250 341872868 341872879
    0x160306021b011401030f0206360406050a050f03011409070f140603071b020907030b031513080703120f1e060303080c0f0702030f03070c0e0402010c0305090f120606 72
    0x81840d41d1400d0300c0c42203014045001d030400051020400652060710200d00c004d100520708801040c3c040a460100c01c10041010030102c041c004140542050180403d400c503000c00c0440d00307080008464208900400340250b12044c0c50b104140c409500240e08544080000b460341e2804800f40380d41d910180c0a000e508500020002035001c1c0f03400440303910500d005101c6802d5036240b61040b074034003160460b6030207d00c0c1c1c90300c6505c015803a00c02c030302c07401082c4039900415030003508010f05142c000c11a08607600c0c90b40600800c507800603401c42e414910340d4450305990b43e440103401c0440d101140701e1a143d42d1180b60201c1500d54035540e500c2010881e03a450180c841002c04a01000c044410b01e11024010902010020b0440c1e0b110b00010312804682400850401c440e607008240703850720f260301c071900650001a400c01440101d00501c0000c110503160b128007881e140d80001c2c9080c180060050900801041103203040d43c9888000101d00b07800b400c42d09081c5114942e59030b441d0000e0790158042c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 341875368 1250 341874118 341874157
    0x1060e0711060106020c0904030201020910020106060e3a0c06020606040e011b0e031002120108070f03080909040c0e07020616051608220306020901030f020903060f0916030602 77
    0x81c021032840d0490300c594000c2c141c0801e0410030711580f060001d200b14115542000300c1c4849607540038480303207025050780c00022141e0034181d028040500e800202441030817410b0310340c0c4030000b15104040d20f183c900c800b40100002c0741e030101302680d50040320050940b417020ba0041600c0b130340002c078144a12000c0381c091005800000d029802c03900c042000c0c010142c3c40c00c80581d80710340502070f0681c0c0000003504640c4102c80900421080741c200000c00152801a00010801c46904020020190202e41450b0820915550f2201400d00c11155100e004001060009d820700c042d441030b4000900007100c44800c01d20f4054002520740781c0845492581018402c81180d250b885541600d640000404000407102056100d1840384d8100c0c01c9080c50720404504d1072040d0060020404008521410026854408800000d0161490007004c0702c1c01c90300c18410003d9560700024015003261035101c041009442e10500d082c00c000345c0640c0b80060003501c650000410510758003d0014001d05940803030f00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 341876618 1250 341875368 341875397
    0xa02011505180714040e01031b060221070c12030f02010e19050c152502090a0f09020415030b0c030c0a1b0203070f0302090f06030d12090501060e07 65
    0x8a45030307000c0c1c2500400d4070040070000e16a00c60806421200314188100c191080c0f1460b02c50507800394201043c00e542e100010010060b012004290a100340c5007001c44140c240840295103101404c4000821102c164100001c0140003040b9251113401400c81000c41d034682c04810b04510001c01d080700003626041414901900c1881100c600f01100d0000d0700e18210180341400892020070070030b84640c020f4400600803640e9601c1145100007046545540751b00e00d42520060210901810b40c0740e61010084660040c0e4030980f409502c1041c2071700001300c620503004080001e00c80b0b001c0003500186131001a61244980e20030b040102e9104141d102504d036601c0c1c07001c002c0c3c0d00080d00d20041041c03084c0810001c82d4000c00740c0d4140519000804180c1c4078030350f0002841c0040c3c2d603205190242181d10188250b0400030300103a8071031560040c0c0c11190401c1c801007079a40c2c10f800b01040c00c0007001e18901c02500d1682d0000401e0304c2e0464024000305850703a002158030003080c0d41c60004142c4070001c0322070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 341877868 1250 341876618 341876651
    0x220306181b030305180406211a070503010324050f100b0403080307050702010c05030f0d050a0219050921010b0a0503120d05180a110a06030e190c03020306010b0a0201 73
    0x1030b250305644460411000143e403d204020b640c03c2583d0103a200c000101c2c078030b1948080b8011b11804e8100c100803101c49070800c181800f10b0020000741844c0448200f0084540080442e41101e50020a01d1500403000020860403581020f5024400e030030082400180101060340324090700540b200011860b944001c082ca691040e440000c001c98801d2001910150040f4050400540103051081c000384203076940c1411130f401f1411f180100ca0b404240900600e070940b0031142d11103d4044c00f180b4064480c0400b02c40c22003548204402c22034000707442505515941110454899001d043c0185a0181110345000c1c2000c10f6010303000b006114000242e900d00094010035040f00804103c2c82c1c07403025118240a0f150090034900d80c440b19081d032011081c410420801c40c640070b00d45003140440041b04001040d840355006404160800405501285020070390640380003598514000c0c0c801585040b080d03103580ca900196050049000004000344100001d03c9603001daa4020002051000e41d542c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 341879118 1250 341877868 341877923
    0x30615030903110a0b0606070507050307030311150c1b010e010f02090411271503090c010206060307062c0307061e09121e02030709090506090a0822030618 68
    0xc0c140e0a1707000c08204c441c105040182461406801510303002919100031070300e040484e03072044000807500c034081c07003c0b59824012140c0080c084001c840131802c1407000d24915004103c0b128080000c07406200d16902425440f5210305609030009003c20301c0032040c15402500500011800365003000d56600609502c0c20881c0c4071200841150190988403415842030381808220098010068480740c50001d031451016510515850005090078190600020706001025110b180282c1c040101845056004802c080c04004040e04014400104045c1c041c800001e00780019014000c43c0710104801d03521160041040c1010a00000c48840740384088845180d02d11039070b22492100c000e00b400044902416054546902c00c00c8108610b140c3c0019080426a40c840d400c00f5648540b0b03542001010b00865903c040001d0240110091503180c1c04804d00c144e11403082080205850346509002c1280c2c003030051071b040403041011021200a041c0822003c00003036a4244004003040700e11504c032041c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 341880368 1250 341879118 341879123
    0x40b010e100507350c070302062703150c16024f0e011e020415110304030f0c0801050408030105091522060b030a090201200a080a030615030903110a 65
    0x120000135004204c44801c0d000400d02d018240644200000940e0f6400081c0031450251064907420081e048040540c1065903941d00303000741c020340801810f181c131500c00c050f0302c241200001030b911140d0500785034582c10312001c000d500c030740e80301342c03e804003560188208100501c09604002c03648080610203110341700e15100304994030342e080103039940c91401c2c0c1045165162140022810380814440c507000c1e15250b140c104c04541d4007182c10400f500c00d02d40e68865000a500b05181484071800c0840d480380305900011303105031000c8400d9070800010a0308031004000c108001c1100e41407520f0603a40caa070081c41090f100d07000b5178001c00c0001c3c0501011506052000b050b481104404008404091035000381d0703254282ea4030302c00040c00350b040718019032180045540c009404100c0384005040101307201c1106491158040c0540060540001e101c865945c200c40c0d8a62221490b03c0110049c01e400d4202504c81580c440304a440d8a030103400c0140050321a89901c1d5005012004459448400c420007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 341881618 1250 341880368 341880443
    0x17031213080d0906020906030901140109110d050907120605010302010e0f130e0f01060305010506100305012304020706020a0201150905160507050a060626070311040b010e100507 78
    0x1030b5107003440d10340c0c030800c0380c244940c401500382969000001c0d0b05801c01c03030707200c5070b6a5155650000d180203007509c5640500300041c0304000f603081e54070031502e20707004959103900243d07a20004280702c01e008000700f400a0904084904840c01a8035000340501428842280428920030020f08a40b804449030548c0e40401b07800d422152031034a0740c01004d020004001141030090702c03c0c801e0045007c0c05200041c5009400205040c109481800141c8603240140300c01c151030a80103104040c844101c07601070003000e403407081c5642142da0009000384144000244154400501d002d0999010340000401001902c01c9034050f5a8545100c070039220221003420b80654000c0307280c140103000e0300140c0026402501120429542c95540d0710441d1b0080e0042000c480390040030a501d00b0b841c012001071a000d00340600605403440d59070b24200b0401c0240580700f1a1074101d00c00c1e60b64800d4010b0700c00420010301e100280c40072418050301e5584103d0017940c54207d090f4070100c0416461014001807031b01c1e03904 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 341882868 1250 341881618 341881627
    0x5011e0605010e0d110a08030a1d0f03071208040e1003110103090507171212012c04020d02040b1504080f03120403050306010c2109090c020606040b0a1703121308 71
    0x5584117900c1c040306003164018008200455222010009040385c49000e40b204140320301c1d2051584010b030703070602e1214880e1540f41c410314142e40300030440504a5080e6000340c00c0d02410b520300808240140c0d004500b682c00b00c1010020811100e41e5a04101d80c060000441d1181d40500110140c5255a02c00f030306590040d8010060703440020700c6500c1040900f001d840d040340f1056010071183d84a0340c0030040310380300c3e070303005200043c00b8a8a029054180c4e90548102c45181d90710051a07500c01007019100d84a0020749905645440d040401050f0740200004588001c0714014101e942040c01814002e1040d01c401c4180d00c030000048a03003200e074440503c4080c1d03480303030340c00c58641e80b006260504021140b031104002030b04002e04200317221494003e807088140d12138001172010030b03e44e0002d03611038107100c035021840781c0201f1100d8205c00306440100740c0028500100711101e250342d10001c1c1103e0390b00b00b8000100d20100142441030324602001c40180c441d0302e54170500c0c803c5a078014164000820 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 341884118 1250 341882868 341882873
    0x11090d0b070c06140a14091c030603021903050c0105040b0304020904020d0506100e06330c070801090605090706020d030902010318030f03050c18010c0204020705011e0605010e0d 78
    0xc140c5544501a8035000180104a0b42d4003001c2c1d6284070941d4400c4041d5500f40701c1a00240e00a440321040740c0c00c80406c46160a0040c0c659441d900841b428603546900300b8006000c1c0b094120304007840e006060100f405071442e00d060101e406901c402c0e21540184c62880c01c0d0fa40c401d0040303070211070860303030098110f0b102c82d000c0060000020380200d90080176182c2540015a007403180c5449580c0b480340c111020f520381094102d404c04010700240c4549a05001ca80c01c5415050010580c1c0c0d20089800f08821700c1065181351034464a40600001c0c8540c0e0b80003d20b52405411641c1c80d184030303d20500060311429155590750017140127102c05070b040300039008415803182d400b4000740fa00500d0041a0300703403103200d00c10448c41540b401780c000030000c101e440ca0040d0580101ca8100c03c00c401c01d5454a5040103804d61401d800c0c10065040010500407442990749503019a026190060003c000068070a49030320410030501404a0703606003450800100c940c006c201c3d0519a40b0041e220248020f00359 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 341885368 1250 341884118 341884133
    0xd3201151e1a0403060f0b06040905040f060e030901121b2636120c0a0507080a0507060503040c05010806190305030a030f06050d0f05070b0a0f0311090d 67
    0x1c0410007880806070740021104800707010700c8246481d0355000c1e07a84504500700a016a000054480740711760401d640c42c100d40e118881103c0c121031100c2000981500c4514200c01c44201980c0081c1047d8284072124040c000d02200400b8696000d0700d5205079400084241400d075120030b4803000290b00c40e01844080c076801405050060b4100b05002c04040b139035a021514140b40c03e440c981001103801425120100c000051440303800115080740740140c1d41d000629550380d444084012454001062103d4140b000300282c00842d54840266040781d9142c601c1e8550391910400c2c161070301d2107869030026207240070b50126401945c1112008001d68105801900d103c000500706941142c6608840300b076000614400c040518410400745642e0a0a141d0050607907242500342d50300300d0700d0070b0740c100311a40d5040915002c10368030011590740c0d520507040c07a40c241626a402081102800640000d5083d070220600d00102407a41b410404011103080360700c05409507400850f00010002c41510224461 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 341886618 1250 341885368 341885399
    0x90a080901020f0109050c21060406020903030c0a1a0124050711040c0e0109140d0f080c06010303020a022106070311090a0303090e0609040807060b0d320115 69
    0x60040301c3c501e0189010703407800c40d100303e10180d6060300305c0c2298070b106240014690081a00307a001c00c089000c10f48420503161640030307000810440e0300240d60405502c0510540e071859038070b0f109403100e01c0b1036400c01d00c5810b2171403a880c4500c03920900001c1020441108a80741ca110714090950f0b80741c61690342660b50f90302850003034030307240508024103800390b4950040d04034840c1c3c0b07540c1d108010725808001505e85101e64102d0b070800740350030210300d05075107441074042015900101104110451070902c080e81d03100790b488211041c0200c50002c010b16070002045450355100780c0c1d81035284000d00383c01004da002807204c040d200c0e41101006c251100e104e5002040c10b2800e615606240c07020030000104400c406030300840c08250f20b14810004600311002050740944159810812403600755516041c602c91a031009048694688200510341c036440c60b480542a440118403105451002d00c0a1122584000140020440d810a0b00031500180030f80188103200c4140d01032498100b901366001e1100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 341887868 1250 341886618 341886637
    0x606080c030f19020c010e010f060b1819030302240103021f0311270301020a02190804090930090b1c05010b0a0f020601050a050d030c050a0b01050f0108090a08 70
    0x2401c030070f008a0710403920040101c142c480d800010380d01110b80c119400d581100c0300700d101d8985004000c01140120004542c62811440c9001d1000d030004400507071201c03c40c4560b10710081ca0440003004141d00080c14400d1400a0006e200b01c0100d9000041c69814007400000c0d00f000b6060000b19940301000f01da8405010700e8100401c906440005820305078220304030403250398440d80d0f00d1074084000b00e129804111030a0313000358500054500e01030343ea8036481c440c440344004520b4003e0140044502920082c2050400078013810701c59040c5890880005c441c80c000074100071112191981c540060343e04c2500c415143d202c40145040c01ca8010341d0000d2503601c065030016201024141528801c1c02d0103440689107143e182e07420b041c1c0040c94512803502003010f550254006012603a41c440c060300c1120000c03a02d00320480940d25044178101e1480400801d940310348103020b4200070400280c13074181c403400e5802c07900000e1000d0046584800565000520b034000e50000c0e000f01e00244c0091400c5003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 341889118 1250 341887868 341887891
    0xa09020c01090f3503061c0b0f0601080606090d06050c0702040509070806010b0c0a120c0b0703091e03080604020a0e03030c0129060d090201121d010606080c030f 71
    0x8490740c60380b0341d460505030f03030440718141c4d194403020a022003d40e8244000000f070b4034440444440001d070079118400036088034070403944229080c1000c0c0b40d06051820309a400f05112515003011031007074042c18820b84071030b4049480d03280003404030708055082d00d441c0d00d0000d0004c54904e0b41c58aa01d001403c01518031100158100054000340c1c4032400340500460800780108a01890700071401d0410006800c420031103c01004900000d25002907886002900324400340c0c05120300310ba0903a801d10f21046c00802c4030728400b08200c03001ea0154046040e03a801202d17840e004400014444040100d590360040124945802040107030078a9405010f4902ca90b051102c2608148000640f55400005141081e41c1d1595111140c00b100351314060412091040310400b2058400005010b50080c05903c0e80d6942e51140090150380c4200007111011b849401d003000b07245504030203010000b003c558540c1d10341d800c4ca0070000d945441280319500c0340642001e81800c41d06c0340389800c507000b00c000d04041c840e071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 341890368 1250 341889118 341889131
    0x61206041b0503150103151701060e1602011401060c0303110f0c0f010e0a02010e040905340e100b0703090e0a062d090b040e0a0606030b13020a09020c01 67
    0x207014a403694851041c0e4a400b51a0324110f1400003001d403554008904050034031524004c0c005e000c0d480402940c03036642c00c2c1074402148150541c0180301c1540902000003107403042c04120000c0c40e0f0059803140c0b0560090089801050507110002e03420310594000803034061851010034070a41c801d21408640d02a010f1509400d2201d11501d50442d14168007160414404a10380e100d00348039800b4601001006081100b07440d4002901b40011034200602540e19075444a0800106025540080c2002070034251555800c485485d41d40b01c55988401c03a41429401c08100201403881241c8200795120780c10010906101000e4410741012804a003806406c90b004248582e13210f01e841c0c802e4005010001c2d8131071a0403160303103440d60401c0580100d9118081d000c40542415071410054070300210000c42c80144000c00300d8000c008030000b0354441e005a0114000700700403a0042d0003140d000b90981c10b1741b5103030043c506451209850303000703601c42c4110108220314040c0740c0141020b604140c0000804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 341891618 1250 341890368 341890391
    0xc0203220909050c0901080a050c010f030e0601080d0f11070308160b04210806030606120c0303030903030106170705180a170705090a020702011b0503040b040e071d06120604 76
    0xa0354050b0b08102c0b00c80d001034901491a04010054900520000c03001301a04410303519020348403210388074203c0c10080a00082c0c84542d00a800030440c5201d07086c05c40d005980d456038000d49031605105001c002034450100f01c00c4072841020107003c101031980c0a4601c15142d551601041c9d032003814020b6004810740701a41c0401d0f036503051284640d00072090a070030520402e801c1115031034110302c50000d10050409114160310300284087d4042070a03660801805100e00e601c501d80b151070940c4660503c030001c1080f8550001001941c100d0740191168000301c01003070204520f504085849400003481400035440a0246035075014000e48050800310b5010b488004141d0360031441c035281103141e400720b00e00704058102401743c1c9a100c210070b6011803c1c5510390340020b0240740a00a010318200f1400408402c2c04401d2080b50020205818200da44e00d075a411141c0f4014011188040890054001801c400641415000000c60018580780c680440307080254204074025042c10303002075549070031400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 341892868 1250 341891618 341891621
    0x30e0706050c100903050307080a020409020a020102070606090e0a0b041a010306020a0e0105090f06070503090d0c0e0603121b0709180b10150503040314040609080606040c02032209 79
    0x1402566445640d110890080c55180803036503c000d0720341620300865000400d900000380c9400c11482e150001694544810f0103000c2d0080303811041c03480d48001544480300b41c0560061071842c1c85200180710315a5a0199541202c860340b107082ca0f01e4000480381000110201144da0348640f0500100010212012401104020076003040b01c1c4117500299a02480350000c3c007641c8408400d20342a440c048001c0f0108503180c00101c01c0c180a002c001c5440e40c1048814003d442090314080c2c551590000d180c10030340092085403003440c200000107800301d021404c0200d8009562070202d544c0c1031622060146a0856014072014000340c0d001e81c0300d01103030443d020b02502101c0840d00c240c8035984105400d0000d04a000a051007a1a1801a108000f5052022814914035042d81449612070742d540c2010741d48501c00102488644000240210701107400c2013201d02514140030440b481907844c0350510044036928a42900940c1c03050022040b0113045030142c8008030f00a000d0b49070496a100340950 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 341894118 1250 341892868 341892883
    0xa05120f090f010b06160f150b1e150711030a06020c010608011e0b150706060f0602030901020601090c020c0a0e0901050903041a0a03021b0c03010c180b030403030e 72
    0x18000840601200d14420030120035002e610000811031030303120f84005081846031b1001c9505142041c10f800c0240040411280c00710b03604107924070380710301e5400e2080000348680d2454610a003d0300d1100d92540e11038520408514402510004041d505400138814035007102000b102c141c000c0312111040d136202030000481c16807040744003688444010800c0e45c01e4500a400c2000c10741e2510f900d12002869480100d08041031000c0d00040584c4001c01080080d07465591000f0004000038000003040050f03030000c0122420400942c003910744401040341c030391007800c00443c01070380f01800612102e0110360201d00d56801600480d081d400c14600440d4030300700c40313600203c05141607000b0090070389401c1c06907a5014524401070f514140c1805a52002c04c0561040001c3c1c610340810044e18840c0281d044036a03400ca6188030781519400c031040d15540b219449a424001d508210400300d101d802440201060300041c00203036181c40c18000410641c0d040100141d00b0540c507546900440b0b88203000c0b06 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 341895368 1250 341894118 341894131
    0x501210c0c060b0d080f0a0e10020706090b071a190c0e03010c020309090a0209010c080f03191b03020304080d060815010f03080f0307111209010908010903080103080a0512 75
    0x7120034800341c103101c002c0341d059000c01405400f000742d8031800220520b0458680e03103a9055115181c0c0700c543c4080700c03080401600c41d030300046001150a8050b40009000c8203d41040d6a401c00d41d9490300a44501401075200040c074100c100c0450101c0180030000040d4001c15240900d092854640c000d54183c0d6003412800d0042500f41000c90b009013404c1c000c0c42018a01400203510f404401008220340400090464202c254040340300001c680c86124900c0c011500f040d0075a448620045454003194826039440b64580703414024440441c0312401001602682c001c2c101c450a50042c6d400d034007940c030040040740c200c5030401c45203041850510403c8042c0c030110004001e03a0813803200c25190710034113030407811181d0f22aa07070820015100d2001c450b801c1c54021011900c0c1c1d1649a001c0d03900d0f5080848421031402145846a000c052400162010500903603e64901c030355244003940c2212080000900020000e10041c004280594007c060078080da1a10910340041c0c3c1202000c1c2c1c0e0002e5950 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 341896618 1250 341895368 341895377
    0xc03031a04021c140103050a02011b08040e010e25051e070f051203090604030c03021006180b0f030604020904150c0f080903120106080901020409021201080f0f03040501210c 76
    0x7400f040e0b100d48203c1104000801c1c007602d0650441d01c545a8807410030710001d041001c6c5030308068540380104070546105500200c0300d42c45d00e03110b52150103045001d0141d808a4000c1900186c0740e400c456805515024241d40c4030031030400c0c13240048170582e0017004100a040311900d803c100c1ca816610060030800d0045845140540300ca1401c0303420400c80c0302c5d40b1070030424103005100219002041454005604ac104815107201510b401d030300740280b071106010381924022000912000c542c0c2d424401800607801004007014a20420160718100c2169a0301544650001801070a00a0149030024062251120700c2c0304007000c54019180d1015902c00006c926510040c41036400c4083d050304408200c010310308220b00f000c64940c1141c014401d2004002c5250302007198102e0a5040741c02818202c10207540d1105074480741c141404081c8260480f51152400380d001e03481700818001c0e0503126400185141034a40001180c0c200c41c200398991003541040b12804074004c1c0380c4500072030440d43c0c0d00d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 341897868 1250 341896618 341896657
    0x405090411011e0905040c0e030114090c010c08030a05070306080f07090c050c0a02040504061e06050f0a060504090e0c0909010c14090a09020f0706090b0906090d0c03031a0402 77
    0x4000c02c110f40103001501148400b800b9600744c0143e04101902c500b5980081d10b50316542c800c0381c00c09007000003940c040d481d00c3d200852400620210074840d11400c4111a4a01540d03001190154201c01000d00788050605c013048424045401603070f00308035613250116106441e505014141316800f4003514180d40202c01c00c01c001c410b6402194240501030a00c142081c403069076071074403810341c00c10081c4075642d580000303001c0100710303804561126140c1c4121152302c00079461904c010401400781c548580c0300154a1021458484180415140140d84417824980f03441a80809400c05c1e40c40c02125009080319090307162a422a030604c110070000000c5a08140203d000c4c202006881510300b07031030401c0101e48269129190107508981c01c908005035189160140803c03103006140740107184608002c07505c0180035501c440c8600452444c0706440941e10b80d218840e9646501502e148007140c040c80210300070038060343c040c0f40e1070040180401420100100014100d83c003480c3e002020760014074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 341899118 1250 341897868 341897903
    0x123040608010e060108040c06081009111305090c120403020a02041a09071404050d03030f05040506061f08010b03040321021305241608070b16021c030507020304050904 74
    0x6555084a006e0800710b100f800c15072074880f110004c07405028248542e180105064041c51880c0c6c8000b0100fa5400b000321055540100015504c804105000c482d8003000c0840d42c2d15000c0107440c0601e00740c0c0300c1a45443c80300008aa8064401041a0706601900c00302c2400f680300c50181c4002044880081602000d551081244207070f0064070340c1c0208418580400101516141103405a03a800ca4002540180c41d04d021005800e210ad005100541064280410000006000c5005000c12100a00304c07080200341c008549020304904000501d190004100411540340110707081b07400f0746028400002d00d03d44101258440310000c1c0c131820350005094105061220381c4a0180c4000c840300e11081c6074091b1900301040c1400900511504000f481e06c120f0114581d0880f503484c0c0c00031020f500e9128a051842c6060000ca6a40103000800000807156920200328812003a10816400d400344450b06011001082c0c01000e034020351200300004031781551131440c3c8900c46c0c3e21880383d07070758041100c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 341900368 1250 341899118 341899139
    0x80d050408130b2d1c020a091d04030309030e120d020f0111030a0b0415080d09051c120516080403021003020310060e04060b0403261602012304060801 66
    0x2035004540f125001d1148108101101c82030f904c031030150741032200b291082524601c200d803280d001c2d1481610303140111000380100640251043d5403403030b22100351055403500b04c04040044040829103050290000030300184c0aa44040740c11030107454500c2c51030315807401088010190801c049255840029440f5043d0707810820000c4045504000b401002c200c2c100d040450b00010b400a441d81d41c980d049603039192501d41c810308400540201a01d905540c03080c90f181c03100062520700b40044c9070310002040c1800e10280c0840301484100c1c07120780007013894480d424004c40c800526810848108600c1d08495201d10b514100c40b401a100340e5a201c0c950b00c100001c000b403030013a00b000d05005104001021a0700751681e030846180b410280f8402c4124030001d00140b07003507003104404a07004940401803101907001500700b15500000b809101d6050000e51156000d04240600052041c001810055124150107102c810484c68058940350351000070f449281c102d9041200025034480040202160f030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 341901618 1250 341900368 341900407
    0x50c090109021c110d1407031802090a0903032004090b030c0109060c0303090b0f0403020c0901030206041e081e1e030301030303022a0f07080606060313080d050408 72
    0x9140440ca0151980d42c03d100a1080d0481526595a00c1441060102010b422240400c00c40300f0b0401051580804007000150180d42c1c6100007441d000d2403015070b803c640588444a900140368100c1580e03000c550b0b8010f0483c2d03c40480405884000d80d01e4900800a02c46411320814029640c17078509001c0004200c032521001d8902c294040c01c240c00030360360440300c2101651400c0c81c00c2c004504040c01d05601629a0110040052440e0b20412a01481440320203001c0c2c0d20035425a403602d03065408001d4003080a01002e540b1240030041044000d1407a03c0725512104049040c0300f81c1d942e1080c44604114032031611010003c0410070200d8070303c0040c00480703000c418000d5441082c81c02c04400036601d0105000c000d040c580d0000c0d03800094002140c03455002580c128807030804088007903941d610307200d0340c0b44145001d1182c00d83c003095001c40803903050311840340981403030b066507a0245d6000320040074401c181c030845c80410800001c10719074011148140e010362800356485400490b20300d1072140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 341902868 1250 341901618 341901629
    0x12003010501030f0b0904060506150c061012030915020a08030c071704030c090506120a030f0f02010b030606130e0d030219030221060a0f0f0305070e06060d0905011404050c0901 78
    0x20740b114405181d41c1e0b406c40306811035040f000001349079039001c000c18441e60360505a0700000c4804201c10716640c2c00040e10600c104010107036881c120381d0703440741000c0c00c0c403214000901090f1154000d00481d0107450440b610615644111448501c4a484201d01039000342c8120310003190016200050003080d442c1909421a0006107600e05072a5859440043c141d03405011500d603103442c0455182da43d420f00d00208035614070191541001546409080d00c00307008d0580d8003080d10741135411610b5006104004803000040e014000c5551400d0030400c0211808288503c8035a5510340009448000c02c410703500d401e901d450069a0380c0307000303030028025280502e40c0c4080500400401c0981d1007552101c0c250004d1214030900700d500ca88000800303030f00e2036800040644860010001d480101c48603540c0480c0d000d042555510b50b101c03820400010401c5400c01e0b0070980410951000c00501d41c8422903090003a03000107074171510701daa08040c0390000c0d43e0070b9031140e00c5410340c0107440c50010301c0e0900526 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 341904118 1250 341902868 341902871
    0x406110c120307030f090302090f070f030501050d02090a06090c020a06060e01030f030e0f1c110307153006090b10080c0702011707080702150c0f0c012003010501030f 73
    0x200c500d41c0703290740f846003420040402c4554a1103080d9180140003000265600620b02800b074501109000a209400c803042800690100d00c2070311018040d21425044c2c920190041da03242c0820f40900c407070b66030054034403c50a030f40c074480004e80f080d003881064a8170601d60f0217032201d860141406020780d24250859000740e95840010800200c541882407081503040c01e261500c40c11040002e0704d0a4225110703540c0006206a9210360700302e89008580101d4824070100185c140365400745596000780b405400501083c00c80841d4200340507903501441b030424052034503174440c883c0d4070003012110340500030740d421074541106025141060040492008080d2025503580c100000c008190020280c503040115000050010640e4032401c6608455955500c04000c1410300c2c0c600140800e00441d100b0005010b44105581c2904040d050b80d8012160384d16118204030146e1713106200c980c80701c03109021030365031360300000b80c6100721744500da15005050a41c141c1707035850030b400907040e20702644140005a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 341905368 1250 341904118 341904139
    0x806010602070e1e01141309080d15030f1b060f0914010201020c0105180f0f0a1b120c0801060503070f03060c0c08030a020405010f0305090a06050702030f0406110c 72
    0x35035001610008803020b41540203025200d09008a00c800c01d4407000c2d481400a44d4004206400080e070445d034044819121042c0400c1800e500d401160f0540074024110007003082500035082c620b4100640402a0300c6622111968071764814521500e60700c0c0c110b0362260b500c440360369110043c02442004107074500313100c1c0e01001d05540051180d56103000340c401001034811641e0a07640701354181c03850759071000003c01c02400e0003124103c08681c0e40820441c01d200c1e407208001c010304041440e410181d40a070080c28100d1140e51540c0350700c044000b544615145010000804540ca48217080308240282d103400b21003400c01900b41c2c01d54807079800480c001e9011220410020f88041d42c40030499070407030000181c1600c5850203d070480e180c1100034140010103c00e011208400b580200100c480036210041d05d443c0c00d8209509a4008482951680d00000c400401103117140d0020b40c0e00c001148196840d0842c6101400001d412642110001805046108405200c20802c0078070a83d17044500d01c080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 341906474 1106 341905368 341905379
    0x512040b071101020c0105030f06031906152403110c030307090905010f0515031503250807261207080904240b0f0d0f0b0a080601 57
    0xb142e5281c0c80340460f50700020f80c9041150b01130315650700310707540c101054000700d40043c5032540500446c00d46110130120001d841c0300c8903104541c0064002d00c0107031800c01c01d4480c0d4020070b102808545010300c9080104199004032035082c500071402000b81c0c0c20031641030141c40b440021512000c41480032840c0c0000952040e1898a41c0c1000700b0fa0365000000b105411038402c1640202c40e440c00c1421810032900155806201c2041c2c550725520154040b074a099255040188600e9030740d2403030050178104036842d070700404804001303021050030a4254032604888041c00b0b5210708242d8030900d81400b0905c000d52044058258190711b030106424060144e44c810801c5502c08c0b4034280c5040c0c00840c04a84408070702c40c200b6008403082e0f0415003180b4459000c0e0114141c908010b1001c214014241e02621030a6440c202010400300c0f105000d100405d07106400c1200d6a802070070041c0007 = true := by decide +kernel

theorem cover : BRFrame.Cov 341726618 341906474 := by
  have h0 := BRFrame.cov_init 341726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 341726618 ≤ n) (h2 : n < 341906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
