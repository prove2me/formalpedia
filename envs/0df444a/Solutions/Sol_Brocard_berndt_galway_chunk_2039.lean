-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2039
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:32.34506+00:00
-- url     : https://prove2.me/submissions/edadf608-b2e1-41e1-8a65-c81c59649d8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 366546762 ≤ n < 366726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 366548012 1250 366546762 366546769
    0x50108072d060e0114040e0901050130150f050108010e010903021b060408070b07030315060f1116060806030106080d080403050703140c0a050c1c0204050c070b100e09070302 76
    0x2191003202e0410401401404440e40101d00c4000c00c40114002d159030389071100c40d880c84528013610862000e42c0f91600000e0b02c4000e180b8060580e005c03c40e5004c03044e0941c1d2132484a8180313040d40036641003040490b8a001020b880c45582d80e4510304c072401203099858100b00303030300f1250310f912540399507414a210701001940c003003840205a0107041c001164811150040740150090303401c00e441500c03403218041180c644001c090003082b44295402e01c0300c0344c030f00500050446c03444c0c0f280e040460750010b050040e150140d0140000d850543e400c5402e04855103e0300c2c0c03041400c0d584010003107440320050101f42c0c1020300903030303020340346100040041c1c6101500041003880020000760820001041000406110b1544445154070105072640c5441c001c01d90103480e0309099034225060301c41e035243c0c100141480a140b5885440c1460050340e80c00307540c1c082c48050807000b050400d03000d404001c00400512078a42182c003410141c0480c1107040d040c8407000744040c0d4042e200c800e803644404800c100594 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 366549262 1250 366548012 366548099
    0x30f1a03030f0f07080301230102012304050109051c1d030c06031806040b070809070501090b0a02100c08010f0806040b060103091e140705010305040213090302030d05010807 76
    0x54034001c15034541500d00c01c1030310fa014462001300403c5001000041012020200440450a04481c03030794060030000160300302d44440c0031100074a11065a00741e140604020fa055106026100225000382d0f82d0b0342d26070401d6015100c2a2900c400d80140c0103505a010300c2c46444c1920741051080d40810040001e41d5941c2d2901d6482d00c00c0c50700000140400704000034a10001c0500003c8944608140c42d100d00e05003400c445020004422800094111000141141c201d40068492038580750a203c0c0c0c4541503404441107106510070420090118900c91040c00c20b100e025981714074655041007550203400c002c0d640001c0c0301e0f034014414031010900e41c07041a9000002420001840c422620700305040010801e590318211102d141e144091141c0ca9113046846841481541c0300d490716500103404886058074041e4200241c038000520b0485070b075001508143c02801100e081c1100300142000740c8000340c10400254200030b108011802c46262082d402010203034404483c01201c0038114140e8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 366550512 1250 366549262 366549277
    0x10051807080a1721010e09031305060c07031502070311071503020915070605090d02070e0103080f0f0d0902040515010e0906060405030a0614070216061107050d03030f1a0303 76
    0x8542803402d848210900500715003c101c18004c002100d1220700010502c2d2078002d00c24110a01d00d203500280f05c181010044681020620504003022424402448075a07007001031509010311543e00080003285851070850004140d551703001d41d40d600103180c001d00381401c04400540641c441c0e1400d204184e0803070110001c0c1403003441c0050300c9480140024030745440504005e481c2c600001390250510050f50400c40c8140c600d00d040796031819140c3c0c81266070341e00030310404130382d100504014000190424001d01d4940d44454156061004100c074403130041c1d21400392046120303603032840e6078214101401384650180fa08110169591150f80020b400c50b5030740d500451244500e0b40001d01551340e101c054401810014040390111101440c11800800100702c20148840840001410107440044c0d501040352868044620b0f41e8a0907406a0700071242143c10303e05409001008141a00c3d5183c1c6941080c0c000c2e940030540004011030007048400080c0c1602e0010f69072008100252000012a00b06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 366551762 1250 366550512 366550523
    0x6092306220b01090b1809070b0f04030b10030b01060311030604091a0112020f0913021e0d0308070f020a0c06050d1107110102062d090a020310051807080a 68
    0x40c6640140c00780c0040001c2100240b5001444002142d02c428691010091881c142e0b814510b00c030503200d101800f40000c88002c0036560141405100d542d80940c0500301d081011032201c1d0915490b65201c0c0030210040780c907900d07005048070702001480040910700707006040f141400c1203e080407c018125901c00180414000c47d05c5400e07007420007a01d90318080241103110409011943c5481fa10706500343c00c01c0c4268800c103a021603200c464030b041d5841c54065480350500d161114415401d00070010440c000f8041051654400b0344c529489034050494402c3c440da89458903450407640241151080e040e400003103500c0302880c040007a000501100555038203041c0952909000220b000203021288201400b115010a0003000c000342d122052200e02426000d035045603482114103400780034411075151386441a0490062042e0742e040781541c100705448140d585040050300403a00d407a071a4425142115500c20800c01e42c6d440e020060b030b00584c00d50340500306080c502000700f5a0b07000c10302c1c1c02501b03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 366553012 1250 366551762 366551791
    0xb250314060d0312050f07030b0103050f01260102040b070204060e0906010e1f080705010e01170c0d180b060114040803030103110607050708030a0e040506090a09020102031606092306 80
    0x14580a54401203246500d01c00a0000307190006e0070400328802911914007107402c01001e40600d42c003901410b03201b03201c444080e14a88e0310302030850704c41c00480c140a0000d00e01d0b28040f000030103428001440a400882c184555a1017244180801c50307056030703c00d0521070f06200500404900109040d8111007501c0044441c070348400d010600e050590410340c0c0c0c40c615803140001244c8c540801d4030b40446200340c80d026000f2160400650b0030318482d44000ea0524078220004504609910107450b0a8145680c00074902c054403501510713151500340c064030101c4070042008000d42c0d01800e00d000c4014041070550a00345030181c50360342c030301040c04002c001490083c1c1c0e001664130b92006a0300c105410404842d017130380c0d80b21010b58030b0764045002c4500085040b81d400010342014015a03014000141c01d541d065a0740c1d5010400908641704124114001000b0b42c403146514400094203003070003410000380c0c2c0c41c4c072407400b01554003d1400700c042c0382c0c0780300000d54004039020600540c0060a110030340c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 366554262 1250 366553012 366553039
    0x14010c050325020a0f0e041b12060e0d02120f03370501060212090913201309052806020301030c150903020f040f090b25031406 56
    0x1411401200342c0d051a032078542240d01ca240c2c0c003981c40d45500500940fa1400700c00e807100003000045199000da8843c1004820105002407c05402d803403042840d410703000022906d59101030260403045405561315500d9032441080c0c44814809822400303007030b00040000001c00640340c0709a0044e4241c00d440e40502000003207200e0a403c5403607100701e0100c043c0b240002043c7c2103512960001202d2509140d00d09000072401070b00001d10701e14644007031080581002d608504118565000816500c0c042c9001c5a8160005d0018000d102c48040d008610780090702200342130102c0d065a40082600e081c0c10110981d010440125a45400000440841d1102040001e00d42d80b104d40c900f00090a086c40000000180203020500e0800d80e054103680d0400010a1102110000b145020195200018004001041c0b070b103a80100c0c018031018030081001e0020ba2241209032800711400c08220030b07a02517881e5018030410307268103480c074103041c06c02005951a40071401c240c40280f000b806443c5c40303903104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 366555512 1250 366554262 366554273
    0x9010c03050907090e0c0315070206070c020a121113020d0b010509090a0504050f16140108090601180b0409060e06060901080a0b1506030a06030b01060c0533040303020301030c0506030114010c 84
    0xc1b84d010001030304a41c15018141192103100340103e801d03000500454020a00c07040c030440310b07050310a800500c000b4003c0d00709031400b008000315400803100c55400c880e1703138689a25018081d10750080710b04001030b03c96200685c3d14080e104992141d41c1049401c01620304c4658807680915000280910005015541c130310341607140003283d149148403032040400003c0c4a0382c0101994040c0c031004585040c4400b80d05005440c1c05200b40d80b510f61a802850040c0240c054861b0308240d07803e81601c01013190b81444010604460058909943c450344074100e07010706a40401072290820801e9848590303562422001c0741e00e591034040000c103042017040c0850b06e4034107001150842100000d0225540b420a0007800b0001e0007640b2084841110035000041d805004003100c00903a078201015200c2c0b10350b0085a90400c88101c102d845210049100600584a06248c00d42c4640c1c42030b14016540e50441c10b100d04e040210381c0c805481010100010300c8001201204014909020f0908010706a001d11b0b02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 366556762 1250 366555512 366555523
    0x50a08010314160e0610050705030913110406052703071503060302060d05061008190e070b030c0c070f060e010c14060a020406110109050c06070c030803070809010c03050907090e 78
    0x254107405a8400c2d01044030130160000c03901550044580304400744030380390700303942074000c0190180c641d400500c000070341c50910803101504107654401c00195084c07101c1c142c00d00c94106421010000c1c00201d440288456036520040c8144079a80c03240d902d44e107010300082d544200d18002c1150186081051607403441c000d400480c0503550040c4403585407844000306000030f2000f201d4161050469041551425002e1030340316002c0d14200080f41a402c44600c50080681403841c10391441c0d201d0040c00040c0190920301540c050507000314481c0e0740d594101441860074615800011200c2c1c42000c04000d13080d0000c0c1c008038803440a0034002c1414a031800c010500c140c910810241c1401080b042048003800f55000b8416160075031240700ba800510f04580f800c941140b0380c0285158072002040240c0d01c0d218004e0240184512001407585452b552424500d400035201c2c5804241c1a40c2800f040032028022650b500113540707000c020600d85120ba0b81d6030740c8440d00c2035010742980c40f065042d1140d4103004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 366558012 1250 366556762 366556783
    0x201050a1b080901030f090803060f01021c1e14040303080702100603030909140f0a02031b0408070312020a050c0f01090e040f020a1a030708070c020409030816050a08010314 76
    0x92040c24210908002c0c06903030050004030300083c64040b250344908114407030301444640080031a800c0d60340d901d0074002e44109011075281513119407661804440e040c0200c1e020040c445913a2041084c09240387c141910f11007090103024010258805405aa0403505940449402d450902c003d40c0b1040e409a040900840303242c08801d06280000c070605401030005d00071101690000c005050840d05010481030054820044500303942010136440445a0007454102600142c11701c00d29010454983d125802548142419045003c080041c002031807141c0310007a03c0740c000307441a5401035861039112050a1070007032140c51480c0429510f40d201c0d5001001810400403240414206810502040d44c1c400d40100d1250002c0c40300450302440c0c02285444410003405810705580780c0a10981d14804010250f4040191020781c60000d03a03280d0052504d118020f45840310300782050541c01149030b1907079680d030043c030804002002c6060b40c84948141100d40003a0a00400030117018401d040c07041020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 366559262 1250 366558012 366558047
    0x61312090e0610110d1d061305041109060c15010b0906031b090a0303120f02040b030a09023105061c0f080708030c25020a0303030203040203010f0c031d0601030f0201050a 75
    0x2c001170b5089500c808155001c0780700420001007401c1004464170486a091091500d046001c200d60300b06500000f201c41034461b0264107000c03400e004a400b0b50001401275000350701543c800f01811026800c442d001d4540b0301d41c005c1c0381051010200c2e100e440064010280305030360f862203c1006240c0740036101c00c520024400d04103c6e0341c0f410700410002e07050440070340e00d52520a010a0f150034520840b011640760144040c116075400c5820002041e404605a0300298020741020011206a03080101c0703540500c4120198120355440700d0032100700402e214081c0744032105181042443c502080807041d03114180c124800c80c1890402c215002e49040182040c46c044240000e030b960482c0a40317540f1200036070340e01010920504104002c030104601075089110b081041c40403a200c2e800841e0b0081c0050004154560000c8500d42161280052903001070f40d81c001c1d0202845592008184208042009069550440c1c0768a10711101c0030703000a0501100149003a6800d018020a030b50300240311 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 366560512 1250 366559262 366559273
    0x617100503030f04050f0604050d03080c040504061710061a0c0c04020301090902030f010204060e060d290a080303090616120c02030304210e060c0f061312090e061011 73
    0x18030ba500c604d070464000d491083e05001d1400600e03040c014151001c45000030080c0107015080d03217055807580340c090f00045001e41c0030030000c5a591568011400145900c001c800d60038100d41d4204d50400715110004014282004420403100e135101c0359000f50b51000c152840d03610740c2030840e410314210700c038007609812a0000c0000600707880c450707020f51281e60003a1b046d100070726440c1040340c0c01c03882203000d410080303a42d0502061050920402400300904c0710100024012080c1c508404080d1440c402c0e041910101301a0001504104154100400f2408000d500b1800c01229842d11010014080d12086031030164055032b86114416114a414102801700258000e8050003903e03680100e4041d529001e00050802103034003130120701c95043e10143c0c0c80e090315804c1030040040503840a04403062612402000b00074109040c00300901039240e180800300e8940702440e11070520030071b210b40315041c4050600100f0180d141c1c09501c0e42d0043c021658987c002d080107405171103480340d0039002812031186 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 366561762 1250 366560512 366560527
    0x40c030b0603011e0e1c2c0415061d010e10090f0603090303050f0108150612160305010b01050c0a060e01061517160e01082707030c050901061710050303 67
    0x11580441d46500d00142a1090200d4800040c2030030b11ba401500340c00141c2032441200d0708402600c1c4a200300030704261842c1d0140d0500005402d4508c0c00c002c2c000c0e050010a8100041d580000205682200e000b403240c2d02e80310b4140c0064854118420750500130b04162240c0c4240602c5030700683c020703115000d01d022075035403100300050003403402500480c0800e03e0000880c4480e2050030308141215038440003040e007582d141800754500100500f4003604a4000100c441c4031040502c6242c41403580c1d0121840700a19505050342503070901031103641440310800200642c5103020411400054200001142c0700c00c0d03450307041d4010301c51030b0700c55055502c099203503030601940801d07481072a5225280c624040d80b14420640c180b0034201c202040800c1610f0509802d55000c0c1c500c0396405031812440840d2017440c290b51005107505030b81075608581100d40d05200700991511036901070030040e9480d41c4158106203014003c008046080c0c00e14202500c00600e002c1c090030706a8000d008050180c0b600e4881 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 366563012 1250 366561762 366561821
    0x706050c1b15010e060603060618041d1501082107170702040b0f0f0d05010b0904030e12011104030816321209010810120c0e090105040c030b060301 65
    0x507404000b06040000001107203e50302030510f008010081c0641c2c074640301c880401000b9806076141c1d0f10a100051000240c070341d605c1c841d50595042d10001440d40d4940d000c5810b003000e030f500088048903001c50300180900400001c11840c6070280500800d1310103151b2038450b09078003400000a040460040c0c0c201c80d00007181c409851a1031094409229000c056010400d00c0500c0505a54000001c0070340301c4e80b00e2414071a280700c105cac0140e0000079220301030004518800c200715010703004240c00c103407400c0d4682030a07001c41b15980d1040e030081200301622082048a442180300181801e500481c00b144900c000700f01c105c0c60700380c0c012841109100c000c68858010b00c92226044944200d10300085000c04000c5005595083c40e8840d681c5000c001000550b00c0c43d202a2400c44a810300d4000030511407010381c0d0100d034283c0100c145000c000e00d800a8400c101070024800005a410300c41400005051155001c1c20b403a80600401e21698171000401e00500c1034010003e4060b661480d0440400d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 366564262 1250 366563012 366563023
    0x301061214040b1b13050901080c010c030302031305010203090a1a040b01050f010908060a1e02120c210915070c0213050a0e0313050a0504090317150d030f020c01090b0706050c1b 78
    0x10400c0c0c0390381f0fa06131307610384045803940780c3c610072075012404400c680c000282c401c2e070042d40c0c48414003240a5032214941c0b51107003241c10480e0000d40540c00050385601303101e1824501122014100708032840b514250340e4032503420301c041c410a07010341c4403007844e40804d0b8001c1450501034016481115400d103010140360020341102000160180d02d000c102031405480b9000b00c0d44000010703410824a074035580124010b59000c50002d2a089a8041e183c60808c110802c09501500302400180348000c0d1086800e6401d41d4040c02010511810103200001601c0d40740303d182c1c200b41400800100c569402104002500584a07880c400b400300080700107005e003040003844140c03481a6104041991144203120845000f401c01801080341410300035544001e40742c40b554881350001ca403070105000074000c162905100720085010a8078400042ca01c154100081c0301103d03400d00c1e110201d6460500c80d5612482442005081d4548607000a640400324038203d1b0401d03041c9162035001c001540302000d4445 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 366565512 1250 366564262 366564269
    0x6030c0e04170309010f0c0f0f050301080c010e041103010f032109170c10200c0603010b07140d030b09060103140a020c2103180c010504120f02150301061214040b1b13 73
    0x56480d400040e03030a40b04000f524140c50080000b0700c0246000ec00645204009003c40c0b0341c403e481d9000324888028440144d0b0080c40d9111100c8011425884e0403403451810a2410240380d154050000e0f020703500038090011100300460441108030600005814050021161908184000d040c03aa54030f43c0541e4030449030300000700d030740302500e807900c811610b41c82e1001085030f0004060005000d00c22078a401040355078820701909100070000c40420341807059400c11000881d07a1f40380c4000b41c40c20800b02055010382c0905e810042074001550445290344086d041350701c01d0780d01048640c0c1e40d007000c1040c1c0401002c4001c80001107480800d0681f1194000c5840f1040107011603265940c2c9500090300005200050316158203080c141100340c2c1e126101c0110a8600c1189044558050389079544003601d680380308200141d581d03040c144003401e05000f5450000c10586008004a0080007110805030081d52001e0061503545031500b1601c446000c03a00080000c1e0000190080103540610009c000c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 366566762 1250 366565512 366565517
    0x2070506010b041802191412090115080606101d130e07050d080703120b0603130209011202060304080a02070b0d09030e010807050a0e011107060306030c0e04170309010f0c0f 76
    0x480100201c1281a4000c140c0c0b6218240516031b4880382c00c500401c0c1d0108541809020107090484104182e80342140645050070b50b655100d400e56000303c001207110002d444d11400520f45d40c02e00768085512510000215010012200000580000d40080e1134141100c000c190224000c017180400005092800b6800d155205100e40000e050030005280e0181603002030700b060410009031401d4900b950b024600041460703231084c0c0d40e111540c0e41006503000700030607502c170306044e8424418041c00b83c1e01a00004048805401d0800050761017004480c5d1043d1320800e069140d840010f401e07403400c09290010252808085940484625154482c000150083d40c84c00714000e000300041d0340451050b5507180000c1d10400450707a81a024020030400c01c101071502c0500000100401410150b164100000091300d0310000c000340201c1080c200007074052610307a01d4203403c1070f07500c0a402143c001600d60380b0301000320001d402400c080d400180f016207000340034407a85903807810051280410700c400402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 366568012 1250 366566762 366566789
    0xc02031c031a040e0a140115080f06010e15040b060d050f1006080f1303140d060602010e010605100804052e0c0c020108150f0301020c010501061103070206031902070506010b04 77
    0x100e038034060084d5002d06001002800e01881075844060000302c101c02c1703142441d07484c0c00c50000b454a075900300d08000c180302806043d00741a2501c2da6401c142e0107038424400c800082003409400d40526907804414002281e0001e0181a0711010460f43e00555041c03040e00780c50842080406050300820503c00d40ca00d0003001007450b100c19042e2000201520740b1074480704104009502e010701072000c0f08046001e800d20010044002450305602d40c005e5000c442d810340c40d0441040207a0302400b505003003421080007170103024284001729034002100032845003044420400f01d01070220906c002001590481c0c04130181009140740b806a4800d030600182c800c0e0714040e02041c82c5440b443c4000440d990513035558038507807900f0b00791104010f01c0c0700045901050048500c051590244014030002514000105c1c9540c5030900c00741000201d08604400d40d0810024000103941318800c07203511480382c002d070300c841000e103001f100c3c028029400000c100d40300310000803070000d043c6005082154201c08281c2d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 366569262 1250 366568012 366568061
    0xa09050f03180103020f28020d09050d020405190906060614090d0206030c2104050708030a17150d0317060109030c120519120e01080f070c02031c03 65
    0xe40d01c0c802d450080301120891400c01c2c0441d8801e800030607051074142a56030900c0100e42d2503000c1204d172816030340000342c2403c2001d40c04030f4050180c0c0208006e85d00307117400240d00c0e0202140108041c074000a00c615543d05c002550050f400c0c0100d002070208100030400c41d420383c5031070801418240504008921180d0010144004440440780c03c520301600b020704d101c416600b40720300e6400103404c1c401c0b0041d0902105001c8144c401d0424562103ca403070900d07441c01c0c241070550510509412500c100e80080040c219001c2d0810585503101c0700b9000032000d030f50341c1d00c503600b0b0154501303207061940011841060028142d01001a0103aa42c110300070182640320003005440064107440001d041d140d4000c41000000d100c8001c08000d203015800740e0303031050100440e00e0420a5100700480b1581140007031008a60f41c003525600c0195002e00f0080c90781e04098840101c5903a000f00014104035850704000d08548003030000c042400c01c100030080c0303050700444002d00900f034500d060400c0a404404408d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 366570512 1250 366569262 366569293
    0x9080c0f0a021302040503101d0d05120c0c031b01090b091006080607020c040902030a080c0a06050601080f010e06130c050c0610050a03022b0c0e07080601091707030b0a0905 76
    0x450445900074010000b02c081c041000009e0a03071034605401c848400202d141d5260005d010300c400c600103560715a5901c400d0340403000358141c00030341151010305043c04030f40c140300707000012128804110003802d402070181c1820903000d401101c0004101842550034003038407040014056800c820161010301c18142c481210aa482100702e5031640140d109109015581c180342c0d025140060015090b6540500c00e601c1d1140a540240400c1407030343e00002c40c80040c05514800c503a040082481d00346440d0600c0e0f4168421040180141d07061480b0050200c1e105941f008d50712103400800348800c0c88282c7d00c88202804a8000f545841494043d0200080c0c082020120080c01e5440040030315003064150b4007408010b0006034580420b100b00d04a1400300d26030740b0a010406184203d00c5544260300f0190207426060001c2c0503c400d20401e0814400c080c0e2f000402007040d109540311140707400044480e05441c1c40020f50000c0d095014602c00c2c041d02604581100d030000b4001c2c02160002c0c1c4031907450 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 366571762 1250 366570512 366570517
    0x32a0b06130b010f0302071b03080909011203050306040203060301020d1d07050a180c020a0c0803250c060e010c020402210106020d080f10030618030305090f0703020409080c0f0a021302 81
    0x500c0c3c0014003408803444414080d43c06881042d019032800081c1e06002030700b0040e48810781c1c00a445000c00030030503503a2841d01c0e001607030140c030385400c44403104031948e40d000e41280403b0300140d11440d00400000c0803903d0940c192400c065603003a0030302c1407006403218040c0800c0104100e8a050007920808181c0781482200c4100b21181528002c181a1500412800401441c14041e04500895068101181c101803224020b400d0084c061540c0d26409200f0038140d00070203141d421242c2507128004086100f00201004481881c200003554111200040300d0400c21440006c1d44035102003600301d4040041c0c0c19151500c008103a0001305030b600e526069a40341000040880007810510009110a400303040f229004001a840c2e210601c1d00da0340c90a0a80e40060b44555003a00c04504401c103250385401030540240c00345001c6c0005c0c0e00300b02403541c1c032002c042c0000780c091601c400501007000200c0c0b0807680ca807a183d900b6203407100410203e5980300c114a03401a441b40148002c800c445401d603108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 366573012 1250 366571762 366571781
    0x30903050705040b1339121802040e010f150311010203160f030210090602033304200708040816060c03210c05091f020a032a0b0613 58
    0x80c159030360800000c01c0240842120098003c41803450046d8003c180c100e10090042c03603155017620541d00752100034a02c6209200e080026400c0040300d0745d680400040d4400e00c1d40d01950040307914440343c01028050661a4201c80400c0c0c5000e00224440040c141d452084e40c0c4100c15040488403502c004a989010b2585400300400340d1001200000700803e6202401e10f200740141d80e44691071151000885001040685902d13400004110f2031880d004213445165140d00f15441c41c001081650541c107982101a070b40c040c07030355a417401c0ca1081d00550325034128038040354900c0d582c4646103080c49098206109140551040882c4507004030140d4101500340c2d10156120600c0401d107840c201c0d001000401801c002501c0d00e0400f04900d034048c01602841201900d030140d80301400c2c401e101e28955907041d10808440c0c5a1903071410160701060f040d0060380c2510741025400001d102e138600700e03100740c49994030041c3d480c03100400b004100250184666000c0f122000d507040ba0a000c0ba041d03458011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 366574262 1250 366573012 366573019
    0xc0301061d0613060e07030c170702030d0e1204060905150f16020f090a1b030908040b09010908010c0323040317090102041a03101e090f090807030903050705040b 71
    0xe001a0190500c00f2201840a00752800440e01a0366541207045220044d5005000a51a00749604c80075421682402d50b407040e0788142540c900e042c040094580c0192007030f46030502d840c0c404643c4100c00800c8511840c0c907820301c01c1503031155250000b0704141682d10509000782d21499444903901c1c252015644d22420106519207030140495144040c1112031004a9002d00031849130354858031601c2000388a80a40000000c0184a000c1025031074801c11880c0e41c101802c03c40c641d80080e0f0858280d50481e210744007555101c42c42d0b000146c0c0c03905483c0d0080e03002986004408a116a8560018041c50001451041d05507800ea045150860f00c2224044e0100302180440c15083c2d80800c282640011200c0c001820661542401c24450003400710000c202040803051002020a4017003c1000b00b4031548085401c2c0d800300c440f840600c040d0322500c200c02ea69142e002111041a401080a0396400240223540e28041c0ca0060a841c03020300003580c0741c1c81260744c0030a80d03080501c1100d42848004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 366575512 1250 366574262 366574319
    0x50a09090504030c06050406140a09020a0e061f020309040f091a071404060302030906090604050a0b0a0908160615080a02040908090307032a241403090c030106 70
    0x151112000d440081c00407000c010014004c9000b00c2c02030302c40c84d0b0103944104c201040d61783c1c8031100b19107100009040c42240798074100c02400140e48500c1810211200c012440e1400c0c0c1c1e0342800a9542010246d12040f4035809000c1d24841507408801454034410440c0c013008101d0311408001e0443e14100300003840070711221188550149625200341c0d003c1945d00c2d00d01513103029004d68803006e8100da842070010a401209109171143c0610800b5441421000140650320300364403480d642d42405107026050f1a50040850fa11409942104043c16000950180c3d500500014081002d440c00d0042e50041c0c58100c0712900220651108011610900020903102e04640c007088010704510000711408082004402e40b5920144034a00c01980261a03051070031114200c101d1840750b03540c405240254003544103200b880040c81b12071251840b09101030240f911099001e9440e02034010000c2c26455020041003a85e42c00060b034a0010319082d002030151315918640c20b451024956441c62212115 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 366576762 1250 366575512 366575519
    0x9060a27060b1222051204030309091815110a080906090609060601030e0708150414030702060f0c16080601050102150f010501140f0409060504060b092b0516090c050a09 74
    0x20002c90184503850003544407814407440d5203140c03501b8009038071082080f402050800500d41c11082c8800101509102484241802d00582100000d51030004005540c40091001e070500301c1d6003c1046028071000066072898034a1000c0c204032030850700201240b08070000140001000b10b00d01e40a81c403002e00501d402e403103e0005601600300901103c2d103920030f101700010389510400c083c2290982d60048800c0030b051508140394118079101040410340d00400a0400680b41e80040341d000c0c02c1c1c8400065141d900c1d00b0007842c102081c0803103480c425409080046440d1401140f1103040341c400360200c520110380d048600000d004115a8413001aa81c40010080755029901451030300c1816142c5919020394000e2100b8282c1143c1c0101e14920b56400040c06035007810f200c3e2001801503200301e54200704050b4009558159240d03246000710301c13002119059074081d1111009101e5001c1c0540e80b40803103841d0150b10403056441041c000701d08003220550141c0c000c00c200d42e4142c00940d2a0a5114103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 366578012 1250 366576762 366576781
    0xa090317090a020d06050901050603160b090103140702100c020c280e01080c150309030a11030f040b071101080907090c180b070302010b01030c0c0209060a27060b12 72
    0xc004040c210280904215503005035100c100c0c46500b80e210300380001d080e08000c02c4160842d00c006015602a0780000c848448080c240c10981040311039000e5880d5840c0d4002c1c2c0103c001d07040041d003000007041c00e101403102d01c5030082020303507201300601010801560041000c90341e0340c1b2840002d60300151019000031041c001c1a0208600300c960540c0030202a03035075169030140c040300741e1081603070303400c40d03540744000d894140101c61180b0040c0c11101d0840c2841c5001b0b940303d2003049000002c1c0516405c03039400075502401506c07400d0303d5402041c0e840d50350368030090499a0100900710340030300109060030329642c083d05030075024810400080580b1810700440400a101c1c0344548c4043c08581d00d0343c0f0384900c40019441c4041c0045441c0d564441000340340103425100142200760601d801c0950004113180c0c072014042ea95501224403a5054491a010542000a6401c059102e0880b50300031620710b1188a1001e50100000c04100a45a91810180014040c6901e022104840d11020a1130b203403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 366579262 1250 366578012 366578057
    0x30506040b030a12080714040506090a05040c03060512060c271005040509100b030601032406080103020a1508060111011404140d090b07060903200102120a0903 70
    0x9440001c24064210000349821040031040341c0716030404200c05401540600a03a8001e501e07820700e21291404000d140e10075010b41d00400d40a9100881d0494150b502c200819000b004050410801440710300c000501420090081c0c4e03000d80e00f840400b103140c00e80010f4061292580b20300150500011052170744202d5400c0d50300c03086d82d9603240301c0c4180365501d8520b00c000c0c11019489290351a8641010301582510041c14030803911481702040002d440c04004032503001c8806d10b0300054001e01311008a5044184101d48130445060084c08241c003504000700c01e041e2802180c66840300341e0b07650342d01e002403000f160380c140002c0c440a0200c0c41d10350003901e024440d082d0708000407810f1003802501d84010401210207440d814408010b80422500c240401e120040141c0f03007030300399182005c0800e07180c0c2c8562107004142956a41012003418401c000798585035400c0c0300118004101040340a010f13410030702d2203940785070f085d901046440e40b5504c0740756030203649030310f400405070150495001c080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 366580512 1250 366579262 366579271
    0x721050a1b080d03020405100e0f060313080301092c101a030d020604020a080c0102031b03040e0103060b3c0604120501020c01060803070b04060c0c0c030b04022d010305 74
    0x4801c0000422402010f00c04807102164139600103880e0745c40d003020081c1804a20005105120030701e241c1c403400d901c90300c60b05090700c0b0055880b40d80c0d039201c600c100985250901c002038203230b180120011803c0c00107a003080804008200700000c8411200d05190b000003400d4902040d181e00040e00c5004000b40c44d040b000d0b000b041c82c022030002d441200c02090902c81c41c40e1003080180c000d03604100c1145880d8149801805e50b1303c00508000020340300207940ca01c54568030704820141c02202c6165138a007081160702030083c00e440195203580d01d15055000e410320401d020300c1007403001e04110013000c0300c00c141d002070b4003440b03140b0440200d03828110710714407001d600c81134002d03800700030114000c04409250040380b031055000683da490300d4a00942110344035040641c1c260001c22a10300801c803070300742d490b41264000100052544048106464659003450010300c101c0d2109000000c1c402d250201d03520481c000c0c0c0b0600348410100842044c10300411804013407540000c600d0384000c5d403113076100503440f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 366581762 1250 366580512 366580553
    0xc0302030409050a021c02090609060904090c0e09100216060c0908030a11071a03070503101a0301090f06081f18050a030f0f020c010c0201051306020721050a 69
    0x905403600d58500c241d0f641224100c82e07458000803034031031088007041c90701e000300f00c8100d0841c01e1a034914002a560300c2442545403041e0000300d26613000e9a1181d00c011812584a480ca013040c0c0d5a80400b889204d40484182c0b40500550030840e001c202180200c4078a001c9041d000d4440d4996551034000411121014804102c0c82100204441c10100000c204001203503c400c0754040400e01400d1400469400001c084910005e850500030207200a6982254980c01c119071680e0310001035140300216036020040f1a00c01385041c6203449010402581a2480550140a440d2030310f070200c410f07551203200b084900d47c0007a03074107103070109211a0b82441b4500100c011902001c0002c180c030b42c00c0103076203098031a0f802c00400d00d0100360f08030341d44816200940c03c054284030239034003002e900c440803c02014180081880c400f401c5a1141084070513046800445000c01c58446c00000d60320015030003070070000d003450611200204402c0d02072401e8590b1141c0104020310b21035440e0f120b640c1350502034111 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 366583012 1250 366581762 366581767
    0x50a03021b0c1905060a0503180a03030207031209030c03030e0f010e070905090601270902090906070212040e0a0213030c080a1a09061513140f100e070c030203 70
    0x12860030581e8803040208020700800d80b0203003020411580300f0114042590040361000100001d4541e5025204540058180303240c0742e80d01e0740d000000101051003800441d004000c0000304247c2c00d5405806480c1c000d94400b10f84030b1101480a044503040c1c40b0180114074841c2d80e410000e4030030381118800100e0031066074819400b24010780d00303440c070b9910f400c28250000b20040c002c4d8040c070310416500264850041015507d480040000d0352207c00c62403002c4903442000720180030300c2e0b0300104405a805416440300703140c09011683c4941d02511041d00500401d15612a070f0701c03a640a55043c1c5403007003540740c1562514802040250b104240b50190508004d10000121701050b4084004040d43c80c01380034189618a440d40800406100340881c8030050ba00b48818101c00080c0c5c81e034041c14900c007000c03130140b420b000513040e20500c4030051400e9081160303600e10049500d00490080403056000421ba0b15034150380841c1d01020301070220000b01010018460340c0c41400056403040c024015a031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 366584262 1250 366583012 366583027
    0x1501030609060b03161404090c051e03060a0905010b090d05250603050105090c070b1b04081608010c02032506050c0c0f0706090506072d1406040f03050a0302 69
    0x5007a5407455000c0400c503400030081011221180c9050710400d600d9181c0343c21b90000071120040a80150701901c4011541c2d844c4603000d10380035408890f0740340010224202008109603141e045580300f150814022400203200090012090143c41d05907440c005c10175083c00702c0031052101803088004141d03514460310250b251039869415617540c88a01c1003e102d00601e08014000d0107840060740301a02825110701000400600503090350301d030590250a081d0280c5801305d20030341c640a210071104d400c900024000540301000504001d003810140100f072401d5640d80c000038201d4803450140c1015810401039001400b03601016001c2800c0851100c0d5030031042070310b44078103c4100b190f54120400001074004058a0304009542e0466540401015554201500200254943d00c81c40303002e0600800c0b60020009840d0200940b550003d080e004411307076105907442c42460f402016921102140402500c103480418154811b503040071241940080596044410303a201014040c00c040e820301112 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 366585512 1250 366584262 366584279
    0x2010e041e0504030206160908100507050919080d0503010e0105090603190602030406140601021f1116030e0d240207050d0c150221040305040503071e090504020915010306 75
    0x103d01543c000c0e0300900e02c600c2d04d0100d8040350242030781c00000f40180d07070204100c2c5440003e44a07909005840000c605511028015950342c000e041105901601001c0c55001c101c0e84203040904541c944c8007120343c1240300b240140c400d8030080c043d00c00142035500042c401410403040081d00008060200c0f8013842030803202d81c030f441001003070889115030000144014059240500c005681415004082c0380c200b0500103540d503541248000350040c4600700ea0514a40194000c0482030b10001000b599508801c08203100d148542608030040b07011450010b040b8102860340d102030302c3e170000e81380b400c4035040d04031a4100c100f810145901903401704100b500203641400034140c14842600c03406d100c007000c0d1030030130a82c80342e4020032f401d070f00e2041c07043c4d2124411600c0761220019a12503c03881d40d4641c1d04040f80c00d440b40c2d400c056054412a00c2c000740c0c40c1d0b003c00d100c90904140482d6420141d4607451040c06550003502c0181d070016800001c15801e268aa07100400c12105050015655642e506d02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 366586762 1250 366585512 366585521
    0x921050c0a06110d0f120507020f1221220c051201020304062012040f0c0e0708060406152105011401021c08041202101103061305010302010e041e 64
    0x244000400000c400c8003403d40c20440c140b0325040c141032007000d01514a000a0089103a0151030707440030744403804148520300078082220311030024800d591040c007210250351032691041e12481070f8a0a41203540c08004c408248250090342c0406070b61388550900c1300c401500b42100b071429113040a910a0008041d039402c10022064010701c000540c8034940303402c2c680f080721089403c1c820104410000a420300c3da003007045401022022512862644450824066030b03400340300d0042c080c100c00c0d440860010100b2985a02c26242075950000c1980c1d000144410786206105840c0c15074502400000032600822000344c90301d118a08a081c80c55100021000b590b100b039001c4004240100c000e100c05582c14000ca10010001510300940c070300c40381000400741c0780c000f400035000624001044802d58424400ca450800d102007040c071541c1c1d200d079403100b100e03441aa4864400c61581c14003196030252401994102c030740585880c028200400107000140c10707825660311740d812a11880c0350a0003400e20a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 366588012 1250 366586762 366586769
    0x1121030403090e2701060b09040905070e0c07050f0a020108070f0c020d08030702010c11030d02090102100227010f090e13020a0e0601080c030c030a091e0f03020601060921050c0a 78
    0x4210340744da40000d003210300c03d640d81e9a4020080e4100003060082c03400c0d850440703c1c1a05c023a070700001d544180f030a0440c02c014158101e66107050000c0140003500070060052314030540038400762030250504204265a900d0440ca00070b021501c0c18001540507406140b84582000d49802d0000781d00c0c1144c4d00040e4003a00c000030480e0912801f0085c0840554244035841e04018a41052440e049802280a581e800b8074030414194540009020030564420722035801d15080901c020343d00d501614001807161a00c0c0582c100c0b50b0380300210103c5030741d84a8900781c400c08009850f144001c0b410900c0d0070b00c0c00c580090404500e0404410307004016141d00403028007e00f5050101c0400c4e091403000100b114001901043d08035505205100b071242040d001c881c2c20500e40d2200007058840351500d8040360003a001c1e44030256060303403014020700c00034801c1d00c6c518510950903502a0780e00c0700800c2e9104032043c020000c56400c00c021403a941d803001007500448500403400c80d545c00030007000140d160301550f007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 366589262 1250 366588012 366588031
    0x30806210d0e01020d05070b060307030215090312090105030a0924050a060b0405100c0303060f06020f0607030216020f0a09021b070603020a0e09100b0414011121030403090e 76
    0x1150010300603030115011044200920140840000700d985c000e005014040f00901030390fa40708003203001941c040201e02d00950b800b41c14003000000740041100359400c00001540240250365480a00928400480c0c0329103105840c0d090451321215084001031002030b00031503030300b400c0d84003d101c48109007284035840f51030f556001c078140ca000d031051400e507092940965103401c01440203122a5640342c1901c0c0003103e50703141041403840f0307500f82100079103455408526a407002001c0403465a9000c1405004105000110723582500c803040c1c03c034100d10410380f640310125440446600145800c10130042c0f103100092205016548460208040342d0008614031b060825000440113401c1e03003803010000420603400d0860908001072006042d003001030315801d11508881d0300085d1601a40d4103542d01038031910340b01d50344032920340d0a071040d0350002c00d0010f400300b8075403c00c1c0b10701d040001640540307400840d130301903075003050745044d60f07031036400240086060102d008030101d140910a40000e2146000b807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 366590512 1250 366589262 366589273
    0x52a040603060b0c1e0c10030905011401080c01030f11042c0403050f030916030303060603060b0301081213080d021e010c090302130603060212011e060c03080621 71
    0x903a01900b12140d0380c0c02840c03610402d00003e9070382030011401d0301000f410b440d91420101d01300340e0206c3c02d0095601a269010078421103581180c0d17070540c0003c4c101c0e0b203d54000c00042262920600380da010074400c00215034020100745500d5480394001004070040c1308004142c10880140032800d64020350444c00030310040200c9506950741e10302003014101c503074281c0c016107403c00d07880c000c200d0311800701072480344180000400d072104800c0014544050003d858440f00d161a450014003501651140c80c0000e82000d5011502e02504000c0b0781c100c2e6220760007000c0441d9400400c0e1201e070041d4095000d03400070904009a0541d09001401007440301d54040d00c03140c107072101c2c1103284a02c813503908400350b854110344c1d030852900010000141c0e17404546201900308017003900382c0505441e401c0141018008030303518103121b5001c8402d40c180ca04850f01c56001e0750f0042c400c40045030803442070100103403040c95100c0200c1d02940c1c80e1074101c4400781c2452001c108048008116441a400000f940d6020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 366591762 1250 366590512 366590519
    0x3090303062e18080604050607080106171f030b1602060a06080c092a07020307050904080f090409061107050706020705031f062112020105070909052a04 67
    0x14841d070303a45211200c400b4401c0c2c115090020941c0360040c01c0d01c1401406144010210070080c001001040c0c0c4104072200703480c0ca4900305803255015140c2c1c0000c24a0710700042221400f4a0f505c41410ba5000840c40d001e80d1011882182003109542c424005c03040c90b24044085800c41490910a504100003220490813050009242c600b005000c90021840d0800601806d03a000c188012418070403200c503207042d12038800c04840f120b00c0d8440700541c25006544880000864030141100c10700880607a11030582d80c205206503a241103600910f043e82c2007105038400e4401401401107090050400a03a03c410350380c0e8401207544955480c641c13410046041170402800b00701b0380d8043c0440f403010342921490300e001720381d40714840c1e8100180940131404040b61400240c0c003031001081d200c03001e10000e05150400e01445a080070041c2d0b02c000030100c649100341d005000d4140950b44a5544100141c03828808800a00d4090304801540c01c1004110700c005000c03490104080352551040359a0341e19 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 366593012 1250 366591762 366591769
    0x3081005041b0509180702010b03060f07020c010c0302150103030c021e0906060a0201020915090907080f130219060827030f09150304080301090b03010e0c040f0b060309030306 77
    0x9550311251055003000088060100744030007008810105080079601c40050000060620240741d0720241000d103580d0070040c80c254150440c108034001076080d074005468103104140103603400c85100015a21044803840e0315441607004210b414021b2050381c0481c0f041e0301182c00450b4003a4410360001ea28041034006524150016460081d0080a007501d00c1c0c40c000045030500500030003562140703002003400319526000b9011110120300c020030150802d4443c906200003904450003c500400c0041300040c80e15000e480120700480701c0ea440800960f81c0d410f64a07420001d01035040b6000350000c1e00b04001c090080074404060300c40c680b10000c81345002211141d001c01030342c110140001445a00301c100c0200401104d0407503c41c8020282d030b50881c440421f1000c444808848c81c600000002c01052245201c05103068407a07401d400c1c0b094451031010903003640d5811220000daa0009600c4420b9451f01c4c0e8481d551a401c068004207454081c0f40000d22940c0007140d5144030b540001003000035928 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 366594262 1250 366593012 366593041
    0x10050105091807060e180c0406030507091a0f0409050f040302010c0c031403040809060a030b0a0510170a0e030a090306050c04032006070623070206090a060f02040906030308 76
    0x11058810b031200c104550500310764841151140c0300500810003690062520381c03290020b8001d06100038080d0504064402125076401445548000381c540400300b003d1905c1004154100d8004100782800300300c064094074200e0740003681c81c4080c007008100000d405540790041c2c51040f1414041000039207410b0030b000c0d0a4600e510350000801141e00e0110001a030050f40c0b404502201c1201540c0b655900c0c54003170050301c16215000e0b80a24082104020702c0d41c103800c030005440c002d032043c0070541c0e981c03018003002441c9100c9040c0800e14000382036550072007001240f58401a9000081800429011500e0840e8001c000701e1002401d040f0301442070007880d011781d07500a80351300b500900c1d0601e15281c07510300072102c2d03d0f01d17115152a9281c040ea0340e80c401c0d0540b001c141c3c0140081015413440c80100c56001e103546607402407411028001000e00d0b00100310b0382e200b40e00e5000503046100c040d965960007400081003202490790700303010102d081c01c594419070002e1880394451350524200b8202c0c070711031403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 366595512 1250 366594262 366594271
    0xc0f0313140c01110718110906031003062009040f0b09160306080d09052809020714010b0112090f0510020a18080309010c05101506030b01020f03040e181005010509 72
    0x150b02c054010401480e006240100c00416960700241e1031fa015a124040e034402c99503000c0c1d1114012040c031408090846c500002c5910400c01040100d80c0a03c01103054018072107030180c0b03680c0038404140d407400c01d504074141c5800714140010f10112004001880640140c1d0220907443c40c140b4190300c2c09400d071290314060007003d4010040769002190003050181d06018041c009c12580c0c4040280b80c0c0e0940043d07890384207455040c0d0b003103600c03110988002d400c8803401342c5a50641c0141d141c015241031041c2c0c008544182d44001c040080184c1d0701d000360049041c101c4040f035082041501042040c03007084018001c5900240c2e50f0380a1044c01440c071402200d2980785007520034002c1003801e00020455401c2d0344203081641c00b010250925505010070040a042414140b02d904c440b040114003011083d100c3380e84003001440c010400490fa034180750307080c0501a900400c03040c8040700200c004c842e40690404140440e1858240d00e490400b050a5003c2c2c105d01d45070030051046240006030030303602 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 366596762 1250 366595512 366595547
    0xf1410021e0403021c021908060604060611120306030f1c020d02070e04020d111e0418020d140c1003050106091508160e030304180b090c0f0313140c01 66
    0x2c060542d00002d00510100f11034010354108041180b04544440f00c6944100030000f0203440d820355075a0509842e4442114100c2c4507500d04080420580e000d8016651140505402081e08400e5038120750460b03400a84456414401d4040117003401138100000c2d015002201c01c00310603541c4001001c5c0ca0004803140c407030295084944140308424800051640c0190111032059841c3c01ca8180b0342581950034074a00e800540014581000f18104c81981016440c00c0c0e8040020050203410301259841d0004003c1d84402c15200400c0450004a43c130741d03000d0341040c107403072030100d01c0c000040b86841800280000309446100401042da040000c21004052401012a00c01e0203014024a1128001c15003191809900000c032210781c482c180721029510081c04481d6201d4507540d00700104510106401202420300c9011001c5041ca051040c2c041c002c0c0c05240b90400031001000e5520b600018800754507100800c0c2e070b44d004114900400d50015048002070030711101c280c000140302c00108001100f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 366598012 1250 366596762 366596767
    0xa05090c0a05090a03140a02100305071413090c0c060f020a050a031d0303010602010e010b06041d1e04080421080a0e010c02150a020f01060b03040f1410021e 69
    0x6561262411207a0760300c514030309540d840d41c83e5400901e5007103c41c0c0004e0071881014603d070352035000018991b90a68001c840c80200348034848801c41c1612030444910300014080d450b50700c01041443c000d400328100410404032615161a02041180c41050300c2c50001003205c21220709228041c8540e00c05104d0200e0700b9403801b0502c440140c690b21600e1030000803d5510380341000c1d609841c1c800030240140000c141c030382d00c3d6075440c0c2c001d001e01034007000551103504c0c0204041103403a000044400301c0e1410610440b41081000d0003082c40bc10080c514044607a0904c2002d104d0207042c0c50a40c4138a11820308240c440e0305101394603004c0310b642802c019070212400d0520010a070b11000361210410713a45410f01c1c03548160001280c4800c610480250004007140c0351142c13003502070300030301200398070b9608a0340c186103020070b814281c2c0c0040c4115407040408001243c081000c4224000031640550030500e013103001c800d005854030002039a40d25442da804144500d14421144c048600600806022030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 366599262 1250 366598012 366598021
    0x7020a0b040518130510020a03230a090c0b04030807140303070e060c070512030403060e07030b04120e120a11040e060f0a2306010e0402071a0903040801020f04050a0509 74
    0x1129890440d451005a03455400016000410340016401c01a803150640f00500ca071400068040e4000002d072030b000c64142b9045c84030554402e040d840140c6c0c2c203481c0c4a00c0645840030114003e1080003425102d01d040c0e0500487c0032000c0c50010001103128072000381e0b42e21024100042e51500584540216400070801c0c82542948044102c4007500f0858000e80e40c3c602c1d1403040f51525032543d015980008a003202400d80107000700c0500100ca0240409028584420101984034074241c0401401c0002400200e001301d8110121403c070b0300002e0420307050f91b01020001841948010039240c03e01e900c011310345000c01041c04401140c09806882c10f1040424451000f41c58000081502c880c0599010000d0a00c084c1500024001d0900d0010b01c00502c501c00744661002c00100c52481c04155400c16104503814144200e0301c040760003904040d066000504a0b081007000500201014402400045480d410a01c0100340c0c40c0b02050074241d8451800c1c003400030035055a840f10303224208050800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 366600512 1250 366599262 366599269
    0x4051203190b0105040810050a0e010b010f05070516090e010605150d021c050f1815040f020111030318010b1005090108100803030a0b01120e1b01090305060c07020a0b0405 75
    0x4424141e18680416102c0a00c07004031007500850340b0201d12885800444119400142c0c080760240040305001d1044100c4d00c0016030036a442080c0e090b00040320038000c085001d11503405802114410400c0d200310f03100c00c01c08002c0d24210340e041650501d030b40d0b0398022003091702449904000c0c0001e0f14080d58100d0202c900500394081d071020808599000103100100c8407000308141c10748049190100058108443c0c00c0c404424103c414071110114408920a444c80002e13a280c00070990444001b02e81c3e03101e55484103824107203a0201c0c1407140c5501447c90f50074041c8040c5102c1e001108040c8075043e40c540c20907003501d58070303400c15001d5045c851018003490761100407960066000e083c46c8550f0b44a8540001e05007107243e00c030307513000e00011082c82980b0085070415400321300300740c0c1d07115054445d01940e8005c464202c43c0403071407a84a400c105100c4904500f01071400001414241c00c010380d40e464007420328804559034150714200040c1c00c01146480f076403980c0a032010700200c506290820707010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 366601762 1250 366600512 366600541
    0xc020604110607050c06030106021c02010204240e0d050d1d0a03060b06071a010914100e060103020c012c0601080d080a0b03010c0f0801120c030b0402010903170304051203 75
    0xc600810000070f200c0e003407000070807041c000302901034400c541d40d6a4075000291501296030100d0505498051800d0095105000384c0e403d603131000100088401d05a01070410402008030180d0500210002d0540a55103140f8540c580a000768060900c1d004d42c08401070840d208100e480308030b28100301040302d1700d49030341000e43c05407507201400240004108001841c02d00400800428004485220454854a0882c4d890485003440d006000600c100c3e5011a40c0000072550855a00c0d100c100c200110207090b030760140c00c020117040042c98410385089150958100c1412002082809043c940000c1000021410341c4a400c80c0982041d5044c0b00403240c840e11164422010410303404041949000190304c41030300080020002c00082c1c0160b4005401c04d28080c0c40c88004c11400000080c0c5054910380742e407003841c0d2200600241034190303512111014400b4000703a0421402e00401710020728403400301383c469041d10a55985030b1170285080c45c41c0082c00d140340440c20005200748694405203048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 366603012 1250 366601762 366601793
    0x160c0b040210020109050a0302280818060f0d1b020a0b0a1112011d100b0702010c0602090a0815071b03051606050109060602240402120705150903010c020604 69
    0x4141100b1980c0d868200d01402140700d0142c000d0244e02414020150001440407180c4d8000c0c2103045101c6900140004091080201501460040040702ca405007520059a14a54014040c0d03080245180c007160503600800384c0003040039a5034200b001c680720080c0b000e1403104560310044c801180c1540d07d12514280c05400c506506844150028041c03080d04203941403d10706007166419580d6074048002c0c4400b4000e02002140120070200b81d80c0705030300c984d10042d0360710360507014a40580c41e40115410f01c00c0220a0b501c00d5401d202e088036035510b81d11020010724580b4018502184d82c6000e14150900140c6001d09102d80b41c41014207016140c558506402d4160074415154024090007600310000544020b1409180400101c1c3d40d005652251050b5403a81d421113626804240c02a02050392401852a00203c02030000d00107140c1100d0412561000b0800d4500c41a0b0380c4010850318050484d8020644401085403115400c0900c202e5010b400a0320003011141000c1e250502100d50040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 366604262 1250 366603012 366603019
    0x6120e0109020f12011b031a03150c0c1c09060206100509070e13141006140d021b0d050301031a0f04021302070c080606100f0f050901030b090a05160c0b0402 69
    0x80313201c020410a500c19540c440866030000e00701e80018000400602454022822032072640100140030f003000560043d0800ca07040c0701260355194154007038243c0c1c1110103e890385110700a8065a82c0302041182885580035403141004541403250180c101100100305810201c0da4140030806036a40d00801c54020920b030800c4a49840d1183c0401d058030302c112841c07640c1c1070500c501c007146c128860191501c01d08407013400902e00ea0b01d0303640446140d100c0005a121025045c40003014040e00d070340c0242142c03040302c507845514092039404d041c105a48404c000300480c038013200401c184651020540c1800c0d1700103d9962407894445202807410300042c0010740a03c40208015074814010380c100e803810b9404c07003c1d1051060fa03401102e5a2140110f4800b4040c0c10307083d8070080b1843c0102d40c021168402c644071404002141c460455482d00003c90325410113882e040811007645440c03114034000c200d403030808146032600780242c003500202c0707051410030444417031107032004295000301440c0c005038102c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 366605512 1250 366604262 366604279
    0x3060b190302090c070204020304230a0206220f08150c0a0518060f07050c0f01020319300e1c0c06020306040e121213020a0e041b06120e0109020f 64
    0x180002007135008800c402900684004203008c1070141c1141d4074002d0703202d04d210340780350500319110485e241d44905400941000c0700b440313940141d442000c080c042403038103902d00c030b043e01e661100940d00c02c0d6050780c45003203150000075021b5940041d4074400303139210640015a41c0780c0780501030002e10522130803c1c1e00340346900d0340c0d0b20740d0240da9a41e800c64901c0000404030f1600c8113028244230f511200c0d081e095910420080c031704140654000b0081d20542c07032861314140c081a01d00300c400d0381d40d145055010503500c09505004000554548081d4803084014040024900110804035107043c162103148000c910822a184806581c860b000f114119800080941c40c1d03190a408100640103400e40f402e518061981c44400340d03c04030300a4805040314034500049900d9000290002c032001400181d00868034600038064101000d01c0f051700503100d1500403064403503580c1072000b00101500000c0003d1f40002440c01a001103005200024802c44001c11807423500c0c1d4001480200c420b40c406d0b01890a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 366606762 1250 366605512 366605521
    0x2010f0e030a02031c022503030c24050402130504170f0906070302030913050f010e0c071a01050307172509140f24010e151303060b19030209 62
    0x2d01c20201d02da94040c0c2102e86064000780680b0090f8000a2003000500c1b403600310300090340c0b0001054203072959011907001d4040c110b0318211032002c81000103507201c4807500100500114059450301603c03103128000034807420729204110b040d6000d1200e000080703003040140804621a440c0030455491840d0341155a03a4550440d40c0300b5000e1401044c0c0e1146010034402e090580110041107016802c440c0038a9160808000904880d020384510006071021001400211000c1071041e4002260007001801d00c04159154040c125025800b2041900c40c040100503500701003007088041c010103030140741c0300a0710010f201e50718403e5144010080603151280c02d4180d600825000207802c0d04442400004181d148184501005541489000e084800011244c0034000f100d00c0c081e2407416039842c1c0c1040e980c801102d001c80402c54080d40003d1459070141c203000c1c0c04d8000c0c43c105540c074640200880c85c6081c400e08480f4811407a6006042040e11012800c1000c80078801f6030703904a4015920362038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 366608012 1250 366606762 366606769
    0x9090711100e01021e040f18020405030319030b0111120a1e02010204060f0903020303030a050a0f09060b03010606020703050304150512070c200a0905060420130f0302010f0e 76
    0x7072549154034400d00e00309010204000640041181001d00b88084428108441104610303229510403020ba003069201700384000102e10108000d050701c004405404c15448500090640d80714000714808640b030703608043d0306140c150150302c80c21402400c03c00b42d840060411107403038605e0a141044c00c2c590001d80040315900a50f03540c0b11101a038041404050403021003c3e000398018007034132011520342c200c110280b510070b109500540340c0c003402941c00c640341d564610018010103043c0c01d4006884d1100904242d1a500c00c00d42d030107025082c081140c034440f00a060031105950001021500300d2002407012030360000807034080740c62000c001140c445002000311200c1c0240242c0040c6000741d24107005800d0f6100110b0a403c0703000c1c100d12807092101502d61080b0071802103d40342c0000b02d9040811076001643d11107541f1031005030000c00e01e007143c0008000f41c1c041744004001c40e840046150006e4402c5032221078003a000554000c07002a0841e00060170b003050b00c00310b550402c8462100e2400071348 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 366609262 1250 366608012 366608023
    0x30708070807080a08040308060a0b1602030f250807050a030f05010e191a0106140705071d0f070c020f1e1801090c09031a07180b04050a05030309090711 67
    0x181c0100031140c0f1441a0703640105456010f1b901030380020219404030f445494400c0800c01110203440e03c07146814950f8410050881c05c00801340d90500501100d106000341c10f200c8000350a46d640000e0004100411420074000c5068100740003503030018a050269440b4a410b55040d030350441021662010f5034500342c0d01610020442110600541542c200da502e031152785401c02601ca00038002188030f40081101c1c01040174401e41001500c60400305420410b044000c040c914000d0040d5a94917844011180d6810521560504031801002c1044407105003084820340001103890300d5142d071a00c1d5000190a4659907415901c034022105038451707048800c504000c075640707000c5d0045100480004640c06155070903c01c0182c1142000910f4108601c502c0880b010b4035405024032840c00a400030854400340010924001c2c0581085180000100c541800c001464560b03003556460f030405040c040340400642c001c0740603900c20f020070030301d598411a2060b4000d605103401042000d501e46081d141c0b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 366610512 1250 366609262 366609277
    0x70201140d1401181b081e100504140c0a181d07090801140a050a020f031f0504091112120a02030304060c080712020d020403080c0d0f030203090307080708 68
    0x103141054441050301102c903141e0403122603d03040c807602d5811074101400d4420085000107002c001c5020700d6800b5004101094005020046c0d48444084400300c10b400b2140c25200052003c81c0382d00100300502d424081c086180c90007800c940d0007401c1c00014984240544010f4105019604048550090120409500521107803200308038000d500b02c001641000e050303410744c0c00224109404203814205024026001081c00c4501c08603647d4800c0d250000c203806451040f026400b040402d4242d0030800285001e140c0b40d074911405004001006c5800c8103695001740c0c00346084c44490400310306c80d21550400183c00365482400d10429a0400342058074981c41140160300c080340c0b0154090f400006035128600c5140108003c048601058807a0b023000c5500c0350011700c10000000f43d140c641e4001d098030284072000503003459202d584000c902e821804d07081e4041d600c0040b100448a40c00b0032803e6061940b0700301145141000c03c102c0342ca0380701d18100600039000010301c64040000f9801140c41c0c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 366611762 1250 366610512 366610537
    0xb040b09040f2306030309011b020d02040903081e01060c02060a121806061a030c1810050307030c0903020a0b0f120103060c082508180a0c0f08011107020114 69
    0xd80103400031101443d19009824030b4001d8071400190940c28000304440500005840302c84001801e0540255402d4015000f26080802c14072200010f032142c1c00381401c0c03140b2a40701c09802c0e03c1c2104105c3d480c40d690340b0030f0a49100d800d0b03004000d000d400043c1034000640507500300c4d5032540380344001e440800c0080490b8170034601e00194854003000580c03680301e00a00c240e80c00e220850b07075503501503805901c0721442c81e41d180c420404615580c074444018040031091418801c8446440800255240380d1854001c011403000000c04c2042c66151050701c102600e08c0c10903c2d4400e0039038010401c8000c4a005a1503003040004110418003400c03010b940c0341c44001410032915613100d14140e006050032000030740c0810615001708101c3c0c0c0005080700000e54020102621540c84070b401292042c0380600111a84d2401001c15015103000740041e002c254041ca91a0300b030f1a18120f08a20aa00180c6c0000c040364984030241d00c203901200c0489030700640901c1e1104ea00c00040540d5400c522404044002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 366613012 1250 366611762 366611771
    0x11b0609051b0f0609101b0501020d09031707020a021003020412140f071a1e071202060603031c020d02040b0d0504051005090d03051b160506010f0b040b09040f 70
    0x4540c41e00d15103040032102c02d40301c080300d4402c00e4041c09070602880041640c03007022011854012881403030443d6403c07111460f03218103c08103459030303401c80e40b01c2c003440310080d600c80b0325030800c2c982c0005101c007c010111010000b0b41c46d00b4500252200155003000748100310440190060074801d0b01510042c0c070703003090039803c0c4400710b180005115140a80e101200d002d106203d10b0100320100d481c3d01124030701d01070310603405e041c1c40149482d42d01c010000038282e541740c0040070b05002000007403c1d1b20792156440c10362061030b020020b450414020076052103988108544850051414084190141c00c6080540ca6a840c0c4580720068002c64210b40f0100b44045424059488250001401a406030052300c80c2003910188490035031b20110f1b1a00d005178010388590903100d00c40d07031055520803142004015410a541d10101c000d07401600212030320381070b020510091080074400395005100746c1e080e8403205480c20f20542e0301806644109034a800010440e000c003030316990014075983c10201d00810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 366614262 1250 366613012 366613033
    0x10323060111070807080a0c0e01050a0b0a0203040b040b030a0506040e0a02060903072c0912070308040203010f0f020904050610092105060f0702010e0d0905100c021c05061005011b060905 82
    0x155100000320065588c1004c5040000710400100744160590781b003c3c2c050014141000390000301030b4051038944085200c01c100c0040c0c42d407448400f50000e4101c10441e959a410903076480d4050b10400380520740700ea854811000300010002031425105a415500c05449285641c0000e0900c405648020b00035030140d101d602c504180d220f0240c120300343c0c4100c012580e85880d1011035803001c0602241c0801d50342000307080f010a00440585602c00d10060000c250f50110f00c003940251203c02d0a2806095004603907a00c851401c0c0c014150311500c2911000c0204081c02002441c200c0e0903c00d01100e5245c61a1001c60101d890840035100c5402100315021400e00d1340009015020441d136400040d46001400c852510303021440c000280d40a54403c880a401c0508101c644101d2015070030038001d03414030280050319a00c8540c2210034804640310050720711170424506140e001006040200c19021090200340e07040342904078a0380301440c4c0c202c400401071400744000c011200001e01076100b00460b82 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 366615512 1250 366614262 366614279
    0x4080307060c020712030c0803090c030106030606091a090114030a0b070518030c09010e1f0906210807030c08090d0f03020d02240402040207020a09020405010323060111070807 77
    0x541032002d9421658800d0395400b00300080e4000b100000c001542a82c3c90f40d001c140024003075500002044151540800b81c0c40000c0e00f1a07ca0390700c201c0f40e05e911528100031f0b081080c400d0481c09110070f10314a44120800e80083c0801005006114805160240740d01c40b540f81004803d201a9021070300c0d0752242005400a001030300100c100d20910f01300388010822030700f00815103c5e8904000b400724080d81e4281252845003043c01407849a42003141d00c0e100401c2030310303c10402c0c02000340d40b10028461381042802c94841c085d82e64a4510110b885c00071000140d04a41207500c095018a03100319481c5c11442c00d00b00c18800e02c0f010590008496000e0424803070344042c4070703420070300c26000c1300c8200031188030580e103a14006500c541a100c504040c844403003043c6101740c1d0301c240f0081c401450568990f0000c0d181451503000750039903a6001c642806030b541c062040c028254005042580812644200c902100c0001000c1504201d5144c41c940c021203c100039050241209009031a03001d615071120 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 366616762 1250 366615512 366615521
    0x605030a2a12061202030307060b0411131401030605130c052a01050f06030712050a0605070807090f030209160c170c28080a0908031303060b0108060a0501030b04020408030706 77
    0x1d0342c4440c2d291100001e002299501a04102c80d03000e001f4600f48245504e54500400d45840347c04c3d001500d60f501d45408804040003403031100c15036441d80f034816080c41000c11099442d261a541490304c1d1032030034480c07955114460200c05000440110b041c80da104c50490f41401360282015246005200101110703000d032000d58003011091000308260395a10b07115891700c690a482c2c0f03a070160420103040c4020f41d200400e030100310740904211640d00c80107a44070400c8800858111000420520a002c0c1840d80100400018450815a00c86040c150340000c0c16055014101400d42c0d159064500c0740c00c0d002d00385c140b40700c0360030080800301176400d40c5003513040b41d00c1011320036000c0c055008124156210038555640c0b0600030b401d0405140c02e1581c402d052540320000900030300002100c001601001000242103004800a082c80c0d20351a600c1c000d025240da840b08107050001c142c041001035103d0482c00f0040360003d01c0c3c0480c41200b29400f04009101d0b9070000c8855001c0042c45130140103143c0c02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 366618012 1250 366616762 366616787
    0xb0d111801180302061b0316050105010816260a0507061d01030501030f02120f0708210c0d0807031103241e220c080604150605030a2a 59
    0xa989200161030180414002c9280c040250700100a1003c442c50f1130b0000fa00510854030002101d240c0300c8150701541a10440440c1101e00f03030344032401449a25810304c400c080805a84030202002410510603401d0183c68240d1b559050314541002c0c403584004102072000325400100b569140e0b629100003c010340c8142c445821302c045007a11801d041e5100c2d00c500c50491b600300c07403580110560b0740d082101045940d50002600c0c131030040107400200042c860400207280c49401002503030883e104070380704003002008410f2940b505100035001402301042800c0922810f292650150303031001c03000c3d401000304003100c1c4a030752804400c00120007400709a18201140c5c071403544081011520401030b900c000844030340d500c0d0340c9030040300c4900d0070b19400c4a103440d08409826800d817440a4269006c490b266216000051390007028088182040c1c402c2501c000303104500316000c1030400d2030203803035844054260b40c0700f560f44080080c07021b241c0100501b41c02e0882c41d1406003000c031601c001440c07201580d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 366619262 1250 366618012 366618017
    0x7090e040b070306050f130b040626010c1b0f0201021002070605090714100503150d051e1603110607062405040203191a1201090b0f01030209010b0d111801 68
    0xc004507052401070b19078022461b00810707140e04020805031103000390034190303a40d5402c40e44500340800e80602003085d05800307400d183c00c00107015004112150030740e03c1e80f00a0005100c192034490340b1401e0409442042d454000420094000d220f10040303113403020305450000307200e00c04240241006010b400c042d00405102e82240c01071600c42140100000034040382507484003007219191041c0d40100003540e4010341c02904000e1030107551003c034400204410041354941c0002400c1f00344090700c81c0c0000d8141c0405002440440c00c0141c902a9204d441d000141403001c200b1030601659860300100c0d80202e502c02d0060000b103014049581e00e1401820410041074540c840c00701d001e0a061095a03c581480c07450402c00030749103c2c00c00003d04016102240c0c221500c080c001c00e036290105d000009600b08800001c1e0a420760900c92001c20014001ca10860148001003001d03a8130024202e0641d608070205640c1d80368000b40110041c40c5001d01140050000f260a6102d0410303e140e00c3d810b5a000e8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 366620512 1250 366619262 366619271
    0x4050109140d080a321c0908181c05100f02071a01031505101202030c100f030b0301050112230f0a0605010b130915080601031103070609150807090e040b0703 69
    0x100101d04168183e00c91841c0c1780e006114941300340c40c5051000c00c1017540744100203007021441d00d9100466000e01c00180b0640010703454075202c3c0c2407025030006036000050700c41e12144480e98649440e071110201c0700c0c0c1a1502d411101140200a5040b50b0b03486600031001c845c080a41940b182c5035540900c0241d58010719208102ca8510007406180e201d10001030400007a60708051481d25441c45154082c1e030107104104e072030f40302d41d00c0340c150040342d038034298a440b109401e0790b0030000c003990b6803441c032540030743d0400d401000354550402c418144103600414140d94009515103080c03009141d0440c140491207482c4440c0042d840102c0e404a5540c0152414811680c07030f0b943e0301006106c0c406003420410b600b850b040000440b5948140a402c200c21014085203645222183c64041d00b03800540702c1d1080301e84000700d01e00e020841c080050400f814603001e0f4170710304a0301d5007030900c00141c1042404110f100185459200e01c5810b4003030101d03015400154201400d10720b41401d000c44800003ca4600f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 366621762 1250 366620512 366620567
    0xe010e010506062113021816050f0f1b100605010807030c02060712231014090106081003020603010b090102100b0f121c02030a1404050109140d080a 65
    0x3c1c030102c41c001c5030004440c07052001c4600411100e840014040d0302d490450018010040e940d098090b400520b44018080041c01c5c8510b045504460180c038000901a080204a0388000d40d04140c9602d802484110f50312040311a240c0d000006800c48008010b0040e0a0404051611540018190b030000e0b620f090680d501c240058044410f080701d0b610140e8409400030308150b120382d40310141101071010115102006901d42c44440003010a501c2c2c1c101000010080718005500d49003004120391035021180a4141c00802c0719444180075400c1080305240006800c49403200a42c8011903020780308640d07070340e903646d1990f032503070042d80c0103500500900c0300d8449031362002d024510800d400102008175408021007009034013809040004660f0080200c180890100c4241c451111401600695900c8140400c014000a1602003074840701800740b0041c03095907804010f0405070344180c89020605107000002440c0000c07440070041542d10002212000254406071060044030a004441c0382c0546 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 366623012 1250 366621762 366621769
    0x611010c030b0a14041b171317030405010e0601121a0106050a0f18080a0c150206011205011506030209040b0303040e0a02072102070609050d051c0e040e010e010506 72
    0x10b103503140355010381e50000074005a1101444001c2c071010080000500c0c0c00c0e000098084502c05001c0c50001c602e0050107003128284858166070302c40094030350b8140302d9005a40301c156060040a40001248002c400101044000d6002d00c090403815821100107603554000c0c0b00e041a903105007110300b01c920b0b016005501c6204040c9505a440940309c05013001c8514104450281810340d49204020440004d0400180c01e03d540704007414602c00500160340d50b81c14584c40d50766040e03004d82940c0804c84145d10100b940452042d040d124103070300560f1b1400c0b80342019805000c1103030a04541036403001001820075010750092908110550f030520807202c4110405031a40118810b41d854011101c0000384020960f078000c00d50544250b40c05440d00c060b80000300e00c1d5141030300c1104090f82c0500400e002007070b0480f040c1c41c02814110380e84070385e03074003166034190300da60311005a0803028561a072040305881c0580c02c18003001070040d20400000a2564206000c0d10707203c2e804154551030075000c1412406d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 366624262 1250 366623012 366623021
    0x170d110d02070306020306061e070201030b0109210f2021060406020c03130b13090b1f03061e0f0911070f0609060e4804020705070611010c03 62
    0xc41980141003500d180d62030b240080d610042c1442e03031000080215591159440302080d007500c8941110303d44030040f900c00074003103a4624040c1814041404030400c03038950201c1a4001440c960034000308068854a419100180321400c014030075401c0c010410040489040340390382d0058115034240b40400c82c0d074032a02000c10344a5030b41301c0580000c0002008599160003c100a84002003100d15040c241d02c41c427030086c0d00b5a04560002000001c0041003940603407218400303010440c0d0304024401c00d2000140345c01c604031540b2480c04000034500c074070303c40c0031742d200c400246034002c0000c0804803110300380d894003031543c0141c5016071b01840340401c80c138031544201c804054a00c500d031840c4c0542c58460b43c00307401000ca01100d036191500e00d1040002c3e018000d556100300c0010040030051a00048100c00b602900c5461040c450094044206940020906140c490032140c0d40004400c241740858044c0c420310308040c20074440c900c0c000800507848503e400164101d00020040e010281d481241505c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 366625512 1250 366624262 366624283
    0x417030115030b0f090907090b15030f060301060e0709090e0c0f1201060317031501020f120a030b030d021501060e150c2e0c08040507120507170d11 65
    0x6080384418021407402548601e40f82030000701000c089200d20000199400f1040f1001640c54000391000c20491000c0d000303403d034104040300c0d290104c1444103103600d40b500004040d03010318829940403e402d5282980103c02800c1408400c00300c500c0d0542002d020b024071031040041441c505078400748070050104055400600081c11280e54911020801c01a002c0700c01c0050065581d81400000280c030714284064003501c103401090712481d2a0307a907015410840c03034a042c150341107244000b20f4902c5c045495003403e40099000ca4803100a584124028000040850741601c2035210040c0b24540010b4900c0429103e1080e1400c0307030780c84642c00c8500060311a810343d001b101c00081400110b00c89409809240d601404862030904440c1e2802180d00c0c640b8003c1101c0da503001c1403242ca420581c01900b030000d019090214070781c2025507032559150441e10a020750001501c01030803c020003404400002c0070420080f81401c6500c450668503103c00c042c107800410000c2c0001400b000d000b05949101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 366626762 1250 366625512 366625529
    0x100809070b0306031c030c11010c020d1b0f050c0406051509060d0b220f02040f0e0426090108010e06010c03080c09130f063006090c03030804170301 65
    0xd40c1c030300403a00740e4580028001c00e0785405180c48880d40f96442e60a00740b0340340825070f00815415805080503103800000e8281e4001a41451384500c130468001403208403444052900000192100c000501e00c491009001088050250010710034000c00141c075403052402154100b100070740c0c4404000c100241000b041034600014400480580340c140040e05e02905081008a1a485040005448843d810340340c220120703100d0166030042c4403503214415030b48881000c114602410150010120311151243c0c0d0b0005080c1c00001b400c0221010001154802c001109680c41d2100c0c1030000e080d030041100b182c0081d1446000240395a101c0c80314a010341d40685580c3c00301d81664a0440d00c8941c020300f2002e0b44c03002089106d4054442e0b0459965002e4060b40004000c1c03880004030040d0f580d0341c1e0003103003480002484000d091800c0c00c04d8041c1d400680c0c0040e040000c00c1c2c43d000028080501d0060401e510510f000406d050b089001d052245218800700540031220390a05d910302c2c007080c001c0310340c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 366628012 1250 366626762 366626773
    0x6041a090403210912030608010e030403020618090f15010206040215070c030b01080d031d190309030c03061b0c0305031501050705072403060302060306100318060605100809 76
    0x2080c061501c00600c1188079103960f0300c00701c00b0103450064038032545040311030031945400b103048a40c2c18860500507081e508001d1104940d0580000d640340141e000c040d215480006002411b25484404108400710150000c2114130b850b038020400c40004413850341c4280702c0c0416241640d840860003a2245078003c3c90854103c001060360409600810000c13a20b940705500c1c04404501c017004054028800c0a009000c20000c010303009059426201011510300240c401460350001d011035420380290142c2400b05c2c401d1080e040807200c102d100d50010b04242a4000c01205029040d00043d070602c40c1d80c002030224805485e000c42d03020540140280024105001295030410121019244444145030050401e1001d460725800d001032940311007101d4400c0f00c00c081300300f032031020301c01071200381402c040042c4e41c59900494414400109244d03c580340ca28541610a030003540112421045418600e09412262410000800d5240070f03c61040b808000c4111440344290803091090584101030503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 366629262 1250 366628012 366628021
    0x203070c0f080d09050d0f090b09102705010f0203120109020315041401030209010519060e0a08010e06070813110607110d052103090606010c0c05061206041a09 70
    0x1981140741000c40303400b01c040110740b60281c41802004038450242001d0200a194010081c18900c050302c170700c20502089500c10004103088106403060200e06840381e03400c01c09001d0084941c043c0c0da43c1c2c4862400e4510b8900e40d0344403e14158501640c42c00e03210412000395010382665640186134141081404900052080d004240c0265070410034081c407900304103103220001016101181c00f00c40d000c4611740010001e51030a078114500624040d682c030f5004103000001c02800e03450324000c3c20f080c4140042781680325251002d1640042415100070008601010740c000d481c0d01090703070583d000420300d0001c28174618480c81d20b444030030350011042c1648225030062103a147c114400c151041030f0201000b80c0d403034a8001a85886030700c544040c000c0903000011a40c204130090505492144082c000c006502800045c0f01303402401c02d09144c40303503014914100d840321919030442d07508600c2c00700d6100c000030f141e4840c20340140802c0314248090700904104d2820000c5c20308200e9030040100c000305 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 366630512 1250 366629262 366629273
    0x8090a030f0e041806050a0207080d05040c0b0703020312150307030308060a0e0f010602010c0318060504050a170c06010b070c033c1a070914120d030e0f010203070c 72
    0x80110715010300300710742c61504801c0000c04441245201c01c004581d10444082001001d12415502c010100021400c03c80c0507101c6200740c2c0220898444030a035602d001c07405100f040c401e000c0c020450382c0e61340c6540d0800d0f4a8025204e0700a40c8000c20000e0b580740114200d070b210001151000580a00200802451a00c0c03c482046000e40030b15041500c1c140003050300c0714540c0c00b0a10880c000c129a0b1519494580000d086070740440c140d13401c1601d03094141403520200b030303105015140c0050002c9600d4070384d4141a800d05103a000010900c120350044051078099000140c07440c0e041c180d0607101e05a03600d0405403501e00c42c0050017000814070340c02c28800542c01900b48545c030303800c144c1001c02603030401c00a070a1301340d04c494002c001011400c0d081010802c03c00107100c8104000e0a0064050030060030250071240f46000e502c0c5921307000b4040280a4803091680009450f940d030450300384d0900001e0140040c12080111880c90003031b1083c91041030710500840b4040e00300e0fa5103540300ca012a07280e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 366631762 1250 366630512 366630527
    0x1030903030f0903030605090c030c070b06130f0c020708030c0304090213120606090b01030e0c0616060504350a05090f040e010c08060409050309120102040f0b0705010c08090a03 78
    0x4509255548010b50700a894900c107450039603100392070015503a810142048418900104550b200c40c9081040111040e20742090319540c40d482142d07150251115800030f0040c20800d480290000d00e0310800c0c070402c40035a0045100b079516902074030645c0c3d445081c202d40300d10035101d2808150b401000100b044518a40c010000344542d80100e01900e61140503000c0940a5401e0550b900c546951003400341c00303100d00c14024046800d080400100c0e0b40745c015291140040802070b4414400803480c900000741043d0004916640b060742004140b903d4602a1000c0c00e2500c1d0054000c214030040c101011000d03021a95000d4dc00d01e5003904080c41d10800301d078a07501c800314a40c0c01000f061103c107030580b503602034040d950b5204000071401c49000300c0000d140e40d00040009118034101030548010400100888241e403109864508078a43c00c80e02d410301a01c25a40700b050b418a09403800180440382da0041e0441d00d12460090125942440e000c403200c14007a1503030b800306d4101002080009006130803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 366633012 1250 366631762 366631781
    0x70f0e0906010215090d02070504020913050601030605191a0307020709090201090905040b09010b100e0603040c0b0406090e07231309020a0e010e0306010303081b0712030e0606100e0103 81
    0x4981010402c01c8140104a0307094801440b298041c0d000701b001c0380e406100b00005003000b50b03421410000464000b42c0d42da049032480804055071640812826442508081c020346005803001654217249031440c100c411140c8034099070a10003004403007162840c0422a4012980c640c01400117a00b866007000c001c0180481c102d041c001d800c0000510b0f07800074080c151169003e00c2003041c091400d98070490940d4482d8a00e54490101521a003048a800c541c1e11950890140d804070340703955a41c94110810b060301d40103000e4901001c68001140c07544030591400717a5607806000c215a4586610560b0f04001d2051000c2441e030b815110f4000344e40b86d05010346840240100e07494862030342d81e03007488100d0380711052840028581e52100801e650304500840c2d030455041d001407007950b256071030040903103501414000c1c05020340340450340001041e00039140e09941014101d6142214154050001e0504164900c16401650005009031030059030b07400c00d21031684c0b1000c1180e45c0c0000114014100c100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 366634262 1250 366633012 366633017
    0xf040213240806060f09160201061a0a1218080c100f0b0f03070b03070804050a05060f0a06051c02090c070501180314040f090c17041a070f0e090601 65
    0x141c0140140901c07100d480303480111940d03540d14850400d0006402c18900400960003041c4811550429456405141d1792003c03440d080030a00e01c1100c9030403030241903550301460384420301485114190140c04014280039441d82c4802040d0402404940242c6000d482080c0c0990385105600c00440d4001c0700406821a1340c205941400f1415524130302240c03140074014410703d0b62410001e14504101c203c005c803100e01100181511840c0110089062000600c007008104101d0081020001c04100c4200300f5940802954007510304440c9100b02c50303604447d010011805d0007000501c41c2016000c2da45024a00000300ca2145001c4d02480340081d4090480008a4820007480c00421020310881c0e0020708034a49408209209044c0242203184200942d480c01c002080100950002050a44220b411100010401c03046040060307650101c180e010404010101c402c0208114503801409407400300b05a0300034207604c8803501184c1809410840c100490300d031500c98192450840700c1154400c1052 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 366635512 1250 366634262 366634271
    0x1719031202070b0415051803071e0b0f070306092310050a030f060506030d0819060306110304031707020c0603100b0f0a02070905191d070f0f08060f040213 68
    0x70fa540b00701d2420200c40c103480c0c1c00303014280c1c90500840c6000311034008088441c401d80d82585030403070f5501da2048420040c2045100344100c50800b0410044140140d0841e4881c90a0303d00400007034003001040340d01000080c681b081c013140d00c011030b2050644928180c07401b200c644038010640b2500c40340107400809004d002c40c0c00051541c0c0d13400440c01c040d500c2000f06064600316480d18106130761010300000c1c400c0d003003070710945000d41d40441101c1d4451001c04800b001a64039502000c0100601d4101030003181c2003c807102e1420004e140110f0141d4880c0d07072440f4074140103e441020240042ea0340500580017a1506d021a2800f140610b4000c040384500c00c0c02c45a80740b92024841d40101d050300d5080c4030104034110940d4051110000409080740c085c0803600e40859041c692003000003d0200341d0b950344078410f51350b813101252403e68020a0044640880e07c990300800c0d80c81d41489003c401c620b0020002c07c004c070002c01c072140201e0848106086540781c035402c102c10f590903120b800c82000d07685d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 366636762 1250 366635512 366635527
    0x3507030e030c150c070b03040b07080a140115120c080c0a030f091a0907030506040204020a050d052707151b0f030c0209091f0c021e071719031202 64
    0x30143c0000441d40140341e15a95541d100002c6801c0820070342c0042110700040c410840400c070b5500450341d100c0020300e4905e0166581114610040c2044402d6408040ca1003001080003c048066220900800d4850174669aa00040e1034191152285101d00081080c0042040050303880060308001d4618100828155480d60006040300d28906060b0340c00194880005000b0050002007500103180302c002d40030150650720f07443d43d070340c1d0042d0000b8000c0b5070000d40300314039910660503500c880c03144002c2404241040c102d401507010203e55102885250100403120700003000612000302c0d003e00040d11f01c01280d420041ea440404c1c000d03007031340d1400600e910b440020031000120302018480e88401e002c1541e54018040803030300080c07144810f17a200c90b0010030303c0c00d4107900c00e4000001801020441c10ba00040403810403d91452607005504410f580c44032045001c00c1c05800c8c2c90b00510400b44840f4070060403680c910850102c41a0b0859484034900800d21550281100784041c90780540341591 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 366638012 1250 366636762 366636769
    0xc0405090c0f03070b071b090f0606030c0219021003020c0303070302030109060506030402280f08010b04050604060f0603020304051905160e06011706040e06043507030e030c 76
    0x408449445031a00810003100ca14a00059890b1040000b03a004120003030170040440d10070303c24500054900c0c58000b5450420344003c100e000050100300d501070000002322283c00d40a0111030240c10301084c10701842036200d62002442d4062001143c4000c900683c594003403052184140c010b582c10150200a8170940c11001c200442c010301c82a40c005a50b50f02d40441d010071658903421891050704d0030010b000261741c44810703400c0d03144180080511020444580192200300641c000c042c0040002c40009a50b00306500c42c0c40502c40c19581480b4940e19402080100d8000340105580c0081645040c000c40e07210b80c0c081c41e03015105808a4480384901c41801103030b1019400111050f5100b04000408411800b14500090801c40000c00d60340c01c051001902242448900c920070104500000e103ca540755001100660b0100c010740d4001e0030f103824a40e62400c0e85044015030624000f11011140d80c02040c60440c4941041d801800c011107036404440c078017007035001c442d414442c642c0144015034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 366639262 1250 366638012 366638021
    0x2060f0c01061203020d020d14031f0902130b130b301f05010203160f020409060b03071208030a0b21010203180303090706050c030f0301080a020406051c02010807020c04 74
    0x30a19440480007483e464024505482c2142c0d0004640128a04207442c541122001c151540d400744942c0d00c80d40c84162000c07455160184800f80c105a0040004425807298000c4c440c0304152441d19152644841c81000d0341e10985122244a89040004101200050740608061003010300c41d00020b07081e40b11544076919445c0c070191000c0107e001404103074035800748048961507070003800d110203d04d89070003c0c0d02c80c058203280f1000c5118154030003007004540ca1000c82210360003041080601e0007400c003c070088c04500591070092040c5407001c80d04120b112003603000a17a200304941d15550359084050b000e05004200c09810650502c0f40340084c00b0600480d11017100da4000042e240c0c80d013015030707910205694070f000409400800500481c50004980c0200b41c6100b030409958030f00944440c54550b1041540300b0303407882400300001c5901c40d808111020528000c4605111076622041000b0081030022028102c440f503100c0400015401642000d0b0f00034042d0050301d1060380c8201c0410245c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 366640512 1250 366639262 366639269
    0x7050604030f03051302180a0608010e2503200f03010c170a0b0a0e22060903260402041a040c080109050c030f04030e0d020406030308160e060702060f0c0106 69
    0xa04982d030380c4161641c54030038035500c00d0280d03034002d075110200e8000c6100c06d010400318039080d0365540001012140c1c0c42d00140f0041a81000800c214402201e140d0746490301c140390110941800f03002c011080400c0d0780e682050702c0c0c010188021800d03020b80c2041e00c05150f042407940003200700c00c509038642d400303200d0078008007069103e2807440140343c100303c0d41456009011400b03852030007000710104d895a4901741c081c1c5110090103041610aca18464146001d1250305821001c0e03813120203420030929401c610b040d070b8429120071050500342030a0b03d1700c038003103445442440b001d20300024007d40f4141d01b1102c5054070350707004041100301c8203021800390b412203014000800c2203140100100001c0c2d108031340d4807640c05541181103041c2040780344488132010b000a02048900c54a4941c3e41d50f1315139a1138005030380200200891540e9240240000d14112826a550389800c4005005e040c000d00740e9000912008168a1516900b54200442c50704141c015001c152014059000040c03024800d04000c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 366641762 1250 366640512 366640517
    0x2011103010602150c0301080a17040305070f1e050d12030b061b1c050702010f0e060d140f0402030304060507060207020406091b030c0815030f06070908190b01030204110705060403 79
    0x103407441d0f04004a1040350103800032a1709031040004200e03151002c1642d600c8181e124035030408401980142d2a07070b501a27504060114054500f00160440c0d00c81c10950440e101140b13550002c1600100c800c800f21b509104584d0807507182a55400082c60311140c154054005d03040000e21602341e18040340061b0421444aa49900c9411b0140300c1d203841000f00380d1280b2044101620001e02002c001045030054010082c1817010b035644a0101d18015103846180e00320203409141c0f1741142002e0500034000041d0004400002e01000c01e440c00c1405865038490358010f401149081e1800204484a621048080c0c40315503007408104010303543c5000728402850001404646a21410401c81d0041161001503040c10b1400c4100070741940c02010103a07100c00e418483c00c031191017800110707040060300b58200d41140220006c000c15180c120b200c0d01d0036903509030120f81c102c1e1181d454040c0e14120450000d0520801d00b0f004100514143d0001c555606284000e01d0400006036a901c3ca0003a003a40d00301c02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 366643012 1250 366641762 366641773
    0x705010f060e1911090603060607080304110a0602010902100819150f210f11033c3d0b0306100302090f07141605100c02030f0a02011103010602 63
    0x2c055400c1640e66040f2400010442c6112039a2812403510a038110f2500a02e070100c001103040e541c840940362100d81045400c0d64030b20345803919007404d14003284118820200085c011440c107105204644a00394060301c29107024000c4682034440d00802044170481002041028954480ea40191107001c0580b00da072054250a0010040b0026044d4000c4900258030350400d031000d9262141040c102c50300f12500d141010010700300042e50140f060001c0d50503100e1000110122100c1c0401e001d2046a603110f500f000f0b400100048907294100048400682c1c00301c5400f0010401c0c185129000c030a05944206803a0540228900700270f000c0e40d224500c1d2075454000b0043d80c10140f10041d400481c01c031040039058255030006001e00c102038040380c020080c00c00007130400c0340240c1c58a0801407845100c0c0d52507919441103010144240c0c2011202da005420070741d00404254000c1d0714417003005401a40c2860b803040c3e0340902640042c0000002c540d00c4504d0b0405c0e0a07030003001907000c1e00156000c0e04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 366644262 1250 366643012 366643021
    0x219051c120c020f0a060903020a020607030e0f040b01020a0303020c071a03010e09030423040b04060f060e041b140f130503241302060403061107051218060705010f060e 74
    0x40858046144610030354001d0350609010b9500810405c000b02c2d80200c00081031030f29400c01303c1c80c0280c0c0c44402500880300061402c14540c2242d00c41c24800000c44441c4900c02503142840141e0702001545805640111550400203020b90003510000381c01c502103c1100d07555403540c000140c0313070f4080d150032000000018800c990004030244d5008042e20011440c0a2514040244143c011454000c805205140501ca140c0c0d80d038018403c0c000e0020003e100c102d4580d1009501da43d80b030b22450b0041503040c2d8104007581054091070011707181040e20300400025030b540c20303140f059003038124242904041001030008a0602d02a14040031083c2c40050020f0400c404c0c1445c24100b00201c045401201e500c40451806001e21962300c901c04000085100880d440401c3d1301d8000c50704002e00c0c0c0c500b0940c450b40c1820030040580034040c0280704035145010305074031b118000d04c1124030120b24944a04190719030343c1031220081c01071520403400041c0c40d1540340390781c0040350351a80206045c8041c0d2010702 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 366645512 1250 366644262 366644297
    0x16020a20060706062c010b0f39010c0804150203091002030415060b030f0a0209061e030406110c032502060705070503073305040b0313150c0219051c 65
    0x5030110000244405c40550600b259002c160081c4204503030000000680490f128501c14920b148644000800141c140800c0c070744d0aa0b407000e01060280380d50f19003000f42d00d42c948214040b601440d046016500c0c0314415000b000080c0d80024000c028601c20303400488c00451051004520480c0206080308010706400c110b101620003da00084d00803a092003400701900888804030307085440400700603500c040c44c1c400708625004062001450029035551801040355a1000710f10803446580204507920301039001b14200d02812a030000f1070b60040c40390f00c0c0c80d80c0414002210b200060349031000444040e600048039548861421a042e4000240c101b002c1e0408014510140c00040101041d110321091410345458000310306908170845103002d01081d501072000c0324054100300702c440780da030f182080f62140f43d60000e21040350607400003041816010018451034100e10034990103400d165a44071003400030f140603501b00b07580d80c0c050040e030a0b41c2d0800c4c1c02207222401c4460b480d40066030198298a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 366646762 1250 366645512 366645569
    0x2030c09010f051804020622050a08010204030b060102070f150c0b011e140334080610091a0609010908070602010b1806010804020910180516020a2006070606 69
    0x144040d80d00d0082c071005958407c00d03202e41d14004115840d229080d100d04030403580c81903001640090701c06102140455044d0014015031f4010b13910100c051702d03020012a84c541042c81900c9541201100038820b103e080b10221581001d00d29044984803000d86550007005820790201103070340d2411146180d96901010010002d1001403420303c0c00e6605840480e460300c8a082101075244454140907241c01e050000c51008000140040c1180b913449110059582506072024022400d4650001400348158010b0302c412001e10380a01c01c4a842110a00555801c59116103051000362070000ca0542070402c0f07182c0007400c803540081048141d90040c010302545490f070700003484510404001c0d090342c2000c42c1c0354219605483c0c040495440020040200c05241c005840703002c80300c40743c900d070140b07030340c110314062166041011101d0032518010b9a50740c407100d80090140e032000200d040381030380c0101282da20800290416181c0b6185641d080d007112102d801c40645003503041c0031480008040002c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 366648012 1250 366646762 366646789
    0x1090e011a060f0705031c0914030c0307151844030718140a1205060109020f07080c0106030b010b130506030604181103010f11090d02030c09010f05 65
    0x8807001a1444010542600c82d000500010300700009141c03003005801c0084500840505d41c5000c03c04000700009400703012140800e0b20300302034006100d114003202208580244500e08001d5240400e80c1d621200101c0302003a9016016941d00100ca03444512002081d0025128130030101c1800c400c1a03100300d58041184482100038070301910202c003140c28580365402900311900040c0c4071380d20b0080845064038012001e05100f0741c43c110020380140e200c001e080082d4411541c2302d40c1300c0e07203601d0408140d0080f444041c001e0b0388928010422a01c40398010100c0c400c07804004c502c1d0079503548070101298001501c1264580d581c000400c1440a581c1566014000308506186001c82803240403d65030783e1402050310540d000008500d6660304c0b580044245d81040321030360410007441c01d001c045000c040301d4150195080c072001e03200041d40340c0308080c080da2009030190308040c0c800b814800002e405040c00c9801d4800c0030501009070381d032a0b080600814541d00840142c42c140004d10101e24814007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 366649262 1250 366648012 366648041
    0x60e010207020a180b060705240c09100509040e03030a110903030703050a17090309010e09070c14070803030f090d03021303060e010b10020d03060e010305070501080705040b0301090e01 81
    0xc061001642d400300c1c020222070500c203134024800c10b4000e1010003007503603411541c2e20520010303001e400c000000c1000c200c1e40c02ca0014000d18080000c2c1c0f024218003003141c03001079a05003049035140500d0101c640317024411440c503009081820f40f5003c90101d40003519000502d80c40441000884070890290801c3c0841000c0c1807800e00380048040381e84e9014141008013030107000301d050350b500d41c4212140d00e1503419191980e641ca042652000d5260391000040a000035040480c0c50300a0500c00c2c1e8540c02000b0560b038500c12118203440381c0e5400d9040c00b4032003845000e1800001110f00e0100301035400303a456030300503038804e05002080030320b0059104140c10900d4010b010311410008100107440480e40c01501c00301e0004d1031346202c580100440710356940e01480c8441001d414a900080c1c0c141d40003616101000740c19242d916541d4000024071005105500c00300742404154803075614290825514100a400e040d00c030180700b0038580090700650991a541e4000785035100c1300b401201d2005034142c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 366650512 1250 366649262 366649267
    0x50f0f0c0a06090303140915040e070c081c09020901091b1805060c030d0c02030a121404081c050103052407020d110a02030102031e0708012d080316060e0102 69
    0x42d010740700000c01c0c40050f040c8494160b240808100c450203d0756242c3c402820510010003030b0500d214a9040350160111243d03201c4005414980104003d1803810707040035015007040c50442c00020381c0070749044400442600e51000d80e0040e191180a140680286c0b840402d083c41e8449044181d032803540417030810850001c403000d0501185c1d2010074150390081c0c075419550700c00382e40e001c0c2c510710902c60b001034590701d400340b86a24542d02102525500c0a603503580084035240c04200000d4501c1011507400d220600f00116000840150080c0311000b908840c0c42d00d4142840301b8401140c4099006035203903084502c010507001700d8205c412500c484916800750036800c1c07484000b07507665446521002400f09100381184a054104a005c3c50341c2d40c001c0007035540b46000702490003011856a189007102c628540803828981c000c0440174160b68551320aa60707086082100500250005a40c4000b0070440c004003050006041c002864203c110001c007030300d09a224074111048030038613000f008090344107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 366651762 1250 366650512 366650519
    0x10b03060c0301121a07090602101e0203061504181d0a0b040203101811040c020d03022a03070b090714090a0e1606110312010306090f050f0f0c0a 64
    0x80344180ca0540384113401030039880c900307890300b071021840d41000b005680c08064100030540382e1100c040016940e665081d9a0400c00c55900581a1074a1a134030004c085180e1140c0304505446a0185600c000000c00761840314064691007280c41d40140c0080c540c2e0300e855038542290102d58042c61026900050500320105202805580c0f0796070b03000030007030128504d440414203664080068030302a08230600c0411658000189900001d604002d045510150441c04c3d0800c2d85007a2081c0c03545410320707801400380c24107000001c500a5002c0f1200e2102c4083d484a11038a0707403140d11451000d40394000c02155210082c0c02d1035070105074004e08400c4d041d8002501030122851901e000940b110f0140c85011250b22101c050b0b9000e0b0802c451000c003144100039411681142420321001154001e40350b50100e007a06460994903880740707011000c1d0340309016004000242c2682c0c48028642e014130010b004401440d40da050078003a143e102c2c64000da211803881c0300c00354001d04c08024885811150036806514 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 366653012 1250 366651762 366651781
    0x1020f0f0c1b10050d1407030b150a210608060403031e05090c1003200a0f03060501051b0307050111041403070e040305130e07050403060f02070201172214010b0306 72
    0x4810315030f01c0404c0b50120b5011108034450300010303180d01c2002c1c240f003214989a0b400900903c180740030319101c1d4a9200703c008441c0fa001044920310705066035000b0f50704281500d82141580018000c0d0340c050ba94102c00903c51a040c4010350145201c2d079404030700c02d9501c0a20001d08403604540c11012494a420301c0101000001c2c42c1d1105241a20030510400c2c0c070342c1d4290000c5c81008142d08405c61114540c8141401e03860061503a20341d5503d48010111080710304400b00c524a0054501003103040010244030081c15a1200007586da0204584c03600c14207689040c03d481c541030b5050060b100101e42800814405915231f4800c27141500100300d41464110301c50148100584050b0604c800020000140b007611030002010b0704003a4817580e090b00b05544009d009901c1448150740075441e1003c01c403112002402201e15480d0141e4401d40e08403000100d400d0541c00250407080d640010000c60642004148444440903004188203100c5c0002610201c1c01d4440e4115210300c250440d40030000c0001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 366654262 1250 366653012 366653029
    0x110a05070f1a0a090e0709050303040308040603052415043201020f120705010b061209010b0d03021c020102130605070b01050a0f0b160206460e0301020f0f0c1b 70
    0x542c12181c0201e06c2c0c541c41010740d0003014a40100d5014080094044244414440200300b121403545e001c00040c0e4a141008e184200035040d00050301701070f41c1801c0c0880c9000c4540c0308400c0380002441d854641d450410460299040201c0c1910001030700700fa600410301c410404821100c28009001042040c002c20340d2101d500c0e00c0003840680000c502d081c00c1c041c0035805145030002c0900b2540c0e23241c28600095411190440350060070b907003800580c2c0001e04007003043c4100207a241c0c006100848501a06945e240ca001280a04641d030074401e4801500843c40030f60020090707501c4007541c0d141141010b202c4803505800241c003c000000c010000050b0308036806045440412082d900c0320315103010341c04002000b02010b0340c0003501180809011018800d5100d00680381e080c030b00c41d1170320920341d0400c40c90603030141c10070009090000c0110482c02101140e062010040006141c112690121025900040060703810280041280c841412040000314514441850001c2c036001d542400100e506 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 366655512 1250 366654262 366654269
    0x2a110d110c0d06060b070b0109060801091109060102010b1905031e1c020723032a10110604030302190311070809060d051602011d0607110a05070f1a0a09 67
    0x101003082c0028240203541c3e0115015000030603000f66a20343d64102001555001c1c0036240700c00c2d1801c1800200764205100c0c0805c2d0030303801aa801c00d0628894104610007200401040c190754a0700c0e00e00304107941c0d00144084044500031281c040ca810b01c8249890a014040350b41e0380c242c00520182001103002483da4210144d2484203a03180712124000ca003070520603840a210300c402803914142d4030f40c54940c54400b0040c15000c0303a08075a40182d000240021040d002030003000b05100042c007a042c00c04450122486500740303210400020a0f1040c6800022201600000e50110742ca03030855111544641d40c06000d071500340008000ca0150125074850240000c1c407480002402c2070903a1104c8003602c040d1051f00c03104002502d004001410024031271401c0e00015480c0103030814901e440c24160510240c00c0c5001062540d40741807003925000e0014a089038a44941d0504000040c0b0130052030016089880b040c0188524020081c0d030709100c43d12a40000380710910140e000d840c0d018003580f044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 366656762 1250 366655512 366655519
    0x90c08012312100501051017040b10031403092706040906111b0106050402121602010b030a080d0507050726160501090c0b13092a110d110c 61
    0x1c188a00010394001c07603022041014000c030364000f485451036038041d5048880c1078a581050541e07030310017203804502a608841080c0c02d03050200d0041141c100d8040d6210707030102c4c020118103449490320003205c55003072030f841041d40c4000fa0101c118144040c205a034040511030541c944101c550600fa86c8031001401e01d400346a48801d24801d006d01500040e4141207003004540e039030100303140080b10503104200c08101070741c04c0803c0010181418800c55609080c2c0f100c5400098688030f8111144010f520b640b0411992070714005a41560203004080c0c80e0f84c0304407100c0b40c1d148120b002a0007511001415034040c80814071003800842c40341c55040b0380500c81d00e40700b0004900c6104c58841c0c2805412000362100d031141c25403108111055000e52030042c000c41c1c1403400da940c0c95149024034401d004010300b030022401400c1150382455000000883c10111991441401440c980154000021688030000f0440c48503020201014016a124482d8500c4d01c215014184011203907182e9452110600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 366658012 1250 366656762 366656819
    0x80304050109240e061311240403150207120503040302070f080a140601050f12070b0315010807030b0109260a05010212010f14090402040e011104090c0801 68
    0x2003140030750082c00d01d19840001c101c080d414036414400d84569900d64160468a404500103c0c80c1c00015164401d007500200495410a690760381c1000080c610f16694104000c0c1120300110341e0340301551000e15000d50104c40d100c030f285040c4034510b924a04100000c49104004840208084010030030284000b4181199a03458500d030891410160340c0c428140414040300208030200c000c01e1100b809405500a54181d1040020103030b100c0e04284245540702d00811064a028104038550030030a81458040c2c6044a5441c8404c925075801210740c4904a00720034110029988c12030a40da4100101d0302e01000540d0301a400600341d4200d0307014501c2c20785280d004070741c9091140424801c400d1642d000ba604c01030036624001d400b0f0b41010100c03038050034a560000c03450030044a40101266030850150021500701b10a01c0545070000c5c00a0780c2180d203c0001021814090041c05910007907400001e640340c0c500543c00c422100c000140d1030800024800421507204051110600b100d00c0246050307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 366659262 1250 366658012 366658021
    0x40c06050a08130f0c08101a0306060d0804150f08010902090f1201021c090311061620030a020f0c0f09061005130906060e04060312030c02010204080a0803040c08030c0a0803 76
    0xc4a0500c92000504170b50038140080307001c0c0d60210740b00c0310044100c0814848038100d00164404001c42c1c03283c03e0f405038040300014800d894184d4000c0c040c0c9000740b405034502a00c07485002c03c884080101400400d091240c1014029400f265a5006001846007142000040070000300c00043c05a076261013401004000689030b0400c0d4100c4104000e07a0020500d6001c007070b0004006000343c4c007070a402160914014a40001010a500c1d100c0c1040d10b031220a880c4520718145c8070100392501c030740d48894000d216040086000c0005210f0500103070001c00084028095092804d03608100036030041240c15440700494a5480391280c0101045458200c040480ca10440d264003400c2d0210994015081e000203540480380c1c0540252541560703541c08100d911800d01c81502d540784001007286429a00d51107071b141c420741c40250701816034400946455030f04d680e4149000ca030210b0907a08158000148001c0020850284006128802c046c40c00c00400d00f20080c0c5501c4d10180103001c0000010004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 366660512 1250 366659262 366659273
    0x13060e010e150f070b060a0f030201141612081006020d090b0c120f03070206070f0801030615030b010b090f03010c020705010f030605030703150f0504050d050f120a05040c06050a0813 80
    0x2d83e110908500b14030780360364840c1820840348000f5540340707004070080d10020030808100304005050341d8060310781428011041d200203041d0b03804031401d08041c1185d80612800214010400d1001f45050358480c01e95003020b1041c6005004550301690565001d24a031003603040e00034503000c044442c10034200381c50f8501c040020f400c00d43e411a40103007105000404540d85240540950301805459080300c019a80364bd00554135011242180c0c00404e8000004000140140d0042c60315240d0070700c608091540d0f82e079649010258281c01010468a000c51900d0950070303c503601c0039801c5012002845516181c030000784d100c004c04d001d01030400a1205280070024003079008800240005000c03a0400d40d5039041c140d00092017140001c80c018140b0f0700e092001c45460081d1401982c020001d00840748102d0016142d0342d10694529815920a10200007000b0508858510030101100b0110704c80c40c1502d0020f04001c1107400041c00e0040034060800300303680c401d562039480484400d15400000950614 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 366661762 1250 366660512 366660517
    0x1b07030509040c05040e1608190b04050901060515042d03050d021c110c220f1a0603010305070504050408040312030c140c06040210111213060e010e15 66
    0x1800d400c98103014032080041c0c3c4c080b0050003100c041c2e119100b0b241d00d07041040070044450050781c400095940003c185030014032101080d83c549541c40000704900044045405e880781152000c40744d0b55600810040b07801e20a20482407440c488400300d1405c0d060841e50300813030412007031030704040700701000ca0030510036006183c1c406190400100c54540c462001c000b5a81c2180c4000403142d44200510880c210380514030210203030b2150000b03071103034421050922504900c003019241c50011041c4601004140e40d11a1a101078030302e040200d0300c100741c42402180d601301920484c0c0150305c10030040000c40c41c003144030802d54030115004110340d1200e0401620070300440d00040c00d0340e0900c2854400464240d4480424036000f40c40310050340c3d20301d450300328070340c0204408280c04d034101c0d10000d40140341c0014103410000e00750800b040d1034401500382c1c5103402c001c04075160411381e00050700884c104580d22003800502c05850520a0251810002000315a60845444c0500c002c10f103070200c02c1000006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 366663012 1250 366661762 366661777
    0x1a1c050a021503040615260106090e0703050c010816081003080d0b01090b0c07050112090501150e090c0a0303050a0c05160609080c030606150f0a050703080a051b070305 74
    0xe00c2142850460360403941c0d031040d1021158186000c91904103541c01201b02801c0b1100d20200c03d01c1003290501550003070f8000000c008065598810210311941c0e030344240814804603200501e080350851800f80d1900d00c0400005041c0900e42c82008041c1408110503400c2d984180f91522883d21000070748070b400d10040d04010840600804c0555504c10654016803188030240d8803001038035521851881140b25047c421050340d00004010300aa501441e002e070400300e82c600c8001004002522510300f1a0b00154036000603001000701044007807202c2c1d000c660400c208002402c22011048005801ea0700f0300d21004042c40400b04031000224064060b046042d81c102040c0c4400c61003a5092901100ca175000f0000031a038000c034041001100056002d99140c0c1c060010b0115840344c1c0708100502112050080c4036a40401c00081080c5d03000010748000c0000340c4a140c0c8811281c6005051118000c00040e8110300d0201008000072554546810214030707841084d5990099040c1280d041c441d200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 366664262 1250 366663012 366663019
    0x60f0417010204120b061f080a150f0e04052b0c03021501080c120312011e1703030a1a010801090506011107030b01051809030d0f180b0405011a1c050a02 67
    0x5800400e01400c0e085052103000202c9481d40c011160008103907d280008440ca00051300800010344004102d902c140c0440302e1701c641d050701d1f6076a40c2d00c92243d8501c1c9a04203c041d500702c0c0c2c0601c82086020080d8480c034a292100d1503400d2400804284821040141d0b9407040241249054060600a100005041d800040d80c003489603140c4202c159140354001c01240514101c0c2003100900e074011041d2000002d01c110550b02c01d901c1d01d03c2c07a0300c0072800401d0045000009030300010709200c60003d070103050a1202c001d10349030321701041c0a004440340200130a03007003541844181c109a034031040e40d90664000070000502e98982d5070040b40c800500803411280e07171080841c04814003c44c0018281211002c580720075007540c10302c419903003d94080d10b007125a68406d001c1840141c01d00c1d000704c01001345407000011a140b50703031482d50981603512400c2c3d6040900b40e05020600c9401c1c000c7c3d00340e04800c4240100b46620342c401055405041581c606181c510840980c01000b100f0302034a441503070004e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 366665512 1250 366664262 366664289
    0x5717040b030f1602030703020a060b1203030f01140d0b0f070e0303070c030506060607120c05100614010201060906150e030a0f080a1706060904020c160807090b060f0417010204 77
    0x104a03602002d80283d03030f81d40d22410140b0030054890f1000045802d060740c035502400c0c2d404c2c803135511180644160b000281c1c1c4414200080c120b071080400c0514482c0b12264070980b0954500002030720619a240320b0240541c03204546003010601c070900d5140c100c2d81c20704800005591310701c41250803500c0380819a516000c00218601484807252030142964001d805644e039070307140c101c10050b8500c10003c00a046203090752400c80f80c180210f0130900414082c2080d10300c0805005114806c807055038100c1c1c00380304040c0d90044060351782489800d000e001e048004210072414110b0007400703070200c03240240400c40c00302c0c0c0480e5075071400d0040c1104241d00c107204099507070113494100c445070028413845000420000c0304842189803c056203001d401d000d0314441c58400a40188000f9605c501600320680c801c800004544e144504c002600400c0c4140140c036a450800c400842541c16030000e0520685050140c2c0d0180510310702214221200442000c00310142000000d001e0300850f400034042c1c1800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 366666762 1250 366665512 366665521
    0x1050916030e070b0c161508090c06040906150306060e041d03040603092105090405070201021e0c010e0c0609040e070915150813060c5717040b03 64
    0x11310000d001c0b4020800160303400e00f207800c01e60314000b510714454a1550030036680c4994485000d40c1c94140c10200c0c010031340d0440b5032070f007001c00c80725407040d84481c0d002c03a543c1c5010031182c89103820002421500385001d10071180f070850b0040600700310f25030340e030b00c1642d9444100c00701641e074407400440c9580e402c0a4a07100c0c0c0e40d80e08041d0080424003400c0d80c0b100c1c2c3d414660400d982e03015450440c1500ca80e1a500c2c2010441000d20008000c018022025503608200394a800d01c14860790f03c40e040f100b4503880750790780e008100b0982075490306985501c0076480b0108002c8150780b8002540c0007c0000c1e140014091403000781c4a14066065205248051806140e84a40d03007506401100703450051310342620b100b03501038080710700700300c115151003003044458444000140039802a40e80e01100b0302c2c1c002e101e50f00e40114140503800004101006a500f12800351400400c1e0b44007080316050090f203080b0341901400380c441c200034070603030044c41c0120b07030121056040d00510944000e0a0007595030b039101c0c0352 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 366668012 1250 366666762 366666779
    0x90705010e0d02150a0801080a0f061d0a0b01061b02030705131e050114100f0c020a050301020a0e100c020a0b130e0108010e0c22020310030b04082101050916030e07 72
    0x1005d4a4040003030395400002c655584000340d101c5102d6844825082c85049070740390440205880d44100c20703a00d42115070650000700400541c0542c501900001006525008024000048410201c1d14648241c240750000d0b030707070100c0c50400311a02581c00d280c05500034042140104079078031001c8042401c00060001020042d4030042c180c5900c5c190000e81d8042c01010012540ca507007440740002811004500110b03441041c10899142c03016111074111611200060700b640c10140403600014910142c1500358a031641400700d511010303013410503c0603d16004528140c14a0003442080d880c00100044a803980750505401000c070b42c00d198086507181c0302407034080c2c1640c180144141c0f185024001e580d141c0b004810401803440d0030f0404c15404a1210030004e5000101014000300906000001040741030341d26a05c9280f0911400d59129201140980a400720080c0003258024100052015484154103190841c0e4080c1c00030310b0a01801404030702034504140f503800c9a00410170001480e59 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 366669262 1250 366668012 366668017
    0x18030503090102093a0b0703021b010615080105062508130b04080d1805042f030105030709180b090f070609090c0201110405040506031905070509090303090705010e0d0215 75
    0x1107945200405005e6060140950002d0000029002c10482001718032094080d80c0105156410102030301d0034039081580791801c4484560003440130703d10314010500311562007082d01e4003410b8219403083c1407031039901100c9a542d106484041140400a0112044c030455000b91380140141c0c0090410f4580c54000c01203454000d8070031000c0c0d07482401d0040c62080d001e503047c01107005040244d465a42d1622003000054001040000b15000386071506445007212581d07070103c1242420140ca030b9a52400c2c003414500b05143c0d0010a07420700e450001d24882e10340c1c00ac201002608044511401d481d4004250704294101c84020341c2d500c80d11800040203034004820404071944104100911501c4860903070a032860041c0c04e850308601004140718900d4990b122a40111020b01190240605c103640302c91130500d188009e485550201c40104014070782003034001d90101d01900039604509001d14003e0380c2d07101074040c003810700500c1c03401c20849464013000814030b15001003d801d08051100a070301000d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 366670512 1250 366669262 366669319
    0x26060d02060d05040c3209072303010f05030604030f120e0604051501050a050307090c020c0909010915140a0e0c0d080405040501060507051b0a0f03080904050105041803050309010209 80
    0x151801e001c151a1090010150010641c6200b4114801b43c005041002c038032401017020f814003655140d03152402800d031004141400030310300d10941d01d50411440c6001200e50740e004500c00d900080c00c00001035846040e038000c00c1818203240f4441504060b42030080c10401030440030070303c500d100704810321400040194504900400c9071520b642c0702c00031700007940114098548c15074800d20302000081f506a00601380305005205441141e084c03d00061078104c016142c40c01140c1d151f80c1c0035418040c201c3c1110702d220f0703c0a401004100072080c3c1d10360413480c00800c00301d941580c400070400e242005005c0d032112400000c09400c4041c0d11442c3c481c5c0d15802034090a03000d68508400032403101d02540484403655008401000004040d400b0f0070080780e00c03103d02e580c20685140780000c1f00c0c001102e894029600c600362880e150f0300b051003440220341050344000d00c194182886c40d024020030b0000880a190035203840d0f41d4076515140040c2c060311410412642050458041c810820705c085c00e290101c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 366671762 1250 366670512 366670529
    0xd2304090c03091a1003111c08070b07021522050d181205060c0a02070521011b0e0d02010201140f0709090b09060d02030f06010303050a26060d02060d05040c 69
    0x113402c254100b50b49013007207440e40754401094800703101241d0080c0c0d4181d182d040007410000756a40306182c28101d41c01d414000c88030761501103090030070481240c1b01554040329a01c02041e07440d40001109021940203004101804901015001c4003c09050074103001d40d040300440300283d41e541342c014011071805003150400b90310408007142450f00c1e14a011a40ca40000c0240791036215089a2019644485104000d510030050005907940790503a86442145080b8000c1c0617030035022500b182540c00f9280910040081d5446000300d051700704401c00605007054840000c10440c0b440144d0043c00e400b03c403501560761010400a00840b5004e201d4170401c80350b81c80c00d001554541504003034600c440d500e2070748900400c001031480d0230406aa0454940010111400001c10944141c10314100b80c2080d00080e10000d401301f03015811920020a5a468903c4d482004445020b40a9000c402420291082c00100c12180a568401054540c0f100100c0d40c204001e080600d00318403441030a2090201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 366673012 1250 366671762 366671783
    0x1210c0f09060e0a03030513150206040309080f0d03020310090f0c090605040308070206460207080a17071709040b04060e07080406020d090f140d2304090c0309 70
    0x44680c841c82810f05104000740c1481c044070f096a800b558290030050221404040113240000c141010000d08010300301c454000d4002030400f4140248904c065811030320f8203038020f00200320751080004181d45000d14a207801038590700e0341c48e021a100c40c0254840d4445504021441c012000264002510070410b6110111000d55131075040da5035025510024210300003d1003a040981440401480da105d0500407260261080c81818807070420750507d8000111009245030070341c804802d54030340201d00d01c1d000400304c161402c004241d8821020034010b201551100c008900305508900f40c07050141c1c0a095010764040754900740b035054010224251085040500d400c103a801d217032081005584a0420b05403241e681c6d50401d40301d104025200f01d448580c204128543e0182d64450174102900c10300d441c01401160b82490400f0300700315100c0d088182c1001c2641540c03217030043c4540d658840b4510708120150f260701031902c000e000ea0707031100000904240803084800d92503804180700610803183e100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 366674262 1250 366673012 366673019
    0x19150608060c030115090302180a0e1f0207060b060a050a0219020607020d020127060314090303061e060d1d0703052a06070308040209070806030c01210c0f09 69
    0x60350740206030b0b45404811070810044c00450b60842e082d0407842980e00782250031a41d20340c00b180700241d01400c0e11444001402c00d00030000300c5400303400440d6145100820500340d6031040ea84000403400c0304486110382c002040300030030030290408485020020322481d165516900003a14581c0408001d40041c0907031991101001c042c00b402444154010f404281001c450780e00b84070007015920000da0500080c00f910207003502c044007008501c07030362151204918620300113028003501c6003caa180c07200005441000f0019800100b80c0e640080d04480e5800c0745101c9031880054111241d1034550051030004650b50000d009030448500042c0c0802c0110014101c04101a01c0380c0d00c50000800c240c00c6180b0007a102042c0c40b0032103060702050800c4805040c0a440051b19540c4440c0084022500342410403080d8900082c400303031310404a0425020610b84000002d48800480c5100c1341408518980303070302e24008407000c2a40302074030802c0c01c01c07040070f2880000e407540140c206030b000012042100403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 366675512 1250 366674262 366674279
    0x3010e0322061107050904081902030c12070b2206050f06010912030f270e09151603050705070227100e0109050a09020307060e0103060b030c07020f03191506 69
    0x28480c81c003d80038008060818007006245c440c054810b40711303000c007071021398240e0a6041000760652400e800842c2e403440301b62040d500306440d0710032481030703401d051110b840800d5100125983c0807510380241e843c1e0900c042080d900030511000040c1c24246003a04112000503902c80b418001e03c0241c0320801e1a5a81e40381d40f20503a681036000500144076203110700e07082030050314030298140070400e02082d400640c00080b01c54100c26408a911020104144800000103021505040284140c00042490030b48030014091030307116041020550f99900054099100c0c4050754a040da005110358180c0c401a80482403161480101da1100070f441c0e13020609001d900740c600d604031090020b401c00c00e03a1030502c481004102c000d22288035640c642c83e458005075001d0104501510030342e00c0d0100041d0040000604840301c83e00072103107a403010024811202000c00c180c2c0d003403550441d02c3d82000f582c124007090400586a42862a901014014104004c00620101100e0a50034010172185030f0741c6501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 366676762 1250 366675512 366675527
    0x1404120f0507150503011a0f0711031c1e0f020d050f27040b030d0219110406061d040204050d110a050a1d0f060a0b033301030f090209010902070203010e032206 70
    0x10160f41401c005040000e20080c05c252b00160000301915406d40740d0801008500d07010f03804e4500020030402010403400710310455105040c0c054981400404c03030039a8040e5440c2020010041440300220700307000e041c0014400c50b030074008030745103403a106048480f19410140006400354400c49c00c00310f81c01c415080c0080d14401031340f0964004d1400413015656020b40f40d4042800351160030700c140300c0e074195880300d0041c0c800510080d0354115900e911f820100f2400c0d50180034044c80399004020420031039451340c1403624102d4004110004201a900005a508025074002c58112050000020740074040d03444240c0c003941e18005202c020b80c0c50520b2810740c000e0448580383d03c0315007030605004400ba5000a1644003a5610351400344a5105203039448072528030000c0607140980c04120501546c1c540101b081d031441c00c0a043c040c5418036400148402d90500135500d03010307800304070041990360941001405108400603a503407048500d280d003030f8000b400943c09040e20f0b020b082c005061403007400b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 366678012 1250 366676762 366676777
    0x130513050c0423030102030c0912060105030a080a05160302010501090b0a031226010e0618150402031b070609020f0d03021b011205090d1404120f0507150503011a 71
    0x10722441c050400d0403c00e0216090035000c00c0280000240d091203480910046014070403c00340b41c1d17202c030400c10801404842c2c803910788080f500104010080c9480c0041d4269440da4032524141d00c85240b034a044070180904141040c450320a02ea0724002e244d0198041e6050300e01c60070040c44841c00701410f020928900d44001013016a030703042c8041c1500d200300300c0c0e40c140c120900c0c50a0040380444840c81d2001c0b00a800141e90301c0940b40c03d202c0503140c50060400c64200a5511502d9440d04124031080722000c442a01c0c003981e000030024102661a034440d02040403150301c2c4988840803030034070b903000f030004100480c000c41103201c001d807561628094484102d6403540c01402c0c4111031201d81e2400c0c4620841e40d5050043c0c201ca06907a05041e40103a501c1030803d40024048944580402003104e2560103208001c014104401c1c005480b07214111105c2541098007110555101d2500c6480c1003401d90081c00d10b00e803505003c00c1030703660200c0114100e41c400c01c015070b1516507400e01502144034245 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 366679262 1250 366678012 366678031
    0x601121104091707050d030507030e0d0e0f03100212090c0d0305090604030c090902090604020a02070308030915160e030115050409050a1227050616140313051305 71
    0x34101115403415410200341035100d0404002c2d1141e02c0890004243c001c80300484150300b04602c2034400325451f00c07500b0303488442840d06214200c0444050350325202c980e004c50302004405100405030fa12003d44104c02080701a0440d2442d0704030392a000025000210f4400441c1c1c0b50070080341c07400c103000420a00382c83d8000c2000500000070755099406a00012016800c5a010700000020402c3c0c0740b120401032482800219021109204012903030000400d100c1c4240d10500126141b150300141042c1601c2d8010052031303076501d0b40e5030190310780541c860042440001280400c582c072440c01c070360303461702e50560b88500114115010070182a00e0131403900c5e603e0403140c4441002503240036003055290354018815120360318241d480b0100c1214014925101040040d034a08103201603c0445140d40380d4448100c5e08028103282c00030707203036100c0d03220a55014101d10b4248418070800c0e44140324004050004c41c2e135a031001003400d845c882e0f02ea00c42c0c0362003400c110341802000b03501d50084c01c2c891031802 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 366680512 1250 366679262 366679283
    0x8060a030317090a06140a05061806040218060408010e0f06091c0e0a030b15040504050a0615150c0606090203090705041d150103111e100c020d0f0302060112 69
    0x100410010b02c08018a40c461a200e40d00b8070501240c030611601d940c0e6080d6108585151070091640401d59078084c1150380512a0009030300c4c0c041c2044201c494016200325005a03840000d80302c0c112080d0700050055038004c0d000a000030f10594154003410401190100360351500620002081c0c9403003040351202543d8204002036806400c0e43c0780c45007444201420302640220030280403c1480c1c09641044a5080c000400d00032142091828a811040101c40620682c5020340c0d0b0303182c4604180f04004d12150b16119400784640c1c4080000001c2c084594032a80004c0c0c80400c02000d07051414000d40c2c040d07290010100d0940c0d15030086a109110319070052000a14040c1840010101000b041c1c1d85032110f08601a103816090080720300382c1040c1c804018255055080410b130800412408a12a80f0203038000303e0b06a1158040ca0304c4404112244041e800e00554103481204003e4002544000303035003451820454100b050a807882d019600321540b5030f80b03c42c0d5519901d04c07440c802400401e01e1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 366681762 1250 366680512 366680537
    0xe0a050106170607350109060b04060504030b04020a0b0706090b070c11130f060603090210180b0310050402030903030405010c11031c0f0203131103010c090302040e0a080a0f08060a0303 81
    0x525100c0c0e440005c203007401503904802c04c0c0c040300300d00c10500300011030307100c01c001040f41d001580104800380c065511128070301441c0000142403440356100051004080138009010340d51840348810081c08013150303699417030340c440c03510304000c0583c3d0304121124084c500115520354841c4601c60301a82c0e0041020f00e500701c0950410100d0001024104002604c0d50f50001400c0b038140100002003104c3d880202c0d00604078030420510910310b02e40c00703041040d085903003148044641113000c110b030011210541e4a072074813030060480c03110135000726401c90300000038010720030740000c021071050740580300810036036406600850b20a10744160078040340d030007842070070f4920200080e032034620441c4c040c1c0054401c984d00480416038104a40301c215181703a10f04035400b03001d040b024003000c450b0102c008000300b20041c00301030100303050f500020f8090340d5200c0c0c01c0240700600300b00c0320380b100341c01c0120141c44141c40800200f500400595010000d403010b004111542084405181034962545481104420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 366683012 1250 366681762 366681767
    0x206011d0a0506030c120f1c141c0603030801062c010513050405090c090c0301050120010f06141e09160c0b040503180904020f060307020304090e0a050106170607 71
    0x101622140e130500910ba010710480e903d0a090100800c1140042d15200d04410445800d009542c16002e00282800c0040c2025940c4081c03208541007003111010f8454203c86200441c1140c4001c030600c031f1030316003840070060507002001281203032001c0e55148600203c0901e02d030034100042c1c82d42054030018070118445036000f10f014100b0003440e84000103a0303d0b0b4940005043e0346041e07902050a4000c05c00200d16820400e414a03403080880c03100d14910b524240009011640000c80409091108001c0201900c0217411074008400910b509001450302e408401401803010050907118115070995220b03090104002400c00b10700c02052840d80f80d440d408050010320002c1d0401081100c5686200c000400c5081d08500490140008603107c1c4a242800410141048059032149114504020040e84d40724010840c04105540c04c81e00c903110400c05034038500583d000300b40200e0505807003000d25000005c1280342180a207000344001944d6400700024000b400c00440643d030402000180c0060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 366684262 1250 366683012 366683021
    0x5131e0f02090414090c06030403170a11031f050f06070602031f06030207060f062d0b0a030b1005030f0c07020d06050a050702120307050423030313060206011d0a 71
    0x15148003000d460105800c002604440850070300000c02001c000911012250400c980003116000341c88652841c00e02d500e002d030000d11910544e2020020f81c20000784503455a0708030711011010600410344030f09000d0220300e0050501c0d4415440401d01c40d41c006024588080d1a86421a001e0110b41c0380060035141e02c000303940f00070b0015400704000c0d0b0b206600c0081d0306c3c1c03000f002840542c0e00161284210f207046800e031004043c003071030b0f02c41c05c02c42c007481440e01900804a0703450030f4242c9203404409545000c1c00d4030315680c0c0710391418a004a0903190b0306405400c000840c2c2800c403080001c0102460060362075010a0b120001030b006404006900c607a0070760000c01c446400209010b15800c10b41d6200c2d82900c0d421150403040c0e684403002c1c41101ca4040207c01d90f0103010014182c21485c00c2400140a070080b071081c0c001c42864008440300500d100540d007400b201001d0b043d2a071320002d10b1260002c0b400709104000c0103110700000000c041060240c104910402d8014000340ca4499041010260 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 366685512 1250 366684262 366684281
    0x301200702060405092a041503020307020a050105092b08060d05070801050a020d050603070503120702040603020a0b030103230706030e150f100b070209041410020304080405131e 78
    0xc02c00c00c07000c56583d0303400b508240f040801d0110351403090419410a254503117082142821003105100c14004480c40000d8015120014500141c0342daa03090012480d16110100181840d481c0c00c0034441030002c041600310010b14403a02c0c41c840080103d4040f100d08000505d46000602c0c5140861414580351500105960003041202d1440e62260f200d60700b104e8041c0c4006915582c0080c1201000d40c1a000b00c0380d0100088024020052624000c2030321038442c0c000e4041483c80004400d0219516a840b10300070715009800c29031095265070b00c00103036071b1080c04145e0fa442c0e240015003140c06080c0345802450501c0c0303005481d000f407a00c0416005071003083e5880c000c602034208281440c070420040144a21222408031801d401c100d000c103030344e07020b598101c030301240010010100507840d9404007a030095030000d00c156a404404170700301d0130034401c0081903c03800d000000b40010f2100d001701070801d49108039003012103000e4804030030b02240c09005c41c10b505242c0103000e00000002030341c00402e14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 366686762 1250 366685512 366685519
    0x1050a0b0c100204080309150306030c01141204051005060316030204050c0c0a05010b09090d0c080c0c0306190c09051008060301020d0c0503010f1a031915080114060301200702 77
    0x241106202c01d01c280c2e00a17401c899400e91000c0b44c000e00d2850840400300c003201401201a00e5070500401198440321002a000d0601103045003011540310074000320780d225603030081542c450341810714120303464500b50341e413040301d207414200490918500070607910360440e00100017004951550303080c080038190042901030f40310414040c122060a09204855040303102c0c40000503c2e6001d0030402c115580040c00300c42d0150702185000307000d02e030455460398450340c020000c60740303564107030000c1490304501d8000c181c4c041c012030302403000304800c010b04900a020070f41e00c240b01c501002101102c1420880c0314103a4810320107442c004079a03024102d8181c20980240000d482d0140030380c24481502c03203201c0031800007040040104156003500300c50304041c00c07000400c0c407a41070003c090082603000152000f09500005810304903035150a03840722046501c20400080b140707a175107012034020517880710405500400d440005213107180c18440c1140c2c01c07412944070419200c030002c003190f40350403a5804982 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 366688012 1250 366686762 366686773
    0x190606120b130908070c06021207170903070b0d0b040507053705070b180309190918031706091501020a02120618011104060c02010302070614060301110301050a0b0c 72
    0x460303403900403806514064103003640e6500c42446d0882040c0120383c0400308540080751099126a0180308035090340340c104610031500c1000760001003c3c0c0c46200100c41d41807158400000d003252245e00900f0305010800c40401c5103040300010f10080d5082112400005035007040075044461920005000080318100030081d440c0344d00d18040300769800301441201091010aa26003040b04502071580d100c0c000811032201101140003407076a03401000222441a1300c0d01040741c040c80386104803030000700240c910511002c1040103e02010402c4030344190000f0b4401618000180340c444405401100050500b4010741c2e50080007000c0c6212219180b4110f01032241d04402503561882180c2103012180d01406c42030070081800702440c1480c1c851052183d0402c1074102c016050720003039904a401500b404440c0c0702951004030002e120b5110000c0c40c0300d242060115282840c00f0500c0d1003000180e00070040a2500d80e10140203000902c0346581c0080b0b00318051101e503103403c0140020402d950100d62 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 366689262 1250 366688012 366688039
    0x2031e1c1a100c050c091801020f0d0c081005040b0a0b07051c0807020607230a080603010606111b04020c06012301030203011d07090f0806190606120b 66
    0x6081c0c642404000000000d810318014151814001542c81c0301642d0602c1c1e580344406030b6903217071070348070045803140329407000c0380000c0c0c0482208111240c1c0b680c0380c40003150346110b0f914400300e2030f8001e500f2201c80a07203460030000e54640a803507458020b54258840c11680c0d2329000030000640200403986130000d100d158005a01c0c4214006868800d21620207031a480030050004529404aa424078040068100070f006c0060b401085c2c194006503180b800010801c40001c1a89031802c0e803010203910001c0010700c1e00c55096126034401c4c000d8500b24020f00180761344e824221004280c0076200300c2141c2000401d4401000409641d9000c030704040d00140c24140c0444525003841400da00c9400c5401c0c01d01c13408a600000c030000002419000d0138114199418a02645a403105820fa804542c8411001180b4814001c2665000824903100e01d03201c150b8603023540d2600c0350826034615911211080344001541241d0042c170040d284941c0e92140003490207000720024244c040c0702c10380c000c15004040e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 366690512 1250 366689262 366689317
    0x1d040608071202030c01080105010c110f2d0307180f0b0604121a0c04090b01090302100e040e0703121409100f020606010816120f0e06061002031e 64
    0x1c0c008100344580481e080c16140181410040415040303410050703480300501c40707603030002d002c0c03482250050780f2010b4001d4100041581d86240120203030380700307000183c00704000145648004d0705600650200c125041700708203040d51151070f40650515921681c226000354030705980010500e0441c540301160002000c408204598803d801011a1018900035202032080440400d04024460103503c0f441c0d1620111800340e60042d03008206c0c0399a241c0f43c50309071036885910114051a00200781110814804801500402c0c211074014022814890080b00311000451101308882d0000721040c03a0030703450002111400031011600070b00c26000d0040c0c0c0d080382c48045080611001d03a0310f40d070031651120701001e407030148001e001c0b40c104081c03241081103046015809041501d05420010000341c814241c810107040c030a85040c2409240c03011800700c01a0000d1100e004150558101406084120003240c0701d10443c03200c032148800001644030b404842c28010012407500042154604d5002c5101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 366691762 1250 366690512 366690523
    0x16051204030e0102070b0325170f060f0f1f0507050f031c09050a150207081204030912080405011d10030903030515010912110916021203071d040608 65
    0x607400540ca42041c100d06580402031180506a841c0040b4203501d0b0000783c402030303a80000103000c0f0341198546140c080c035000c0d4014882070800100f00d0b00c11450607140610303507031800700c45142c4210802400c03d000340c00c005540b00080c00f00a000c0106401c01100c007045421082d04c04c210402208206134004644140903681145500030040d55484d5104e0014008a401c050907000c2054540504140060400203000d07074019403003100103841c4c48080c0300b948000d002d1428007909222001859800e140c6004068a104511940320703002c1c800e48840080005041c1200c001f440b00a04000c2400158003079652000d66100c5005103200c130a0000f00400e125134200c0300c1c01c90101e61150801320805401d805801d910100241005000f00b620000082c01c0040e1440303211501c2c660503021405005100c0000e01035207a01400c1d44d02c0784d00346200182e1050040b4a07040f00180105a070300e4503c090280e040300d000301110380c0c130f00400c610504120040100212800740c0d12565410340041d00f200c06014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 366693012 1250 366691762 366691771
    0xc0402130b03010b070c0f15080703021303061e0b181005040e060f070e011202070c12080c100c080f060406090c02010e010e0f060f1503060408030603010c0804020108160512 76
    0x107910303105e090914014120308025080752000d20b0301e903c01030120200001414505103543e14003c20700340c43e442002e4009100342c000c6440c0b84107400c1008001c4c0310f40c540001012001c10240401601c1d00e0b03036503803000c44040582e1594041103042c00b05008003404145503801481800080140a81d280000303030881d8407200d820101d54203c9000c01444150200d680743c1c1c84011802d021920148603400280b00c0b040b400303004060703283d0114038071003404a900d9070080600009001210f0114460400311f10303a810021000b0718908c151a010309443d0040e00a07070007010302c5c603214082c8a86406110750080507001b03001641080e6107040000b04c02203280101d1400000a03000020175810014000e03003514480101c0c0d032a264081c1000504d6240c00003942940a1310500b400b101d25110154030f00741d054002c3d4030103641071013003a0601c000d0081e004000e60103104100c000304002c40301d0490a072a000b40c1210080d0125241c0c0000821440520181c01351212151030024038014100c1200c1030901803c0d03c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 366694262 1250 366693012 366693029
    0x27020c03030a1b02150c0a0203070c0909020307060903020a0b03040602090307060905010f080103120c03020a0f0318090c080c090d0609050307020907020708030a14070f14010f020c0c0402130b0301 86
    0x25900520b00070030901000301c0e030981c0e00c003811405145da40d13078141c40781c0090036006134808002500415140300307005480c00030b031b400700890104558a030601c401070805203105a10030301442d00c0014a0902540c0803004480d070180450314050314100360900c42d608020816150070380c08206011541c2c0c1d00344100c801610075515840c8126040a00050940c0b010300404414426501c0040c408610f0580680d03150311824541511407a011303240480c18040300c024002c0401e85040200c0d0101a08400c4201c605441e1040c401c041ca40d807124100309840c00800c12001040d110000f05000b110603070014001917101604040d072000c0c0581d550000c0783c940110603961508041442c1086281186009070010700c0e034801480000d080c4070700380e030b00c0b0310540c1d00613018091450b154203064101101921003440d0000e9200385014a41c0c103117036a0035409050307070103810351070140700e405000b6140c400e440d28507a641c00200882601c3c8804e010080d440034851541c00300b0320000004030401e400c00294060150708 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 366695512 1250 366694262 366694271
    0xe0d0c0602190201051909081b01030f0902130f0b2d040209010f1101060e0903030405070807060c03030519020a0c03020d21230903040503061027020c03030a 69
    0x4640241046040540442c0c2a00081a0740025030382c02002c1c0c4e001d00035148012035002041d12010394842d01d0b161b2000040e4000c0c41e40080410b4151083c48403501d000717803424801c2e401d007100303e0812184201002036001100c43c0c614516148998800304481d0380b01c000028a4850743d000140444401072002172501c610300c0b114256549101c141c0411410081e01c2c154144480c941c00608190440c44a000c104051040804540754094024400400310510015031030b0030108416038032640200c82c10385140c8905040043d00c0c14001030b0050403900103560b400c0180d20b9981e42140a04005040c4490030f60000703a01c030030700e21003920081107240803e442c0c0e00d1400c03541d40350107410001140700b61414010300c0d030401c0e01900c403001d001140300804090700003a10301440500e41c0740900117180355000d0244500801c010648008002c009640781101155801d6849009a030203a00700d80c000d50f55040c4001119141180030b8910209035695072250140c10b00746116561803954004403401c4a02030f844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 366696762 1250 366695512 366695519
    0x70807021609060612140c07170a08040b0711030d0b04200715060803091c0f0305090a1e050607020102030c03030f06040509060708070815060f070519031e0e0d0c 71
    0x20044003244242e045c1002d000c010b48941d540c0043e40001030099549210014068040040303d101d04a1a01a1568566100c1c046000c4c02480c0f40004c8400311003041c03101c408620340a028290b41c4620403200c40096280c5040713126050080c0100c00c130707100e8120703850320700950901c845415204064103100001c551280d85505240710314131090180d60209519282060101c4a40481120701c1e01c502900c10302d80c40c8003044000c051000ca01540648400100b0b0040c6042640c4003008002ea8813003107801840450b203c45414004040b03114407203210340082d100410003030420707030040d003012401401602e00305001f1520460841e4021507000e014407100d001044140d1919129980d08a40300030010320071032030071078006001107a01510607000e1115010000b007080c00101d5030515100c0000e008079480c0c49805200c0e60140c3c110803011100e0340a900207041c0059942011100324030f41503901c3d00c0c485082020800401d04002032030741c00b044010348494425823100c0d01c414802c2c501c20300200b04010318 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 366698012 1250 366696762 366696767
    0x314120708180a0b07061802030313030b09010b031e0a0c06030506011b0807140316050f0c030c1f050d06060e03011b050702060903030403050f16050105040e0708070216090606 77
    0x2c802c1e105441001001000c0c00311100081c20b442030790703a00050000d150452580e120900303e04500009501d44400149801107645130480c0c3d40031244543c05011081e00c40404030b50980b0050408246c169100c110549520585000d00840103a808015541c00c04169280c00034410b165400050200740c46030280815540d0040d1104603910000701001c4500c452a43c03000c806100c1c00c1c50113440f200c40c1c201d8014803044180b045800d807503040f00c21219000308902e04a9201d058904000c00c20340241d003580141400c000c00c094403059401000814104142d10440b01c1d48181080c02d581001800c0c02503030b104d042107105030009800d8903100c40d0101c190420030142500c100003440500c0b42a0352402a0015400500351182aa4120388a0380c40300000004245540250b6202814130304c20001703415207680c40802c0b4050880c200e2580d50070015112001500c1c2e901c980d205003000e000030f10000070f040d0b901c9459080d80000041c41600c5403583d5494460b202c108144d0440d9411554443c010030120b81c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 366699262 1250 366698012 366698047
    0x41e03080415090b0c18191a07030206060607080706110909090c09131103121306020a0b0705070f320619090302031e0a0e04020909010314120708 64
    0x89200052010303a1a554442c0d18020014025090b01440800c0c40761b0364050f00101d031000c445025101c61008a800c002d80c0c203012085120700d0b8001484a43d00c3d51000421004540ca000e4040d0014030180d151882440136582c46040283c420b92410b00405000400d5400365040d0141d005005035141c0c00c2902c1007001906026080902e03d034415562080b00f41c6a8440190340065800c06004010103039080207045032140c0f540c0302ea4107000d103481800700c0d070024030302405086a0111900750b00c19140c034402e994411301224090910750b607030400036a0491080c002004070a00c502c4680c1030b0b0340d0031070b0b4900c040c010407410303818072800546042000c0b041c072211282402201c5d260080451b420644511407403610154000b4000c01c4e290b01624091500030011070701c1c995100454645c200003102605401600003012900000c1e0400145e0025458a4003d898914900421384d0364181d2869403075000e900410300e000405800b5145400c26136211072005003050341d000320031060380c078101a0340e1400c559 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 366700512 1250 366699262 366699293
    0x402011202030405070509060102070f0b0a140a08040204021305060d0f0e0c090105150c0a030c030e101709070b1804060b130603020a03060506040306020c060c0c0a0803041e030804 79
    0x228070610810001c241c000510004594050740c4980f22510b071000101c0c10207890750440c072100c00b031804001440c403032918014101c507203190f80c2d08090441c0e1203000d4800b92240070341c0000006d4401c3c02250152074142c1c02030800070a0124041280d5580e40041000754001d00400700b9099032b948030310300038140107004961711205600080c080654002c00050421001809198040d00c03071442094078101c0540d0448100302405c00443e40840907900d4028600042010101e0020701460348030306007400c0249240d2011055501d41100405c00148003003807003c0000c04002d494440c0700000191480c0000040c1100b6248140c20700032086c02c0f50604c815038069a0200c00e0301e1000b0825145202410f01c0d034101900d42e80c7c9000740e55031100c0c100072400791499030405548024006000010000c4c1640148640030b542c40c16521980e0320303040e56210310301541030400d0454100f80710700030014408100440d44540310390b442003031055075440c0416410f4140c880403004a800c94040c0b2040c03216400b00e403640e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 366701762 1250 366700512 366700547
    0x90b06040506030d0315090e1e060f0c07030306030803100302041803020c09130206040f150305101403070b0d06061e022d0a050d14340609030206040201 67
    0x3203062800102e603031040404407050415075914806c5c1c0ca8200b2001043e80100200e0b0402d00102e01804c151984684582081030050f0f0b0004625001074100482d405214818119068140c0d90302d07034480b0030a9500c0040e0880416945080100c00210b1480203140100203003028008542e0035841803100b190f00c0c158203568405602e0440030002680004c3d418000c0c042902c6140700c540b511000704200130b9058034001d50188002c2400700321040320b000001e0489607007622641100031505029801c0319000d9401c030308000036207201031040c0709044a1810159102070119619a640e48005c030020303401468502980e1038461104204044c0e20a1008008800c000c040303884540c5008006942c3d45040c010480d04507140000d8915a00e209040c03803245c101c080c5040c0c03801418a860415210710702840d800e000303d2020185800c44003000c0080e02d90b40301c3d070351071001d200710b410146c248640c01c041e040c140901103070f940c06c0c0c0d4001031107809962034842c440e8000f066203003020f20015194080200d200d042c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 366703012 1250 366701762 366701771
    0x507080306210607120506010e0109031712150307062a060e0109050c04050c0a170c16050304030209070305042312040e01030c0902030f0f06060715090b0604 69
    0x8a8610811650081c0080b101400d0019036030441e985281900c2c803003681d007405800104201150848502e105810350700c50104115640d140055800d5020418200e0016455603010f00c006103005688840e0715403880340306400d05c1e1103071122001e4040100c4010044c00340b8408580602d0400304030000160801e81409920a0081d003542c51035040c44084024006103812851420300425a214050100b805c0340248526001d40c10000e60b40c001403422240124034003400280c1003c01d480a859100031240e580c2109265168405494060302815049000104119070807900ca03080000059441c460400746071510b1850042085401005103e0000d00d4180300801001a603081da072010403861038410305800501c8003d03260b1801181c5030107046ca03003000040104060322810071140c103d900c280007030102c06465848070340590000f5660303107101c5034504001c541c14004003038045511040240c0384c2410902641c90380214500b540d21100203403139945046100340155a00d429511200c281d60521 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 366704262 1250 366703012 366703027
    0xe0709050a0b010813030e040f05191a01110f0d0f0201050f0606040b0c070e0c04081902060912190803011412030405010f03020906030103030327030f080702010906050901020a0f05 79
    0x7000b04c2001022074828041e400c07245e070704150260098910111024000f00f080c405130001200c0181000c0c2d6044050022142c02050801018003401d42500c945080c0b1070b61145003030380150b541e400c00c903180d0300080c01400300c1c030020104c0070800402c03071140c50303036a50030340c0054401c0103421a00080d2624406900080070846241c0f200d0003141c04a61070500210307a2442c191085070b05080f1030f504980b062010742420b01c07015100081c0a08180d410001c00e8035005110b0180d019183c0303200c2d94000750088404e10029140d4a002d01208600d19440400e44940251181141d9108600031104503000c50011005100029040c80c044603464015110220b42300b42c1952199507a003d140700392410040c0414100284a1080c3c0580b0b440d03020103000980c403542c40349406009081a80285001500b640500c0303131a0342d41c0d10320341d04041c035007546a42c1c9a150306144201c0c0d005a00a11313040a641d03c9170880030005000e80305880c401c051400005840c0e1140280041c038600c03400105008201c018000c40c2e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 366705512 1250 366704262 366704267
    0x4210207060807110a03032003042003071502211204060c050c070f03030e15030f0402010e030607080106121a040506010e09040303050402270f06030f010e0709050a0b01 74
    0x609407800c03030a124a4542c0e0742c1e107084403400030b01c07045107603980140c40d03c2d0310400d40c0681041c500b01c003081003000c04003180c151542c0e400740400c407405400e07da680c2c034940304c40300c02601604224000c06000da413840b98445040900e07800c40801c03031400503071040070f0b00415285c0c11007075680706503250705480c3d2500320045640100d07920064806020980d0381c2c0c20a0601034002d00032036401d508290162680309070390f4145c10b00046003510040d030208181c40d11030303a1a8545084008490b08200b03055500395191506800c080d914010302c102d040c0101064140c51540c1c04000b00c3e80700781565910081f2560405030002d269044c010440503141b4108030b00e48001ca039124035000100e18094400203626642c40c0012280e200e00d408103240c109001105000034543c0c03541140d8841c5000f03a40800c000181d0b0390321075800c00c903041403050001c294100461414200c5440172034100c0c2c0c004085030485d100a02c105030850394089aa0001988560001c0001000c3ca0046680c0040b081004018100900001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 366706762 1250 366705512 366705523
    0x20306150f090c0703030b031e150106080c220515090f041e1e110a03060609030206040506031509010f0e06040506030a0f0813121a01030201020d03090f061103042102 73
    0x901b45038881100d60003c0e20304200700f90150f5030692084851030752a03100103403079468001400c80c00610000021840394003a0a40340d00544d1104011850300d0700d4204400c0004a80b014041c0740545549000201ca54a603402d682404030010030351070740c5003c12002c001740031444903006801103042844107c0c0140c080311443d40076118428003c41c01ca07403036034102100c07007400481500f9810320f0910f08022400c65000640003203900c585041010685030700d803d0300c80d00c1144c0301c000d620180c2000300340108d081c007001a54001c007c0001d05561039400c80f000600c030300c074240c024824242b080c2030108201802040b09541000c0d069800b04114200900230985401c50311070040d214403048500b1504000140c000c4900345030389001d03e40c44482e221001d030601c08003041e000b500c030855600311a10280700c010701802d0407603170305800811401d035001b1000d4000e04000c0c84181c40c0441000987c01c00b040d120300030500074402d40f101a075a00d140500d03001d00d0b090744d0600d601b01e081c02202c0000c0b401a40004a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 366708012 1250 366706762 366706777
    0x108070801052103030a02091905102a03082a03060d080d0c02150702011506030f02090604030f020a0b040e01030215041d01060f020c0a05040b010201020403020306150f090c 76
    0x804200e4411402a2200d41503950141c03c0c4035440000100301c20031010780d0207800180012280265141c16400014038007036410b0003000e0307000c00f40001c0754040310b0096040d40300d0703e0300380020081c06030b0144121180100d02d11909030081020340c4100000002c0240d64502003004500001103c0b0558482184241c00020310b061b0055105050350303010300540340140c0c0c002421080301489802c081000094480412140b09001c00170360f00007054a40d40103000d0b045000d44194410344c0c48a00e03010f8100c026081c40101050081d90070400c1e1042611941c0040003c1c50040112266010980c8103114081c4121750051804440600041c400120307000c1c9224116a01101c61420300703040541546042e10540d0700c03004109000380c16424495222480c014100c804917114070185980c100d00a0f030300d68404d01c1d0401d0744040d0044040c44180b84c0b0390300081c401c25041c03000600341602c030b5000c40c0c503007102900c1407200400040c004200500e03107003500c03074030700c0c1000d542c4007849040010041c03000d1b00810b070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 366709262 1250 366708012 366708019
    0xd2109030f1704210506060f0102060a1e09061b05070b0a05040219080a1209210f0816060f0908040501050304020d120c02030606040b0d0813081f0b010807080105 71
    0x11520180c2801019107000c1d04c01404c1360080e203100140c8061001d805803404444034040c13030303001444a10780302d00714010304d03c81070700948800c1d5149a4104000d15401441c41016aa26403240300c11505610422030b211380314681c001001442451100e02a00c3c81e1507003101040001c0090300005901181450f80000340407401240940f0b07984005241142d041d0841054468080d5001645510008010803060301403881a107150455000864000c0c0ea14010600a42100b001101c1c0c070500019403c844540501c1c980c0c002920141d8501d81940c1c4100e11110807544103241c02424040399100c0c1030b0800003100c0f0b0400c40c0b141c880c5c2d2501c0c1c2030300851085a0510070003200090942d107500c030b407200c443c0e03600020000075510441d0000d480d002c058101a806032003924005046800c09104102c4003440007405007904042c41c0e07503a03041c00c0d030041126010004c501000080e0144040104c55021000010f8400400c070142e00007400715906004014100f15029050014150b0801e042e24150f40066 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 366710512 1250 366709262 366709283
    0x909060904020d1b03020d1505060a05060901120e010507030506010f020703050c06180a0305061503340e0108031b0c1f02070509010f1a030103051203150d2109030f 72
    0x3031544d60300e0768502e54000b079044220494140308000c0040700380c44140a51140400070744e1154000d2044000090055035000a010000c061042d0b01426011407131001303d540210300711301085460f40c00d4480956900c40802e85401c1800b085603080f00070308031000d140b03200a10f4503a06d10b88070b140d503ca8040145c41c0c0903038070008081b000c0c402850040401504042c180c2e00c030181d647d01d0001c0d980c40c01240c54003c440e01404207001c047c50007044441940400c40344141c1103e07a60020213046281c1030200d0b205601e54000b0004e103501c00300c5100d500915020300615210801520702d100410000e0038200483d412150072a03001d980c40f000180c11400a1b000352251004446406902e800c03100d41186502580c0e5100004105c17060400346004c2e00c42d80c0704607811080100c80410000d000031301004015801040b10714454681781c102441e8040c24140d4032042004612001c504401d40c0400e06441404070303016401c0c50341050060900358100285001c0c0080d03071443c3c03a60b01010307110003801086800b00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 366711762 1250 366710512 366710543
    0x209060d082b050709060201060506270105190801030204050c190e040f06090603050f01091505150901030602070219080312040812070c0c0501170a0b0d170909060904020d 75
    0xc50480c08141c000c0103000f040a070a10714406130099035140b043d1001503082c41d001181ca070424101b9074481001c00e84444c0c000c184040c141d0501d0115541034181048414410070614100301a1440381e49680c5480302030351941940184415039900810f008041e4504100036081001408030200255810340b40508452082c01b002a010b8140d4082d402122030a1001c0411044219402002160702c41e000b15032071040400046420ba841c40c800c06000c1c205924801481202d00d40c200c6c0e507000401651400d0101d800800043c0440380a0300165a841e0f40858000210f0030003010445690210800d9403128600e0207000702d64074030038003c0700044481158040341c20401d191013640c03001e00180c04094602d10345100014440069444c09441803002d60070700103a154007951080301050200c444800031a52183c4d4407030301901c4102c1c07c2c20f0700030b440d44000340081003140380203000000604c4120365642800c2003c000c030b10400544803600c625080424040160782c2d4900304d6900562241149100c01d07031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 366713012 1250 366711762 366711817
    0x203070c051606110d020309060a02010e0106090203180c0a090c0201140903120a1109010507080c06010f090c02010e1005040519050d030c020a02010c0215040506160209060d08 77
    0x10410402091449940b54000060490360446016102d0564850420b160f0714a40580d0f184201c081180158104100980c882c2c03d00c80b00814401d0303118000800c960540441c09800c403104c0d0ba00c00e8846607800700910150500c08001518901c401030000c1c140030742c0140008181c800688600c0d80c0e100c3d07680c0b20900c41c640c002e400c81c01c1c060101c5a100c0c0d502d86003c0419507200d0707014905241584071010001820038050b84030f03081004580408050170904110019200c41d07004441c2911142403c0c4603040f003103902049081c1c043d001250035120741500d0072102c203080e0f80a00142c0025a418000b650310144030010380d0b1090b44610103808511625642401c42c01c0c4028803c8036a01406214405020700c9000198a18803000583d41000421041c1d40d04076120905420028000f94200c0754a0015242078030b070452114000e12801840d25985600240c6903a001603803c003030306d01c0150083c3c0154a0110003055210f14142c4500b15420300d2030362600b401d4403944a11814160780e4856a050409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 366714262 1250 366713012 366713027
    0x10609180308010620070e041b0303090e180f0705130608030d1107080c0c0307060e0619021006060c120804030903080313080f0306190812030c0903070e0a0f0203061003020307 77
    0x780c2c18058881b41e41e1145200caa2900c003c0b01d051300e00c900c115103003944404070b61598408a82d095681c040d01541002100203101c580900424424400451400d0181409000c4030034040c0e081002030121038940000e00104190191038a6081840c02c04104134500c0044100e0740c0d20100e4040010f00f141c010700040605005042c0094a000c1c40440c0c56010b0450004a24203802d100303c04681d4a60b646100c1150020100e55001303801c4441401900007916001c0d40c0016030404a005948075002c9a40000301150001d901200014111000000501011004900840304a450007001604e0a0346010b17201c9001444003c055410000001e0400c042200c000004158401c05050f903c000c20440e009040d08140c07403c5108403e020302e03a14007501801190b5007110510300c090b140d40b04070080c5854550700020490313881c9a0381000700520300da03024403210019000340080180241006004481110420b10340308000074410000e100150795801e14895402a10b4500507940e6512040201c8098 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 366715512 1250 366714262 366714317
    0x50718060f02123c091311070803040b0c0712210c09091104050307030221010218270c071e1208070807200a06050424090807020f061b0106091803080106 67
    0x47c501003414003c01c04104011400395015100c5c50f44a41c80341880221a0b00c1840b000800b1000c460000c00e0b1341c40c3c010049180d910310700346200c0003110403c507030404c05e46a4044541000400520007403081858610802e4101d031200c5a0701c6040c00e041c500441c0c2c1c3c4d20f94901019110313450b452381010b0b14100000b1031f04c82228440c802036407161028840f01e4180c0c4031801e03001c0d104d070a0140030380c41c543c8146105d1100c032050702c40d001001901e03808140c00d0140d004490a486944d10030074a210310804c0c0940d050107440c0308010b0100c55446247c0003c0000c94054440803c000c100000d0004803035216602044407081140c600c8103150f02c41500a05c3c1c26140c0c000200f00d1810041000103103c03c40d02c0c0c8100002048000c01c4000103280c4544080740e000a00003404c4030000d000080c0541490143c00c40c040b200a8203240c034025528000300300079400892009507aa440d82003d00c64103540c0e00a20304c0c103e644401d41e015203c4284d50240c00548140100c108000c000781604280d20100c41048010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 366716762 1250 366715512 366715541
    0x50f040b0f07061d0d12090203011b0f0819390905030c0a140402090d050106060e01090815071b03050403020301050718060f02123c0913 60
    0x22040c1000c100412030704034035800d40d075030f900d05130608041422028040e10441100c4014201c4d940e0040e01c255001c01710208011041303541d64802d000181c40c00d10a1044101c400e81c0c400018464404004008440c065040d50811200006124086403c2c0b91412000881c050b000703d4440b880040100082c081900e680c5041e00741312082449690ba0054402d5810b0440d0380c81101c3c150720f40f004c3c10756411010a0300c03608030a0850013041b1b41c800701c200080550500800141c54100740344001460450f039442c040d01c403a591002e081100031b400c105139080d1031100703003030406401c0d2404c500662204041d0000c142001107041c002034070300740f292811040708042c021010300c0750718172404c000b04180c0160101324080c0d03180c500450461402252048941100b6180c1921442d04043c3e00b1642c0c0101d0700c06200c154070030740c0d1440c443e03a03450401900e40d1004090f2081040c100305c072043c9125814010281c807143c0701c85102c04503243c10000032295a510255400e0001a0399400c40d1802000c41308410940d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 366718012 1250 366716762 366716767
    0x130216020a0e0702120903030d02090301060806010e010e010e0c0a08060a170f070e090a0807050304090f050a0c08040825050102030411190b070f020d0b010902030a0c0206060a0501050f040b 83
    0x42e070420b00900c0d81e010352200c0e400c48044024001100c06148900398415038941d1003446144111038550b00200400000035001003a15035450900a182c14802e0700043c0601200c00b0050040750b0300000c080d0300501c810641034080341040e01a01c0200c1c41000c0c209410800e412001440303544a41c007a2600070604010500991000d9103030720354503040c0b144195007080c065a00001104800502007038010840c0304041d040d500056030b240c02d220b60186400329200c0c00103100c0082e02886c240b00300b43d0410110f1002080c01c0c40c0c6840501c0449624014038828820360034107000218140c50165a005410100030303843c56010940810207190503107500602c0f941c0000208030410821a2042110000a9814029290400000d4005d48a01c4c0c0604002020240b044001007181c8940c0c0c50440da0000d0200888004a922200740783c0c3c000340c100e9118150000144001d5000d40c0c410848024214400f828103410083e0008000320000d00c241c0d410042c000c9558180c016413881203034014506c041c0403d6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 366719262 1250 366718012 366718019
    0xc0906091f02070e10151101060f050901080a031e02030417011505100815040b0d060b0906062b0209060409150605030903030a091407030c0e060f130216020a 69
    0x1c1592400c00200040c0102d070000529882c0410110303018507410b8400303819550928141418200b4a031034004101f0031464000b0440c2a020321810019083c991018908181050b013070112512060303200c0033059110104840202ea4012111001080e01c0c3d860000780300ca52040480c40c42c02a03400211454555480005502205621615415000420300860995144200300500303100011500100e642100043c41041e40c45001010004009000040308442c1d60041440c070740014108444440da1800e142c42d0314508045220f9124a0460707005150500f602e032004d4031380c0203003032080102c0c0d0100244400d00100716010791348a80703005080300e40c64980c0e9024280180600c0200c19540518107080818a14840c40483c0d02c00c1804000651454903001c059000030720803000181d07003440e441d03032004400720303014000d04000314052146d0080c06801d14000c8252030b000034140910440c618119200261207400d00306011016203840141c4a0a07103803d0003041034481600290b11401c0c428010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 366720512 1250 366719262 366719299
    0x6121508011409011d10020a0c080c03070b0105090c1c0f02190f0e01080105190e010b1c141308070602030f0901051503060105121216030f080c030c090609 68
    0x60f2240c00310500901907030380ca03020a000c00310000c1c03d521010350880c49411044861a030001d140450151511401059440c0c44082e640d8102040c0c00c441504002107000c01d02c46501c401d1809082c1c1200c540d0080d0402584c0e48003544500001d404440346070002d52100028682c1c00034100c00e82010083d5580c034440600402020a900011804544580300011405100b441d4080501106854400d4242d003000704001c2840590701c000020199800800b02d0146080300317420340200180060291100034115040701985001e100b040c100c0c03460b004180c42035461000341036400441440348504810700c18101216140302d81003010b4900c0b800001844200b95a06001078400c14030403008124a440e20010100c2c0c3c4c0c01e080151030b0781a484000140401d16103001c40440000b0403008490070001d040c55141480d400800541418842030821202850340201d80e00040e0b20452a08044070700c0c1817150114a03000203420101d6141d000f20301001243c4948040b80e50606005088000d150252800c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 366721762 1250 366720512 366720551
    0xc050705041515030606050906030405030904090501020c0717061609090c090509130c030602160c030c1412030d1d0307062004050303030121140606030d090612150801 73
    0x38603030f1520b018045008400d103e4420402034603915a2000d1401d480c00d0300700200c80c2c00142007590607000c00c011040c8265180d00c12003200b40c3c451030026881d2040140c00d58200381c05580092400b02c41031010751490000440c0c02c40e0300501c5404070345948120b2010848108810360048a06189420003540b881504a003c000071500c041310603c040d50b0700c5140000d1007815000005200718200700051000a111f0380142440c882a014429002013030341e2604241c0b0381ca0307644241c403d40c595102c18005241e0050f600c00c0c10200c1526072403038003d00801c03095900d01c1544080110700350781d4484202e0346550700c2da800c441c0c2c400715801c07240c90b01c1c09070800c800184400000002c18640c80b403a40c01800240001350750444000601540c1141c0c80d201c8510484240d030b08610300c0600c070903c03c500015420890283c1c100c815180101401e00c0c2040a052414060307511920602c14030130000c010710795000c4000c4060306c4100d40301003002c004689000b88a410643c0024a0a50074114140313180030b8903104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 366723012 1250 366721762 366721769
    0xe28020316080606041b0c0206162301020a08040f020a12060518010606050904021b010e03071407050906120f191b1401050c031c0209120f0309010c0507050415 70
    0x43d0b41468a07030300204401c842240303100039420700c804030782c0e206d1842c0203114000302c031800a425117281610241049400d111110300c100c0c0c4c0003204441d403a036a0440d0718a40340e0258a100c00031481d100180742c0c050302c40b0b00020b0008224000d0001e44404545860075140000c0280320541c00049030340d0300e885000381004407000688203083c1d00c402541090140504401c44800351203840c81c04104101303000c080d505c54a10038000540402c42c458529009100b000c0742c080d9540c2c003031526801c091a000707900c500010003c41c0f0f282c0c41203d0502c00355840e03004175030f00500219200100c0ca02c00b846064241300c654105031440740600c1041084da15001c480000b01244600d494200c0318000e10004101d40e585402071441042c49440501c24070b5015900418100318144102e90902442e03001409078154603040040c40a034000c9032984880c180208030268003000c24003c0e01940043c0c00c1c1181c4d07240181c003052810004000103d00901505000c511701421024101b400710f0010508214183e071940e10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 366724262 1250 366723012 366723029
    0x230403020105060108040327030c0305010e0d080114010c03020f1b014107050105090106090b0405070e190503010e2d03090f0f0d0303090c090e28020316 67
    0xa0002c0d0f169031198400e24071440d41901e60381c81070218841001d0440107003c0d101040d01404102c0840403a40000c190300c000c600ca03500105140401000c0703241440012254001804180c6005008a20114580304041034080c41d0040036140d003070400b245402000182480680140e0702d4a21507030701d0f900226019a6000c4e200c044c140e050320107400d0380c1c038400c2c0200701c081d00060706010740001c41241c0000b824403401888160512039030b900e407582107410035210201c090399030f91010000707060103018a031149442264200310514080c040038092402c1c101035144586852407140d91824106100d20011b8400a0b00130410b05c41000602c83e0f03a04000886160309d41744400c0c20114044840c4018002c0c0c0e640c030380140d070504000c04140803540c0344951103964000c40003100d01e841034071441485003080b8040d13030f0042050b8045040c44c3c50607a00c25042668a1820500380ca181c0c11000281441e81000300f01790040312001074005032402c581841c100a5040c00b8640c829081c09184940080c04d031554007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 366725512 1250 366724262 366724271
    0xb12010f1509050907020304080d020708061503152508060f040c02300d0923150a020f0f13060813020103050406060b030c0a0306140d080304062304030201 68
    0x800c031040019070704803050000550035810901c43e5042845a841e005603c50044904168450f0f140318101118807000100503409038900300040501009030640100e0844010049201808082034680c0c2030701d11084820754044e4082004d14241c01d4444160a29641c02c2525296510780020004d034001e6880c07511414110200824a00c1c0c64410354184001a800030050b00340000e03402c8814200e02103400300308160174140048010f802c7c0c1e00600e40440070301400a071480702880c24404508a80314109200102244060204036001401401041c0030310715460480c0c3d41c08203a80003912462a500c4400800804c22902c14085079000e40075000244451b90001c6440708000c5401c000b04a40d080700548a0011500140d4000d40c04290407500079a4042842c5441d01d00303214a1744c5c01541e40310420800000d9110700144d06101f0388010b418042d0150b55130303040c46000114840c0e03001e00301505106000012800700811503002001011404400800b031000d4080d0194100d48121016800355090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 366726618 1106 366725512 366725519
    0x5011b020306040309030218010b0d0b040b0d06141305070306050613061e090b0f0111030415051908040b0406021e1207030b0d030e090c040b12010f 65
    0x2e170700d0380e1180303a16520601440c400d080ca00303640c4070140d0800500c110052441100c101040f8041c0c0414402c01c5900010b0041400d00402c0354014494800c6004129041d0401d110b40ca40350b5a0503541541d0b4200040408446100c000b40560024003061000401a07880b064000801820501002d011070f002102200c5d03144d007264803441007154182e42c6849031229103602070003842d84107000120640e03020401c285422031140e8184a52408420704240d4208141c07002004070740b0ba00e007081c4843c00806070840c0e0042c070800808408241c0c6503100103000c0d0003081d000e42c0e4032505003140ca80d81e40d1102402904003140145001603e441920840be44a00c0600907404203180c60302030398200090050201c03840034502500500c00340170400080380e00020440581c40003134031002c0e5140e031074044801caa88590f4200c0540703060041001c0c4140c400210300f060580b0008030318844c0c000d88 = true := by decide +kernel

theorem cover : BRFrame.Cov 366546762 366726618 := by
  have h0 := BRFrame.cov_init 366546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 366546762 ≤ n) (h2 : n < 366726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
