-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2595
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:10:43.937348+00:00
-- url     : https://prove2.me/submissions/f6187b18-17a9-4c26-a69a-ea6abd85e26c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 466546762 ≤ n < 466726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 466548012 1250 466546762 466546771
    0xa2109060b18040228030503040e01080c1f080709080d121503050a1104060b0316090e011d040813080c121606050a030209061b0c01050301051302130806 67
    0x81091541c0030304021000b89405901903060258804010041e0341d0000c014003091013440e20071303624041c801d0303a9072404100794100426511000071301213506120400d9560480340c10070122500204200140000c0f5034904941800c0d0003401d03c0030803511409a000303660300401d13901c0c01000311990b59000600d4070360310580d00c4002c00c4070900c5507440b614607030050400c0e40c0400344100f040285181da40075131310584104090201881d41c0c20b0b251880e40c454003c40000c0024104494880c2003004c0700e03401c1010804e2598000c20003a04e00003800001c0450564100d4500400c1e01120342c00d40340d064012881300420450b00d962041000040c88003042c5c500c00094141800101040705152050111400003040307203d030203600225162960030b50300083d6000707030303070552400340e4803811283c9065010780100c01c40541d003c940420a03200389054500606011910714084030381290080c001947c0c94402805201c3e00000e0403013040d01d48402c107400501040c01ca5010a11041da41e4811140c1840000d84 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 466549262 1250 466548012 466548023
    0x12070305120105011d060d0e06070816080c0316090812130f08060711010e0604030c030201140f0c09010905030a081902060606030a0509160609061101110a2109 70
    0x1080d05420380d80d44030480c00f502e420301300b04c2e01401c1c03204405208801d64001452040d8000901c5009044441c0c1203074000d0400d0800702c9040c2d080480f13010b09098411900d550100018440070071140d0303c18541d03540100741890609156450300e000e20391100c3e850044400030301c24440380029645c54100142c0340d071600101506a22180010b640400d4400700e035000d841380c055000c0c401d0040e44c0d00071501582010700ea0802800503841c07410303418050604d00b00e4009641c0500000c01081c15007200e800d42007107200354020080d5900004580b03017220400d80b042c0182c014034030000761200d1500030083c0300c2c1d601e0504010110780e6540e400240703451410042160301100202e8122000b031400541001e00800c43d0004d02101c0c90100d001c2100350200401100785079840d40c0c081000c1c0d20f41400311034030010400c052544110b071241c00217440da03041e40c0710b6000007403400581e00c50402018881c175a9002c02034400356150100078130f01125280c1005039815643c58410b1100d40c810800ca104081e44503200c1e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 466550512 1250 466549262 466549267
    0x210906070308060111101a040b060909040c12030e041119080604021e041d070c0609060605120c090a060303270e04030e010210020313260a02060411030c030d050a0212070305 76
    0x80300e0b5182c90441c0d400340b85000b9810300280c41180e640e83d40c00e640a44400b034581035080d80c0d442c03c1500c1c0ec05101d5000824148001c0078410078181c3c01209074880e0081a2800d03c081450944074502910070001c460140034079010303d09650703d01c0740c02035582203030b0024800b504103900701c3c030b032600420103802c0800d42900002408100210341d0840d6140700d644034146000d0540b500c00d202038800c80c40710b00001d0030103030360340c101800304200c13035104901030b103400303080800c101030b02c8005c0640d07850014000c07d00c2001a00700199a11a480c0110400d032a89035407440c0181211050003d5585103007004100c80c0c0521020100c1c021065500040c40750340240d60341c145003182280061300b0010548401c0c40618010010401e004846290b102d040d03d600c440440405040000001c0b51070440d0485000314090000e01030a0250b40022400c0c0168012410018040e800d00308050769800d500b540150036410000f00c0340300c0d00c0c0c00391000c2c191540150066503031030510000380403001e9000000490104501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 466551762 1250 466550512 466550531
    0x80a020a090207081c14010b090a050a0501020d030905031b0601030b010602010516120902090c07020301050c0915031803040906031a0108030d0c020a0b010821090607030806011110 79
    0x4541034030014250300904518040e074a448021035441402003480302100782591600709540c841e03101c0c2083c90107810b0705617003a507181c1c1c0c4042d181d036204000c0c40d4403030740070310308041038a02c2d000b40e810f021240143c004140c051403e000913000350401040c250b071140001d102a108040911a0305c90350900e81c0c0d40604915811807406014451041c2c000034116850031040041c0401d040340c4502a0800c541824509462606110400303400760500c0290000c08440c103016520403180301400040d03200310b000f84501c0c1d8807405404402e0080213251a0b111030201c0410000d0791403440116041a082601a028415640be00610b1940715a001c2000a6580d10003042802440744200595010b200d03a251015454006415580d000c0c069010b040325968020414989000300710351800158880da02144c0341d17a691203c00d0f00c0b00006100b40103124200d1750100f0842010a0480d46111001080f0500341509030300d0483e00342000500032410700992000d0480070312000c1100c50884664004c0100b945c100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 466553012 1250 466551762 466551769
    0x309191a0910020715050c010f06080705030c12070b090a0e040f060b010804020109061103091e100215040f151a0406050111060a0b0d020a030302011a0d020916050f04080a02 76
    0xd00e00c2d0141c11034018120034045100906080546005149452a11b0b101144191130040a20300c0e505050203142450002d52134201180c65412030780300714241d401044401c02440300c150142042e10307005401582c0c051007251050805850a040007400e5800c0380c68443c041c1105111056a040d9202050342d201d89003003006900441e01d01240c2032070b145003d81499030010789002113a0048005224502a134042c5918042054a1030301d80d00800410b010840c003450117940b8510035542070b0080c0e0061404048260001400324a01d400641c59080e103540c2e0707502c6440c40b1440040080303414000004403100c05100314052481100100c2c80c0000031800c5d400204030445401d80e100c58144201b1241d14422020013060840c4d10420715000402e004941c0d0300000c441500e9007070001d42c0b00e1030300400803090590540c0f0140c00c06480200840050018070b082010320020040300a500101850004444502d0440062628000c508025040040125055005030800d41081e00300390310181c541e5080d0b25 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 466554262 1250 466553012 466553029
    0x50a0614010c0605040521031801022502040204121407150e01030e0a0507030c0611062e050406140a0b0f1b19030f02010507030c020309191a09 63
    0x4444148030500204940000c0d064005002010300320302d5403180002c062080038803001d511680008034002184a503142c0101c0590010b4424021007854140c104020391070510890314229a80c000f04582811081c0f8528002c070b0200380101d030450740a001c001b40310b4944598184c1000d102e40f01a820108031803015a02d482400d80c070021800b20300c00c0e110800030303800400c1000405030038a40440c46640c8500ca2500d080200d600c0140b1a101d8014000244201180500c095030302c95618980490b40304803002e40e441206444600c1108010640c5400c1500305079400324800c0e41d1000b40e05020b03941c2d0000182102c52039800209400460360000041c1d242543c00d600183c20a03060550910030415244041c074000c80c0c41e1801000020b69038584076001c01c001c51448216866803a00540701c103454000c14551644070b0000c050341c02d00011a000c503000e0700454508410715802941001c01c08001c206a6070300e1040480300e152512880854500c8a4111100301a421142002d6030b451000c42132000a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 466555512 1250 466554262 466554269
    0x1e0906090501031a041e0f020604030b0603190b0610020c12160816030809031e0d030c0c120806040b13021207050f0304030c03140a1107060906050d050714030406050a06 74
    0xa41d0b134101000000b940d050b40500c0c07440804509999800c00c1450301011100844001a5000c000410004200050b892240388190b405505464003420380c212140840715404000030454150100021000e040100610789081064030488142e9111140890260102c102c0075101070f0300010030075521481103060b404014450390300280300036400f44040f004100343c20701009154a20016018103659020407488000c2480440142490707415400c1a03a920900781c031003d40440e08100381e00503824018142c0c8000c0c0c1d90000b1808401ea032000c00e0403100c100004110640c01642c6004408071074540740c00d100040e440740100141e407440d07450050ba0035a034004281c0400c0003005c20545065862401c1640d030441c3e8181800c2503145039603d000c1e0b4421143e150904843c10000c40c0d140c07001130f4050031040071642c0a401345e03405a52209030480c0c411840303000d04000300310204843d54802c15250321044e40009649042d003c850940c0d000109207500966040d9031064441052050354a950312075003004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 466556762 1250 466555512 466555553
    0x10e060f0a051801032006180d150f0c050a080a05092814010b061e091224060a06080903070c08030d0c031a060d0905030c030a0e060705071e090609050103 68
    0x419086000141080c0308c0c01180d034032003d450102d2180241c82e1602c032084e160398021030314114003001100080043c0070048262050754204008071007414061000c0b240c942d61259a18425603440b01114800f41c000544150358910403080b1024000c9801c810700310354410103044a000305d54503401c140c1a6040c2c290840c0e946030740b51461030100780c4d5604c012284c600705400c0c0c3c1e0001506000c4920b00781409603041d80d54000b015011800c211000c08100e650041d050300040c01d00507400c0d44495441000c0440c0c03066040040039405208950007101115800001c80081720302d0150580d64220354500180e2248050340d001180c40c0e5600441401180c041d0b4071240380810420030500403028000303401c00e504500540002600c16101c103e1a017010815980180460340d50311902c5050513500c0c0d1100a10703000080d91032003e400e507458110200d903505a0080b0051062504166441c10202c04d00b902c51401404c0540e000904500c45010b18001400c10200001e61580b4500f00710890040d4600c00361103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 466558012 1250 466556762 466556813
    0x4150216051c03090503100e010f0b0a050d060b15041a0309030f03150316061805091513050412140a0909051306090b0a14010e060f0a05180103 63
    0x245444140e07204003005845034480c507076000941810f880c1e84805400607a01400f4005801c2811055500a564030452408c020011944c1401280c0e08480f00b0349010782e40164095010042407501c010610f03115400f48800107900744401000035000002036541c006c88040205d030821440510b58480744642c60046009031a51803c501515207920031079411410031030340480130030480041421030409201c0d0141c201d8154802807144201c00d80301034454040080c502ca03680c07401c8014042c80a03422100e01920440c42626082a8501c1110110f1500b07070708460300401c10311b90071086014450255003d404110300c110020f420003003040c10110520744690170704101000007070b1380c030041d42e004907941da140003e600e44425808202e40d501c909000741c021400c154400082c07000b050241405440e202408108003640c81103a442240001d1182601000e541e80000300d0b1420280c3d10001000401040c51b0a07481c4c03500002504c13205081550740400c09031100501c03c102945900c40d10b0b01000120056 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 466559262 1250 466558012 466558019
    0x105070516021311030a060819022b0206030411030d050a0c060c050d0e030d0b2e0c0b0106050a030b1e130905031b0d0305040b040605040f0804150216 66
    0x7208022800d00901401002ca5600004001507020000103007443da6107580d2800d102c03000b00c0140105000e818007a005010404101440c00c0003103410b2250b02400000d07040c44541003140000e0a18207070407035006007881d11500140d503500002c5200c2c038449c126104145490f501414039182e20b113085a0b003400020460a00f4164000802c6504903600010101d03921b0011b40c402c507800c0c09010781c6207500d0740c100090500013800100142082403001d8404004254504c0c04102c200c414400f40601010001ca4030f2026101100c0718405c00c0540c1d504082402e01a265600444001d00b41d1042c80051070110311190826418041d9030f5a05100300ca982e080c0c0070ba490301891035000c00d0a030052042d40220b060310f044005580002200c0b5410005907911096004c001811408040c1d4441d00c05010783c540c580d410070701900c2214066070b007203841485c06549950b10304004104c090310965441490032080800508418010000740ca0048254071000502000c00b1786410f00600100750a01d80d40c00091 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 466560512 1250 466559262 466559287
    0x90c380301031109042102010e1b1012060b0f0403030e0a0b0d0b04140f180111030a021602030a030302040f0f0e0a0b0a09050924160e0301060f030b0901050705 70
    0x401c000d20700301d6003941903807074034684442507444861104000746c3c00780304c0da82c0f251030f019401340080780c04d07442c1902d0307408050740303e80011a41409855a800340e045000680c120340300e0420138030703601c1c1c1c12003000611503100d5400c080c045c1c04c040d828056520000409004050b0310020f080001c00068500003111401c20000f149240034000c0340000d0366907100b1444c90b1a41e140d403c10704000d01c0e4540032124905014207020001e480c00c070b03140c14020074030840900c0c13441e00502c281c0d550030040d0009581142c41c0c55808101a40c44042c01852200d1180c0702d040147ea014064500c40c188251401aa04d5103444130f01165048241c0c01003403044480b000801c0407840060590358400d02c4100b00254842d00707040060030301c01e12a000945485d1800e010480c038010001801c2c04a1041070441014005a400c1d02c1610041d040b20303290078504070380c0c444003826802418402180e00d0024008142992520a2a00310001e070741c0c002e0342e20800803c148110124203106403500001035240c91481e083c4c41c18000f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 466561762 1250 466560512 466560533
    0x20c0307060e01031512020102010606020d020a031b0b15040b0d0503030c0a0915050901350c0c15040c06020c01140c19060f051612090c38030103 64
    0x11032050018440001c036083c0c4c030030340c8031010b00e14502c00c001070f850352204d0300e8440103054030701c04074059032812002007142400002d440501c40031036030083c81c1003809942c04176000448541c0180a44481044420004000b404070b288140703090250f422886002408000545030703610050f0b03001d090794010032000300310080101ca82c4589801003060303030b9410b4032504541d51001c503441100313044c40282c81240880c2c0c1c001c000b0b040842d801d0365810380c0220b2044800002e00800b072042300c08a500d1024441c5030101200c08650301400d0110824140214107000d541458081c0d00b43c0b81004003010200420454001580d0001e4000e0303200401030f001c008800131b000302c402080300030009207020034a902c6e1880100401d40030007800d03e02000c042300003441c00030058100d80b64048202420600041c500c5403107458840c401d48065550680b05510111908005044860b420354440709022030108100701044401c20ba03481c003000b20b9080c2d801d0620301c200ca100071060141c03c01c4180c2040100080f64007980c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 466563012 1250 466561762 466561769
    0x702030a11100e0f0105101d060d0b07020d140304030807180819060b040c12020a0c0b1f0b0903060a020f0706050c040f080c06031824070f020c0307 65
    0x144040e0341441070074128648004200361058150030114560380c0f0001c0800d80d214111004002030000c1d03140d248120440d8051030048c0e006500d1141124000c0030600260182c0003040a003048a0041e91a12410314000c011200c0c0e00141c0e0240c400b141c0410b41c0103201590221030656030900310f0805a03801440f225001d4022001c200ba9000079988241c00900e90f84002c2c60124229654141142204082d085000500b55052403034103203420b00b1820f050113100600d21480d924182d101070041c0c1c07800002e400121891081004002070303d40066040711601c4e015404151480d11b000d01c8105101c0e071000a11781110380c030346500380007074941c548002443e190400e00c00c2c100561601022036000010380503440001e031101d81000f003071040054840c4014010368000302030703080e080fa84443c07400d42d4a822903101d00303420080400000d0601d41c00270210382e41e680f0200c01600d030f080c1703050740034003101c184401000694902c1007400c3c4443d00b5040b0540c015101100d00190407403c6810740000d80342d034a90311 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 466564262 1250 466563012 466563017
    0x31b03040218063d0201090c0501140c0115031e050604082b0501050109060c0b04170f21011205030a0c0507050d03020114130b04113706080702030a 65
    0x8000c60700544d42c4502644842e843c02c10036503078000540810703803c04030905201c100d00108951034800020302c18000d00051030b4004005844513864440110341c404801070640120500138822000b0f0810b00380525035a01394103100c01140300e0305505040a9a607040c03040010626151243c03100064004110140c5c050340050b1156252004010001c2a84040d003280c600c542c405070028a44034001940494180c070342c00e90320015a5522450280e820a14501001e041c00034104001400680d401c520050581c1c021140c440c100f0000305c40c8146160008607140644d00d088413103000030000703514450380c0100501c41e44e40441c0320b00d079207e0300c0e00d07407144000080c104425502c00c0740510400b04074410003007078007914040125044d400d00038002d01511211141c034510001c08103064001100103c9070349900803401c18840c0d240d0355680034150540c441744c4c030307004501c81240760524030f031071481070131411000804088002c025400003985841190010310070b010b02d01041c0704070680c2c00400c0c2d4170f02d2030860 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 466565512 1250 466564262 466564309
    0xc060c0302030d0513170f0d090c17070303110118152406080f0601140c10050a0f18110f01110f0a121b0f060b04050903031b030402 58
    0x5050490a40c0f2400340d083e44141d00345410310a8441d144106031000d64018046900e00510030030741e2960070b104282854280c41000d0200242c038201301e074008542188900451403145945031080422502241810019504507200c10018190014103007662480484000c1241e00c95030506240104180741018105281c408011900540f8590181d02500f00d1030b00700d04803800d04050b4140c4507902900a0000050701c0320041003100c42c00f040800d014500503150311910b400c00000407032254010704032891040c81162298a10401c1d24880c044c062503030088081000d080d56542ca10665058084044942a0841c01c00020841c1c0d041c1d850110300c41110300e100d1000039400103c44030004451008031074028131030b4003111381d00001a140d0107a803117085501011040c4104c180c90b03d00d40240c0d010f010ba4000c131a0503000410201c4402c1006204201c006511032489000c0b6089900c00c40e003003100340c0d00000620190040f69a800c0c0c00500d180b140c0a8914030305540803d030001c03e014030007c1402c040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 466566762 1250 466565512 466565537
    0x14010c02090406060915210c03170a0914030c0405060f040e0c030c120309040917070515010909080d0b010912060b040b0109060804031101060f0e090c0406030c06 71
    0x125480511590001c0c074502650400e030510b50010b044910074440e1240c54981001032804030368030790740101c0c0e4080c0701c1074024011008010810521040c421580140100400b0000a07080c00084400f01190500151100108a009803030000b0903008014006018808038803280d800240004116005075401300385502c400022070301c0340940c268040e034024109211541400400201c079040c2060031412528003054082c24055401421080c500458000700255096409c0a400c0440c07050b10030320701c41c0c1090854040f034082d03a03000054101d9150300318420100062600f0601d01303024000302102086140415910040700384198248414200c3d1548a0101282c2c01000e0303440050151440003115408a4a0000000e01a600c101032180f441c150280e12694407070204441070311039580320300e040b50303c80c0e0f01c0640b1903284031804c080da250340303c401c04200461900d9144000307248404a81c041070030720141d1a401d1054010040f802180307000010004100c0121100003240c2035801c1200d140c0c2d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 466568012 1250 466566762 466566767
    0x6010f0e040f0506190b04030602030c040510121125050a020a06051c06030f080304110616030809160e0901110304140c0f03100c050403020918120a02071401 69
    0x80a59954810300d0040308402d4036210f0f40001d446010102c841802d20224042003442a255600070b0106020f0280010f00c00190554006d58010004030b40b19405c00f0795410000e1004000c5107003040000b00020500b07040c0f000c00740220005101481c0c0c04a0900703c1400b1100d5015004c404543c1005001ea80406c0034002c040c0a08013035140c016064545994a820703028225620036600d48a03080d00032026102d94400e98461141a25441507052106001079190700348507402c00780c0309480c5000c00d040142c5d810396890700100014504a40600000c1e0000d041c05400042c00a041001582003411400d0070903a128284c1003e40381348001000c0684c9a07000c5481c010104003c200300818800002d02046c0009581011001c4120368211507003c0c2c592000e10604480b00c90226406500903100090b8003030143d001420522113034544107081075565000104032080c1a41c160a0040c040200704541403024000501c50a009411641c908241001e00035070300d00651040900745880d40c138094005a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 466569262 1250 466568012 466568027
    0x9070c020a0e2706091f020c0105090d021e100c02030d020c010603140c130c020a0b040b070e01170c03130609030e0319051504020402120403020d0206130b06010f 71
    0x4590b00d202500e161560322031891042c1c030809062100c42d0490700c030718805000100e5a01c40c5044001401c0480e0f26400c3c03c05402c60f00310040c0801a03000d1100030294002403042e0f611803440030300100208204001e010b810100050031540300101d001e251075440c0000010700e8018140101c2000880340a0100120b040d40641c400300f48200c1e000040403040804150800420389000d51081a210002c007405266520501c940035608000c501c0414410060141e1125070b1400e400e00540b02c200040e9601c80842690441c0c08a40c3c0021010034049542c1d48400d8420b11900c0a081880c03925140a003550103080000707015071340702e050020024003e10b5882d111b00b13171019401401840318072000d15000e0284480d03c58200d00910132041450301c104d01d41e40c000701c1c9082d0000d018240000300300140840a110060082c5c0c1c20035001c101c1d03400c1c40140191481e100e5800382e405400d208000e094000d0030704c803018110070100d561080440c004aa02c05080b01c0c0c0020090920400b05100c2210a80303014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 466570512 1250 466569262 466569269
    0x40b0c090a0602060108010f2d110d02030f0a060b16032006040b0f01050604090f060b0c060703110306010806090403021c051b0703053d02070614010509070c020a 71
    0x10450410018082e80c000a100c3e0585008500a0104600e03d081030030440701c9814204603124000b00d0204c142e5049980d114404030b56241c404a0684c082c1d900f03144c03059001c1040c1600030303680081000b406900c4898005d81140612505000c0d075454010044068040c2c46031a41e100d0b20341e11078480405000e02948094a002c00761002040c2c200703409415100d00702100c05071801d161440004000c7c0c0386d086c2072356060b07880040c1024105402c20700a0b0f4010b1018003944115075a4504000c102d107103000000e0b0a1700500c1c0d4000b4006803500c8080101611102c1120410f209001e0003400126a0000714565001c0301c25100c42045984d64101285042c240c10a07240c20b5507c105403201000c1c0e8820001e001c4007944109821504000410080c1d40b1046c0748805405c907003100c0da4030b045e0011a1004400c0324100c40700444000d031980307003200b40b929070710303400040f925580082d42d4001c00c4000d004982c2280c072503004203a40343d0701d03280210b032048100901090400240c20b0b0443c04658038516000081e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 466571762 1250 466570512 466570519
    0x270e2203030c020609060609010b07111201060807080604020d0602250309090605030316110a09060608060f12070905060d0f0606061e05041503020c010f141e040b0c09 73
    0x9115460501030000c0c210ba425490060041c00c2c000303458090009446402000d01801c2190b01c1d07071078049040c1403a000705c01e00f1940c02002501400c1c41da074601e280980c5103555407000062607890001d2003450301d03516900c0011150002d50030000943c0e40d842582981f59041040584e80d00d08140e10005c12040e1009114002226101210141580301800c0d03820344180300020030400c0e403203200301a5203004440340c20701786880200680d00002c04200010ba9000005449814101d44070280f80c02a03c20641204c40003812420800946181140040f08855404d0319003096030032080864a446850360301580c60603640f6240854410380310100810780c4103800c0101401118541d242071406000725104180c0001c4584a03070b0084c004489001c0001c600107600d95501d0706d403418245080e5012a50300e40b10601d42e0032300050041c40000e01941021905e50200020081e420048030a035211019086003440c400840295030f10409403103805070030907000340080403290381c1e46000560740d106110082d0740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 466573012 1250 466571762 466571821
    0x1b02061f0302040f0b0a090614040b0a0f0e04150b011b05031b03070605010504110a080603030f0a230a0c150603020604032d0b0402010e030f070f0501270e 68
    0x184400345620440e00c280c81103a0403246c41d6580c048010030f070b80150199482040045044800c40d2505620404030703030101404108030541c0d1a0515064112140c2c4401a209007120800c020064644e40000c80294900c40420154104400003090001842c25000101c0702030f4100c1400c1c07240800940e85c00b180a44d0790141107402a0728810749039005600110b5002d424440086000e103010f004407094000790302d190b1070810240c00707412140801c02038555501070008010b200416451800245071503039254039403c414a104812101314014009061a4607a0050107103440c490342c4002084400c2d0340000344010480c0028184200411060388001d500c12000940002003186405000d1007001c042c189444004810100620b142c1b0b5000a00401b062010b400040c010343c0a21300d242050107028045507a004900e0180520300070b81ba404c5035600781c07440d5508104540c2d1010003000c54941c141d0180c110040840e6081e0440070f403e007d1042014013000002c2e40c4900c48241d041100e06c00c089180c03c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 466574262 1250 466573012 466573031
    0x3050c0f030307021f05131b080105040309081605130b032a01080117071503091203051501020a1a071b0c060e0405072309090412031b02061f030204 65
    0xd40c0d03424040b40102244160903510b40040e2903e115451181310189a803203007852669840d08e00f1900403242c0c0070214108079901181c19071007441010300c501e120343c850400050600004500e0314090003070300c01034056801400e020540351043e03002c500354401500400c0171a001400282040c00007102810100403048510a20042c07040c500e0551410a80355820030341d883e2035101841d14840c480c4038039550302050040144041910a60552082030b10300001d50445580c3e91a06800292242d400065118401c0c0100704005a42c1554045000d0004100c3c034021940c0d14035540c0b0202d224074410300281000500b0040c064900c81c6442170004008420881c3c0034070f0440e4503c0c0080c05400005440e070321282020341018032800e4001c0c0260f48512115414a052200516070002191545000c007442666001e455443c5414051071041c4900d0a51051402004003160403d40001c1100012601c03d540d085802144968000e5018030b40b000806840744500000d003000f507480250418034194240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 466575512 1250 466574262 466574267
    0x60f061a030412110d21140a0b180114010e030d0302030901050c0f09041d031c14010e18031209010c14030705090103020904060509041b2103050c0f030307 68
    0xd5118500c03511000d20020f181a4080742c5201c3c0b408075014aa41c0040035208140d80a810013010300c01c0f03480240010300c142140c10100b9281c110710644018080c48050043c003c14a014100140344280e0342e10a40111a100c0d031a5101c0d8184140910400c80035900c201c1039110341840480400c01600315008041c1c0140000c0c020740c4200e80f4aa01da5191101040c0e111428078203d038070310000005124200a441010000186243e03103e040c1d000300444900000003031b05102034144056032070000340c004407001300c0940c107640d0502c0d8070940341134141c1c006000001c003e1001c1c0e0780055a1800c00303002200080c01040c5144030b10700308124031100540c1000301c4240c054100e8100e08015550b060307842500b881c8040020700050300c0400100d981030054200035482540984501200188042031003a61040854010803080c1e800740c508032521580c02c500044400d40240003061202c5441070619810000912103440380c80004081000c0054082c88083c002c00c0810a10050f00302565505e04084001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 466576762 1250 466575512 466575517
    0x3030c0304060305061518030705041806390e04181407060f0c08040e1f0b04030c030b150307080c040c030203010e040f080715090209010503030c0a060f061a 69
    0x580b80024248800107003142843d0403403a400518000081c0d0515100c8007003292175030520100744d030f01441607007000200d560351809180d20f40920440003071108a17032070600307074156805404090b03144500c16005c07052400e00011700352060400e080100b08586210301007221040d82412002c0d41c864201155248103a41c101e15440486106100d40204508038000d49511b84c2c006101d00700100b00b440d100c500300c483c043d000000b0b0b01440303100c1c3d00d0b10f060744030240c04404070029507404c4001d0010681030f5965584800481c030180c4a40e40d000c0c0d040c40c0ca543d640503120000303404018440c09820005c500308042c148404540c112005058494298684019507034420708603600c18891420442c41c40b182601074400c4905039900d00c100031000380e490761250100b60314003a00c22070740300904100d03003004501c3c02d00c0c009641400d0007070049a110018010401060810b82015200780c000b08640842c55000184850905034003810128101440c0312164008040da03503c9040d02d5240d0814900001400200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 466578012 1250 466576762 466576769
    0x180411220b12180109030206060906130f0605030f16062307031d0409020306131a010b0a1205130311011b020a05060106170103080d200c07090b01120f06030203030c0304 74
    0xc000920300f440d4054282c2e0082080640941c00c140049400c500340782075a69801400a002205400c8903061203208031240300d400c10700056500c940130b000520741032002c07409070140c550041c0210401c083e100700e40b07090340c5c0c030a240a0001c10000c4a81701d81650005401c0909029241e0361160941c3c20042c0840041c03040342c03400b0700f0180c01030708254a054899080e91710703000f40003807a00d0340e01c0402c0001003480303511040d1114546041181d1700d05440c000024085d013144000b41b0745812900342c01520054144110360f002c070341400100180e6140c0746d400583c483da01841c00400c071003100b234400c40c010314600a050703411400307003502030704001d40010301c1540e81403280c0101c41e080d80e42c501c03046840381c550b910103044184001004001007020180074100d200101e03100007450b10356810b0b40c0705030784403030140c034403035a1307201240601070320740240002002082c0010091000351a0000003c0100a5807400e401c1d074181d0700c3e009075007045c0040d4040c6002c0e43d8041d0441b903a83c4030040b0b0703103696a04981b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 466579262 1250 466578012 466578031
    0x20619020601091a0f03101d070503010903050f0315030106090c081806010b0d020c0d170f0106051e0906040b19020318090426180411220b12 62
    0x41c0001108001445a9404c04061000050120400c902040307501c1c4506030101e98103204200320f00c0f42d8000e0905c28110480d0015030400c0155400c400403e04000d21070b40203138402d0345012800c8010a400900f03c4030051040c05003e6542d9a0b414801d03013522a2040380c080c0c056190000114044034545d0224010501c1d58982601b40e0b9103581c0d8542448600c0c44511000d030300124010880c03400c50342e0240045400401c1c0141c24614001c070f00d13a14058000c0300d114006058000e14941c0751081c1010203402140050313565005605080c009409c0307200f00340038a03a4413162094160f403c00005003e48000150040c01d0341e41e00d9a4518040e500380d0070a44010101464200e01102c0c0180000304540140802c1c0681c0f0680340340d00703c204100260018020780d04613070004800f0440c0c0055107800a0740c0c1d40740a40140c1c6820b68580350030503810711480075a004505e01400340c510829048191a101c1c440c1c1d081c940e905012030880d03034440d9907042d803014403213040118411518204459100348a841ca81 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 466580512 1250 466579262 466579273
    0xd0f050604110f04090504030c06020307021b010c0b07050c0304031506060306050901080c0409020d05100903080901180b04030201020f0a030609050a0501121704230a06090b1b0a02061902 82
    0x150b0008410320a80c0209600002c04010810402080d6086198042e01070305180320105456150501668812100382c401604045960080c421441e088120700d4407082c640b00b8442d000c107a662500090b0060030010034441c001c2282c0000c8001081160081c40e13206040220001c143c544180c060150341c000c02d0042400c01c60042201c3c00c12680485c12682080014010f0209413010b1000508000340c0582c0c01140c00700640c03011400412980d400f6841c6800300241c440100c0c200203000d80380161150500742d050041e1440b10088071001429119000031540d13006444514050b030080c0b150844038002d81d0000301d06401c00c0e68059125100b200c0680720284034550b2002d1001080301c400b4014481c101d0509101c110104d14010a00f0342252928402d684c5000e480e1f14281d110b15048003403511b080c0e03400501880307260600300c5480e4010015402c01d001e1160034003046c6507050007111031528803c040d518446640140402140c210250081c1520b60b07180030000c4070000b000c00c14803140015106d10f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 466581762 1250 466580512 466580531
    0x50705090c030405071404060302061603080c04050a0918170309160f0603150f092313080a03090206030a020a110604020a0b070201121407140a02100506060d0f050604 73
    0x34003040783c0c810799100b030140c4159030a000000512114101400760041d5590340c0100060301d0342e030b000302144e46201200205210541c81e008064403802084405a840103000c10042c98580072841020384d0403801c03001c60090507000c11032880b520300600c09880788000c842104000b0200314000c5000b841d00100b0382e010322030500c0c41e00b100200d00d442006a8808101c0041041c03600c80d90010240180c4a68981511960b42d00079495104441c1c00075842c40399104c501c0e48420401c01c1d07601c6000303001050020800e1510825107140c80d001d0440217800d5460014002181d107110340d0210031825401032005840341403281c01c40c0029042020355001145c1d07007100080c0614400640b01e44243d0b80144100500d0b800c142c00071000f5000083d0890500841212a103107440c050f00940d00706800400c1c3c0c1040910340007200400d0f110450307143d1001c00a081140c41c0f802640840c0101c01541514000309840e111040498201e10501d04525222850000082406041030308003034001e120446007402075289 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 466583012 1250 466581762 466581781
    0xa090b0c0901090b0306011808010b01020d02062e03050d031401050f0a0303030f060b0d0b010906050a092309090d091508010e180703050a05011508102705070509 71
    0x19200c401c50200c3e420f07207800c20624001c000116800071040c503100007e0100b40c0c49018190785260425020750751612070f01c980650b410840a55a2a014401403065041003806000e08023203501e8150401d1554201c0c081003004181c17a900021940241114030054130700a0007001010480c0c903540000c0500d400000c0c8500c1e05801110802c40010311402d171451031650b0a0300180580c620420800b603c580c000120000108040e00b0031036a10741000c1420004503000400c031000c3c6030001c1c001c1c09424071803000d6084c5e1180100f400d685140c150350085507058110842d81c25403031741903950700c0050345d0708015142030b000c501c407032070741c002510703003500d090344412050880d45d02e1008070000040d03050004010107140305140c585c000d00c1c0c02c1a007045410250300b031315041078481e0300191810b903c0130201c003040050074424080e03c0c01001c00c070314041d5828411155251805120100d01664813040b40781400707000f04d00c0314060100441c0d8002c040f208a4505151a200780b4860702d41b02d1124040054088e29 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 466584262 1250 466583012 466583017
    0x60f03050114130302060a05040c0f080309040e030f0a12200d05070206010503120d0b03070e0118020304020a0303030e011e0c110c01020a020d0503120c030a05130b010506210a090b0c 80
    0x2581a009406c1e40c0d0388030300109000744030080c42511301c50510f0400003980000c071210350740a0002403010719580e141c2d40040c002030742c1c0708503007a4105a2041041c1a4081c0c2040700340c070700c1c2050600d40050708409002086000d03144840804807220940010030143c6000c407401801507255030381084c812580c691900380e864840c2441440e03016088002060301000d004401881003010003200000c005521001291030032243e500301c0101c01203807030010311005000040c0070008141c4e1040c20f5185140550118490030103d110040600d1b03100d20154482410a401c48046010801a400390900c40466503c014010485508001c10300640d2110032404002c142c0180b0120306800030006004036a09100d808903074404d007071700c0c00d00041c4503442c6190400c002d558014403010418548034140041304c641150f0000d0f103804090400802c000c00086c480c9000b40d0304603601150b466480f06403601d4680006202040c1d801000b0100d541048500700141d401040e44074040c00041070315507600b44e002441ca2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 466585512 1250 466584262 466584301
    0x80d0201140a0234020306090a15110d090305190507020f0603070c06050a230403091503060819050601061821020d12120218060d060f03050114 63
    0xc40c681c0000b8440e82e00b035400606101e20704074104900d400800309449940c0d69030520400039004030038191070a51808212071500010008041d0103c000c10380d0792100010680c54070480400d0f159004e8100185200c1c3c00d4442840c100001409548250714006003103520600050121035103a01c0361800e05481001560203c56000e402400303c10031074010041c0e540c100600102c20441f103c040d03100010183d0090f80d008120b420b9000c03441980c0c0011500c03802007041d0f00e4452210041003000040f991281b000c40407a03441050603000d2400900c0c040340500740a8005c034031944515458850b022484000281c45c142c0142c041d00c04a9072207180444804115044800070102d03400018030a40300445101c1201c1040318840310b000301d140f580032074000781246806540d580c18040440f000c140c0c00840300e01c3c8041412004501d84134891000c040580c105101040c000c02c00442d4100e0300f074030141d0000001c0e040c600440f14460760741c3e15019005e094880d50749601d0440881c00301d020f0b80391404000414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 466586762 1250 466585512 466585541
    0x140a02130b06070f110d03030e0715020a11030c0d0b09010b030f0304030b060102010f0f05040201030f11040909151d07141c150615023a09081204080d0201 68
    0x10031206840340324a0090744001503d00d11000449105c0981c0c803402c00b5803516119440c00700c0d161400008850410103154071a448000c040e030305558426074082511544194071001182800c9604408646030060455029401c490310860f01414003090300305503481490114001e002c030303554040925403242d04041039444281d000380010310005441485007035200c84c043c4000200703281540303000000d0303441105d04c0c00701ca155580103100665a250141d000c21880c1208240001c0c4091446102d40f44150720640030541d81c3d0320008410008440e03807291403100c2c155014002008400f510010700350644204100700d104601001441c1404000700074840030008010b40c00040703a01240b143d003017110000c11a40c040302c1095215043c4102d00c20380001d80980040e03030300c0f0202241406854110f101000d110301302c14802c0007140440e05a400241c034a07400e040c0e589266403860400361007008594002c0b640700d024028000401d83d03103c80140080f510b01c034007141c225030f002c000142d08894172208500d81 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 466588012 1250 466586762 466586767
    0xe030306010f021c0309021207061e03090203100203071b02060409020d0902041a0f041802040b012c090618011a071502040306050c130302090c07140a02130b06 70
    0x2440d80540100c01c4044828015164044441072149400c80a00481500480c1e6501b10040560522603a82a060142d4000520b103c506114002e0b1a008d41ea100450400c030800c0300748072100d4820b130894481c2d19806800c03100c00c4070351001c0050103900b045420000152000851300e401860403100c1c5000c0907005840342c0e00e0141410000c0001c3d5204140c1d06c400d198540707116500503111407041d1041c403904c220814840341001030070001842442c10440c0c2c03056080140c10b80c000c0c0c20101030124240d138116000941c0300049801070b6076000e5234049070212084150101d60f0008200480260848421202ca911a940d41c504016501d28a805c0d2142140c000d180184100b00d001c10040c43e0b100c08145501c0c0c00c15031580e48e1840700001c2c410003015400e40100307040007001860b00506800502c1c0e000321b030382807900702142d00c003a500036848068466068800414150038903041251040c5400c65014180d5022910519640c2c1500700e5041340a09440e11240200e01c00604c81d1101402c0c0043c450352 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 466589262 1250 466588012 466588021
    0x15090609181f14040b0a0b120106030c020109170322081c09110405040804050a09020c0606060721051603080601020c031b0d0606081e0706030204030c060c0c1502010f050108010e0303 80
    0x8020444c4890741743e00b01c401e046d404200c55104a01405a5910b8034080400c15810441d0007000c0e540c28640e00019a81424048800200d1034004a4007984002090585a58070210408148540141c45040110000c126001403100a41c0204400b010780000d0080380444408140200c441d040b8002d0080704c444d041910a6250507000700b81c0186c041d03101c0e1820142c6400002d004000c01d0340c0100c80d2070b6070000e01c2040c81d0b035091194661022048910f2400c0c40c205403600ca01280c25014480d000451201c007420704107010f4801c0e2a41c040d40504040e0004909103070103000b45400f42e401e9409071050300d072020503a14000031a5100f50304461039136807004501c1d105010703d13004151411500140c4828012400c81c4c01001040c40e030300014030100c00c10890680440703041c200150020000c1600401081c808555240042e0701114290304e48500e00411504186a0690654100e4010406004081c20344943e054204040700e0105400411950b640d40315514200c03070100100e4011a082440000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 466590512 1250 466589262 466589269
    0x10030609020102011b020a020a0f080325080711090a0b100516051902010809010905060115050706140a0b09060d0f0516150f050915090609181f14 64
    0x1440e064818000032a00050701216403041c0900b0380845401640215030010540c0341c21444480141318956001d00014144481541c0780e10415401105403a948103010702020120290f80120766004a4100d03110085490900c140c407a002203458402c3d01e164020419010640c0718401ea001030040030901e40034100744059070310382c02600d1181c03112507060082c680415810320005c000c508109501d10854001480050002003020f0072000d0b0580c0b40180c8200003800002d10700307054520310781c5081114407918030101c03400c1c441c1c4d22000700418107103400200114241c1d224180501a695800d0100380110010711a9500080b12038581c07014a0391407100c00b142045280f03220b07042c020410744e4040e0b8444c64040003600500e61000201001c258006045541e010b08400804503691a1040c40c110300880080d80814406030080c000010015030064181e90750b00441e0060040502440c0c8080400e0b400b12820391030846e4403000d207030f8048040d5142c01d42c5c3c400c01001038a641140a4160782e05860a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 466591762 1250 466590512 466590521
    0x18080337080c090d0c15080f0622020c060a050a0c05070f03050403020a0f06030b1e01080c0408011a030709020406021f11030a1a03070807030f0c0f080a03080601020303100306 77
    0xb10380d10ba020400106841361507084010007130343d0103444186030140c03400185c0d103402c0842841517404c00451006100d12080110001c9420080844099602866001c00c00c100e034143d24401c5480da52002031602c000040114035980b0500310504204120345d103800c0c540c82030350540200b20002a20800c001030000300d003c1c07850720501e4000e180c19410291241d001c80c9806c012034000c80c0301e0103d44142041095418000c02c40044030a603034a0200782c0f40f0388680101c0c03000300649607041c409158000380110040c00155801401509c0080c49103010201c01c1c0c441c9641202c9000d806806101c00100701200640211001c68400d070b80281103102107601143c600e01069140c42c0d0200c1c0d01c40c4aa03a12808410007d0740c000c40c0001d40000c3c55507006c400d00c090890303042c0c490600a8106481c100302220002c500d25003180c0c1c21600810100c10b507440c100c10400030b03542200c180d02c1d00c1c500c0042000d0600007940c0400d135100303488121041c0c0302c41005907079a0001b01c13180307000030130401c0301800040d40c40d420 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 466593012 1250 466591762 466591771
    0xd0e1605060a2a05070f0e1b090904020409150b1f0504060804030e100824010518030a140d0914150903030c061f0f14101808033708 58
    0x2d03202d520411642e04da90600d0010b43c090880c040007140107100c4030b0902d103a440c1d00a1810421802030914110256105010340c2e02158490000c42d80000c040d902c03a508182051360303100e915019261500460040145607030050540585160085040d14030303624181c0090740f84140d00e58a003854074242c000ca070141c0004004804211202250320f405484500c9410300501890700c43c0006890011240e0300aa0011004074100d040b2000350141c1598224044075a8070410010480023101c540d03002c20715210207260024030f80e903440a031402c0074080201e42100c80c540c181da90384001541d180141a58030080c00042a0300082e50102000c40e400880014084418042c0650741081d42070301703486080002c1100d44425800216050000640c690310010018000e0700c3d5005010031b0034603414034000f00c606813400c0c0c05090900403045038a8090140c500303900c030341c044080b14007a0300c070a00c21f5240c1d086000c07209824480301c0601c3c0a40115020034080c60740e0794001890074060507050440e180b200107030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 466594262 1250 466593012 466593077
    0xa2a060c090911030f13020108041203270b090601031703060409120906020705060406080f0c07050303011205010501060816031505030106120c05100c0f0201050d0e1605060a 76
    0x580000e24010b090040c10004544903480940700c0ca09402071130281d0200a10010401100c0464080140e800ca5805078006420152900c83d0700e0428105034010141080306031000d100c200c4400220141001189840c14401e9404201548508586650390ba90a0200500701d12080341682c00b030828100c05507502200c014004511207941c2c0d1030384506601440111400142400c504bc02550380405c800c0b0000d120554040745024505000100b440c00d0207412400c0c0c0301e00b0074000c07070761005141041d144c480c0d40140540380e4070f50390f4039152054808000002c8034154240000010418003551030075204003084449041c8000c410202200100006500142c0c0301e105c400010810b51001d10400c00035248010001400317a0341c500b0308c0310050b03442d0340c0824880ca00b00504540c100e94004104075816a01c4042d0b42c0b411520751006940b41c0c0121140084030707514203202081801000904042c00e50b010050f0fa0710020744a4041c07205230b00c510401d110128a821a0701c0d43c2c038103070103d1006045070400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 466595512 1250 466594262 466594277
    0x304050a060203090a0507060f050a0509030705060c030d06080607140306010908011a0a0f05060702101b030c063c11192a0b0603030904060b0a2a060c 66
    0x1d5941c403003203030000c0d01c1006103903200f05100401c00008000c2c80001c0d0450342044c0382102c041700b20082052103400003090400c08042410196031b03d0400c4541e0140c00b00822403600c44080501c0c450342c036003000703080308419030030035a000840000100303205001e5000340e075481c1d020074081c10418a0350342c00a0213a5041080d4000f00040c024020b100e203410036058004a1032800003a01c04010007c20190401d1920325807071001005150744020499044503810782e48020841c03840340c0140c0d103028600601e0f415035480c1101d03013402c0550001041c10481e20480c000c020030307000350454070304c0300502c02c0020035014001800e00c00a120b0005810100c20070f00600805d04924002d0b060000d50003003020b1031035051040c80d441c0710702c43d000000d803400c5441d0640b000410103001c9100c0410f52040903c00b91050103818041811520280215500d090014205000d02030f0b85080104803544507082a400196131014000c1000c0c2200a0b10301c980144840010084100707900d4000003009030151800620009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 466596762 1250 466595512 466595533
    0x306130e120a20030901020c2719050708060406080c0a0e090a0804080604020a1d0705031017070305060603070320030a0f06020909150303072604030501051609030b0408030405 77
    0xc0d00f222040c0c2003010014684900480300064500520302411030310580f880040c040c48108140c2910018040b10392103408507441d459002c100c10740070014240c18840c02c10040000381c98220610a0203140306540c01c018840e1382e8820140c88075041044180c0c03001c0e000d0810009e05810810f8140c000c5651130a881d5200103555600c02e007a8819448662990071410400041d841c3c070b0320408009088040700c0358030a04006a030000c032141c00610b460140031011011501c01705614181c8070140240350b40c6c5918940c00701001941c0e90b07107288421100e0b0b01c606000200d090601289000460f03a011003407984527480e5580501b684c001808825400d4490360b0440c2c4040f0b6000e80801410310b00030240140c3d501c07440028810072000c02420404d031010000175124041e00c0c00001c44045e01d4200700c49203401240d0502d0f15200c0b000b4144001c0704108042004030a01a040d84000c0c007420301900d00c040c2c3c0416800042c0e801d02a6440050031010000c070000c0c0c086a0103c004540c0603205200355803241c07070b5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 466598012 1250 466596762 466596797
    0x3160203072c060603010f1208042c0106030b0f0d06020702100507140a0b130f052406040501050303161704030c060215060a050d0f0b010b0306130e120a 67
    0x4294410300c0404035105261009100781e00030b1a0008400d8402c01d00d90b6060000c003070808401c0d80300b481ca00d2050390b0010401d002512050b10081e10490b00ba141c09040c2c1da818401071a540c0ca0320311400c0c17000d503100000d182c40c0039126425407480f02074480091000440100401000703d80000e88017a074003081500016900c1300d882c0c0e90f84403c1a2119925640c05040c004e03040c0007a01805c81e1150300c644046808545003120041d4031049001108502003414900840d1502407504014120b20902502d41c2d0180c00000040c00c00352810011f04142e651010200010f4940a10074150141c10411007100021100e5800502590162000c0c0340e01c0e0781110410303042c682c840c0e4421342d80b540c486403042c09240d0741400070f45551707604020001014100a800a9503441951150780d22500c0300d0b0a20310200070056610f5001c1c80d40143c5982c0e265070395081c01100661048807043d102d02c110444082c00d200c490b2040181001002000b42200824500c0b82d440a601c5101e241040c007060016011580c44c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 466599262 1250 466598012 466598039
    0xa0b01060203072306060d0501020d06061d04060510180f0305011e090b0c0a0e0402030a020a0f1b080a0306052805221a030a0f020907030603050316020307 68
    0x40c00ea40155502c3d0000d08144416654200702d000b00030055460403a440c2e03000146041d00914215041c104d001c40d80d1400d64024800c82021042d40d90030300e18000b41841d00854681ca0401c2d075003229170f0384012a00b08000032500c06003e05540702c0c07400c016410364144120302d51802c5a14280300014616100e8401c0d0720350146583c0110cd00d0b0b0744901285c900d0f258490611500410344070000c0c06007030b21a83c0c60384d014400040c040c04014402242c0c02d40544e200d10b400e511041f4024000315541c2c03c1040655000e544401080808658110302d1141b80910441081d0951028107030350b940c401905035240381165110443c0d220416490350004030340c60742c40f00c2e203451603290784801d8980301020b00d0250f0303000e504035948032510404802a410a100d20102c0101604c00c000841c00070b00003642410b03c03805550100f42080d0584174502100e82080a910702e070790007850084440c0c000e5551803042c110140c039160702004055800610019550445001a0304d254910050980c0c0707886803140e40c8100600c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 466600512 1250 466599262 466599269
    0x80a0b0d050f280201051209151303030c05180d1b0b03010302030c0d0b0414013806040b070f150905070e0609150d03020c1203180301090503030606032d040311011a010e030a0b01 78
    0x3d942038483cac0f08160f0144103103682c1c1925410070701c3c18042601414409848038403485c0d4041c400ea00025803c01450540d071a81808540420007102074449540300c0e0321360001d010484c000d220f40c2034144200e2030f00c41e80060f07440b03a100d2200034050b03a0f03d030f03694407584140c1c0310561015901d404900098a05840c407281c0c4051280e4205201042d886800d05501045050910300458007000b0510144101c001210405600500380041202c960720380698801c540c21040980030789001c501c03104001d00810b0b200100c0b0828000001f10340c89030340403c000301500361004034046c542c181ca1213540341416001c005109001e070040d030b0710b802c8145c0041942d112000841c40e0040e00001080701071026400140b250416083d802040020101c1c0d66507a628803000e405a84140400310024000d10358808d40d8403000000014500d04108040c0d0040400700019101200071500c40e0603100303800c100500c600c05654403c0c41d1034100300a880c1005642c110042c035443c98242c000d65182c21301060307070307000158000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 466601762 1250 466600512 466600531
    0xa17011b080a0c091404090804050406030c0303180e011401050d0507030518030304080315031e01050411042d150f080f030a080a0b0d050f28020105120915 68
    0x140c070342242440111250b5030189814008400c2c402e2080f148008410f0885d1001640c00003010305481c10020080c0c0116400a90b0041c10441c0200400075501c144500b241e200b032311042ca2011002808003a80102d83c01045002e03040340004102002403039607881c030f940d86c040c1850340c43e001d035000e000800d45030b00725031031070200f51110140140a4050703400d119907400c03000085c5085042643c2e07020307103134800a0315203c82c203014403c0008aa640174852002c02c440441510b104021034028003a01900d02185c06660f05402c2c1903040d121400c050107a141e00e48184064004200e1542841c0503036030511030807480f40310341d031008629071031041c5070744560190141010440b001890442442d01c0c10550201d488000d0b00f0503c26401c889d0b0300310b40346540081914101044012940010401504280e4006091445041d520580c140000318106001140440d01c5103c20341107400300c1d1815051030300000b80002c40c20002c00202340340750030003a43c11900d200151075000b440b06030b15100ca00c4082d100101d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 466603012 1250 466601762 466601777
    0x100212300f04230a082505011a010906020a0201080c09061201030c30020d0c09050703110a02030708280f03050609010e161713050118020a17011b 64
    0xd011016450509040016582e43e00400500b40400d0b03c4043c0b5000081107103002080110a13281c06c11504c52500d0710010351550030101c030341407481c00b9010b6400003002c51881901c0030115940b0844d00d600584446800a10700340e140741d8011200040000c200d0040b40d4410f10000750307a641c80c24000c106029541c25400c04550560a140c038920a007980129404c4e0028440a00d81514140029020300c0b420541c0d4a410152800402d480b481d45400007480407807042008030b20000c01d0740c00140250510380d000c11421035101e40204103840303100320a201680c41408904000351323510000700030152404117011809080100c1c0346000c0c0c2060b1140c0804124060241102c0c2c44d07240c4541580604106c401000381d5242c1040c84100c250040d110302c600d0300c0312031036200a042c0541500e18011240e0030072810103190070084801c140903045400c80303055013414030b0b1219042c46030910b4144d5a8000b010700394140c1c07900c140c41500e900c003003440343c0980d5210350117414a1700c01001c0c40b03200240c05071209074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 466604262 1250 466603012 466603021
    0x10519020705030f07140d0b041e0f0c0e0f091c02030f0703020106051504050a09020a05120f100902040e0a0504051615030b03010504210507020d0f02100212300f 71
    0x52203511b00103802401142c0c0640c0220101303400049140d08280c0001c0030814200201030400c001a5050700060400380307003200c010040111a1103244100e0705c00c680120301c251607040070341424910507100441c3d03541c040c3e00c0100100c6c1e1102104211008603004581ca03110b00900d02e40e101d0f422408003600581d541d000f0800407802c198000110324400c1646c554906410a00040c041c031849000c0d41b081590302013048807089010f03200701c45200203c24484085890301c0e248035903440a00300e0b104020b0400b000e4001800031524000c0d0340079940d41082d40b580c0359807031801150003020000d209481910513030003459411346100120601420080c441300740950004100641a11b5020f0340b00e502903071402081102107407282094207000c7c1001183c1d454200c80170700e41241d40d80100000030b035014114002860802911041d41000e4a02c2602d13034400d030a400d0344083c1d850381c14105000c0c4100e03908000c5400000101210800d90758030f030a040c0036145124030a0000d00080450760300400400c0c520610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 466605512 1250 466604262 466604279
    0xb0123030412090b0a03052707030201020f0a02010203030414150a05010509011a030a0902210a1e030804110d080d02090f040608030406050c0a12200606010519020705030f07 76
    0x400c02d10859080c0030b003d0301e1400510000600c40c8186110806a072607022510100e10700e01080da4200400b111101c0340c0010002c12070702e5242038402240588510b41c0c0c2c441d80b504022944d181c40b0b54058014508603691600c845603c0302a01e107210741c407806101194143e0182c046a0036005603400680010340c0c0d03040105000c281038068006c440e000c88000c070310a59410300c460031207a0159a50601144990346032021070b0340640e56841090070f9248003a00b041e0000400910032140c01d0240b50703034240e080511140450300e14082040500043c10b031600007030108428448004101002410300005900319882e45a050f42203902c8004d281c0383c0001c4d55132160300c3c1520724032807003000c2141d04100051400a50035581d12840c410407060002c0030445051f417000902c0f1402000703030040000913200b22115001001da0311266141c0c8080c0202c402a891400000280c4511900060f1103103858100490880310400a4110000302184194800455152400c0c0009104580c2450040c06840d0500802 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 466606762 1250 466605512 466605533
    0x9150405090f06061801030813170d02190b06012106030b070f08090715020f0102070309210201080402040209041805070501030c110307110a09020f0d0605100e040b01230304 76
    0x440741301c0c0c0314040000002410f001724103030450354413900960b501c070300080c1c4d16803601d000e0b540609260300121030461800000807809100d401401d60075604c14100c8901e420001043c0380d036024201004000001d00d907540602e035025007000c0c441040307480480c03d20041c0029074905d41c008803a01c42e808001c0c40043c5070051400f059250480c14251014648040007551340c80f00d0380300d00e11854911040340c2c610240203000400441111100940d5900f5140c24090418420381c8502111607032885003022210000301070380300c0701640c140e60b0103009884070f400304806034000398003003544155100c5076000e0019000040010861244000c1d05010703141800140c1200d1342046a0014030640900011205002204440300694410068900c0800b0304004c124203010036000604084d00c001241100d2a4600c006825910340084080c41200e4540c010b0080c41c0c0ea42c44074942c00308550102c0030440e440c241d0807800c00f5060624040079020b40b0a101030000ca9100e921180e0404000028081403042c503104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 466608012 1250 466606762 466606771
    0x31506090a0f23220b1c05011406030f07060804060b0910090b010903021c0302010608030f0c0115050f090a0b1302070b010509220c09091a01050a1409150405090f06 72
    0x10008603501300c0c0044a0201d41c02c90805a0000303070303104100080ba945211a00c40365504070b10301800b4108091410600900003400700c400b04060240c006081440c0005942070340e104140c0141600300d01c1c0180640f201c00f000f610841e449901d44d8981083c98551090307c2d4894100c0800d2041310510b00180d94080b900140381017810010400802d10158a03540f0449200d0020595441c202d401c50b070404030b004045a81044601c0d000004000b0700a205c08009800c081e004e000c003c20404504070718041660781070f40b1031076410028004080d0514035180c64000d030303c031043c59804203c99040a000682040521401c840c41b036034046400b401740300300980c2643c05003900746c0702802e4a0411300745a20000524030300030122400015020000c01c0202d042030303001424010001d1100c99a9407500322245000b51707102c64644004600009020316004482c0021119001030071640343d9600401e000c8805070090940b5510a003440000348152501c1c41440e00c1200c14a01810200ea0102c40c84d07810904041c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 466609262 1250 466608012 466608019
    0x11010311090303072603010303020d022b0c15060b071a040320010f060b04090c03060e01050d0305070b0a090b0c09060d09060902030f0d14031506090a0f23 68
    0x25007a4503403000000c032248160401ca0864080c044098803a8540c0003440c2c000b10f403060b000c0000001c0580018014503000405c2d02a20202e800c04440030703030f1480301506040300402c2c00200340d8404501440461028038001e500c0c640662600d08051026241c86a011f0315002500280300c0050180300710804c02030140c1e1000c2200c45081c50b480082c944000455503804800242c154145640070962003c0c800f0300e50040c007800555614048000e25410511070080c07036070f0500c064002181d10078800d81c010303620f505049001c16420301c01800f014805041003101030010412994020510f6040f81d14440c118180300419023200ca40f13007400e400c60016000250241081c40b4401290b511ba205881d483c441003000016640454101480600480540a905401020b0010030844004100c0d041c080c9940d8a5202e01e0420488000039144001c07582111080440c0d45a0080c42c40c0c503000600303540f90300030005a040340e1900054501c0c40070940c090401002922045442115100710b00c444180c0d048 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 466610512 1250 466609262 466609267
    0x3030d0e0d0e0a1503180b13120201020a0801182301090b06041404050a06121a070219062004090b0307051012050604060812030603190503041707090911010311 70
    0xda500201d03010210384c103001c0c580c0390740d555135082c0c10b1941030700c0b481c58104a41280900342900d001401c106100410780c2c100040740c407850038040c014021150882c8840d5140034031a860980046007103501c1c0000124100c1c2c50344a40c071600100c2c1208a407038480c000f80c840e0400e503d08080003084a120709203450140009003c100b19040d92804000010785066801281e00d03511208500002c18050300048400b12030f48101c5002d001c0302c2c0c2045a50001c440c549070f0415158814266580d1a0340d9007000351050062484c01c1c000340b01c80c2c02c00003c001d0b10142c0428240306680c00000c0d140c2140e0841c1c13003202c0c2e48510711045840c00300f2801000b07210503a0050340b244c1402e04001c00000303c290041c80340c0307902c0c0c01c0444d509448543c0040000c020740d0003658500c0030800c009040aa000f079030018481e1042550000728415420800504183c2c05002549041c2c50188202540001d106410b201030240c0c9030001007141d001d014401c10b080c4110070494040344050005801c90300758003826494050306 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 466611762 1250 466610512 466610519
    0xb0901050a0f0603020c01020927010b0309100b040209120a0b0a110a0509181302040b0402030108150406061a0c0f0706021b030102090d05071d0403051803030d0e0d0e0a 74
    0xc42c807101040c0d812514000d40d542e180c600003103029101d1071504a41000b903049440b44010503100d80c6030380e107a8083c841a101c59a03241c8641c09140400e0350a0035860b0000c03070000b44910000d900c0a000c00101400c003604003400c05000401181c81c00f1a22403423a0001d2074030108200924078410780c4442016410420000c2131401014180601160b0310180708000400c60207594503800000340c04500030840e2601c525004190b10b00615080b4000c900550414102a0300c61406009881c140d03040d120041c400c81e203050904200071000644151505640c624010660328800388a8000841403075903039941e02c06017442901d240101d00240ca4586030801042440242d501044507621100040039109043e00b9100010b4024410b4011041e8400c80300c81c440020010041198002c603405d031512441c05c030a2028a28071035100450740200060400c2100480a40c2000f4001d11020b0f4044e0032281031071704545c0c030030040f40d48407001501035500008400d11707d69448540e4008410003500d4041d2414034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 466613012 1250 466611762 466611779
    0xd02030609091b09190c020c0111060c120c0403080705010203042f0405090c09090d0201050f0112080d0b030a0c03021e060d0209030111040b0a1805090f190e010b0901050a 75
    0x42c03d1116880b804030340012904d545101c503010b11181081d140100107800c6550760203551540c05000250120b4402c1070300e41ca08860208130548101c1c2ca13a881146424411140800300da00000c002a2450302c0c00e00c00400819106405000c800303105d00001a92400d00d41002c41240e105041203402c5a0710041d02d2080000c504101e1405911090320040342c0e03a12840540f6081000601701c02c2e8104080b1000c10400050006d840b0072a0708207600200400d85070989144c0c01d0002c00d0140a125140b0041c0030300014131b0b4030005000c0b010103028001008140c450002e4100b02c5801c2d010340e10480c64041c02c0c015454401910f0f040c51828540c10128090300c03402003100c1d0b00450140c240f13000e60200d0f50441c103840079009243d103541540300c01903a45403a000c1b8485150401078621700010240c650540030b00c15040c19090940f02d00409400c941e0355411410b448241000b810900300b19000c280e861040000380c060f1100345e41c0c031640085075140051051104002059101e0380c407481111804022600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 466614262 1250 466613012 466613053
    0x6050904050a061d040b010603020324011205010605070b06030d0219050703020a030b010e01050415141827010903050403120c051501140d1e0c0504020d0203060909 72
    0x1064401084035510a40e40d84003c02c2d096100103200030140a80d00982d64441040c980b295101700768010380f07079803211000c0382240400c6600d5002600c072540d10349006640c1d01e61003c81c0180524154903140b80001c88441070320000e0b4410ac0c04070358040f03800f40c10007102c01900341c0e00500540040801d1000000f0003507480310018103000c411001040c1c10360911000344060710240d0740282840110664a10300b01748400000d02c260f01000c48000008075903441d050040d255407a540406054660b405d1068100000c00c4840512f07a2042403400100c00f9088982d0f8424800c103c0c2020000d8403a2104251002c14220440001c9840c2d1514284100080e04202924262900003c1c080921940b00c401641c1e0072000b2803026101d8480c0e07804e14216401e106a415040e25400c03482d00c05095845801e01c5601c40001e203008240c0700056420100403025416001d40050040e000c0510050703503140844c00301e074000308041610365000001c02500f8103219000302d4100510720010036000a20060045c00ca4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 466615512 1250 466614262 466614277
    0x20f010b090a110403050102280305010b030c0a02010f0911030f070f1502070815011401051315030605180108010c1b0609020f090702151f05040e010912050403021503010605 76
    0x143d940c1c65440e00c00c0000f40251005194440001c43d40c40c2c1000100c00c01c0703070f4070001c7c907184101001c00301c100e4071a00c80d000303160485c1c0494924a055440343c550903d16508551503d80440d9640d80310102e00386031038003032100c0c80f5004054114901001c141498144811a9045285030344110010000904461950703400c5401200c0559100300c080d000032828100a40d110600500ca461111000c0840c03100c0d61070b04903400b10f040440ba00920800644c0d29026000800003002594841081824080c41e801900c2d0102454000360700380d02d030f4001070040002c92410029104c00e1600500c0a07d1092290030716030f03d1142080312440b20100b407001a03030740c00c8a1004003104e8131074016200f117460301c03041d40e0b8610303c004140d2081c52401900080d40c0e0b40003050756005120340c00d00480c0c11200409110398186450780da03891007c508003800c0c40050000160034200365903a6110103004a444020700344d000d03440a649290392140740d401080140841000c034484042020001000110b41100850303408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 466616762 1250 466615512 466615531
    0x150b03040602070305070206371d0a080a030c11040908041a070b0a0e0c190e1308030106120507020c090a18151d0d080705070c0f06030606020f010b09 66
    0x168141131030308484500031138600039040440890305159000004038080120440078254404609201b04c1c4c409105403407054403400b0039440d02c89105012650107444075660009481c9980107540c41075051b1401030708507009d80008011109410811601180b1945c9201c8222030a100040244d181d0140e1445240f1035844035a620078492410180e401043d14241500000c44801ca0724100f00c140000c0d20700c2c0076100c0c007240250b003c240c20501d0640041d60400680f01685600541416100000c4410180c02503035185520603914000540c00e0000350f02a02269444280c0360610840c81001c0c0d44010740f202055410042508140f80c4030040c0c150f0380203d41d05e00c0801d1414500700b001c0c03500d581a0102400890400c41c85000601c000c1e00000d6003a081004080945e62040400c161104010100d5000250000e400304810310320641c0a001d0f11070251880c0608260303035803a480c0c11114a580000d01082d1a01c1d020001e05405014007510070300e680009001d48414000007421000000b13194410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 466618012 1250 466616762 466616767
    0xa06050618071211040b0702090f0c09060d0608030c030c120304050a0b131502041814181e01090b06040c021f0f2417030706020319050f0901150b03040602 68
    0x220940c59404c86002c942043d69120f507155220840c00c1055442614164000c036000d8003c40c0350120601c01a0340310700d448610050408ca0150100300e5958401610440800e44070f20b4007280410301400200105c04250000303503929181610282e050441032510850041c40900800000c50004110781101c0340e802100704115680f17401c6203080664840001500b05100c0201003010b515103580240151000590481820b00a031803102007544d64408252810590100108007010111240307280309005000980d82c40142c40d11039140954000c40c0c180780141c0d1a4030100702030040780480541c0040066800b40420305035490080d60b18031050031990011200400a01c5c6404801e034407101c7e9000c28100244600c1c1a41420b2030511a0501021806004584000503152582d4040209541c044a0103541050b020b0f880380f44c001e401c01020517900c100729041c190459551881510b1140c240d40192410a00b400c6203940e086661042030042c040300101002d04c504244403040e00e610942c841009607 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 466619262 1250 466618012 466618037
    0x60d02041d041223031303090b0a050910050f070f0c0605180915030f0c040f020910030504020103140109052707180f0213090b09010506041e170a0605061807 69
    0xa462600120510f03842030350110502c00440240caa41d144418048d0351848045502c034001c600395403080c00c20000100e2020060968a82070000b000c2003e02c0850401d1400e1200d66600d0a0322640110400c507040c12010321501e080042500400c0090a06460118103094034902c100c1e40e40d091103a1501d1283c0d040d40b0001e812070280010a0034001c1c405002d0b100c100004000643d941c01c03e0500b13080c071135030515096410411480c400e594180c03000504001e0754003a10b4000754010980035009a0402d600c80c259a00071094944d1164001d090400d4000381514100401c00c10316500c00000d0312661040c18844001c1c0380700000c00206644c460b03944201c109040e9105407005180c542c50703911400c2d002040a0314000300a00c840740132249a01d00902820b0040020009500401d008030b40e40b111080c4000d1242c2c4883d6040d6103401c0b40b540c9116101e1320317180c48014032a5442041d102c00c055100b5a8a241000340038007800e40c11030403d0350b080c080c42001260581542c03000509510401c4005142203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 466620512 1250 466619262 466619297
    0xb0306040618140c09060a1124010503101b051c1a011103070312111210050f040603051c09030b01060210230c09010905060d02041d0412 60
    0x740c001d1611500101a1848449101c0d010f04180c140503d0b41140d2034001030f02c1d44e05260308403104688000d08a5181a014440030784040c59420304040c018820b540d082c0e100c4c225034000490b00003080f29483d800940c03401c0c01b058035083d042111020228248440c19424031034900c0301c00c2510103e820300c1d82e15842c21041d80007455601564403030042d400e2121f4542346980c4800d841048150070703138954a6401800031810740d00e10414200030001403030049407106d503031001d5000c0d00d44030f0280f0444602d4400340d1411031001050582c0e42404a0700c02c503600f00221718100c1c84c00542880152810300c0514610344600d500c03001d45542c07061969600c45c10565182e8031031503011010715403041500080b075858840007540c442c0d10701d101c42e03080c0e0301d8000040886002c01c0901755200c580d4417002c4001d540e9030820b1011540010b203120703050084a41c0c01145a80e41c201c007500440e03482503001600d81d45000384506800c0c0e1520f00c00c01c10304004e501408045840d6031010049448182001c0e8940051401c50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 466621762 1250 466620512 466620521
    0x62103041d160c060b0609040f050109060e041a04030c321207170f0a0207030303140f06010f020709060801020304020f0f0a03030518100c05070f0b0d051008030c03310b030604 77
    0x1f120f44c0701d8500400c0031820040307540481d050b81c40d0807074200700464851507044a80c00041e5000b800c0c0c2044d6100802c6041c1041940c7c40d0710a1081c5095440b62409542e0581c2e10041031620703104a005400034038010024603550240100c48150051540c01000a45440b051103104806000c0c0d000b04611141d015400c401241e400c40d00903120230b6030b21710042400079100c0302d032400110002030a181102c21044c07100c440c4580952960030b080001030f201d40307005540c0462500180c10a40c041c08100140b07900391886035000a00880e4000b6a4a150520403c4903840203e61040e05c2024458450a880e4a0712400030301520751500380541e840c05c1e01c1e24041c43c0e1407000d86c10302d43d10a00340c9030082000c0340e101500880d02da214a0454a1041c0c4035240e044015500380180300d0502c03410300802c0340000c0227803c01500300040e20084406980c856500c103066502140302040644d100242d070202e8031400380c0c4e520395118840541c03442403440310101e015441c4243c3c8500700c000d00011000c50700940c1c49500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 466623012 1250 466621762 466621777
    0x320c07050304031a0a05040c05010e010c05060723030c09120307050307030c0b13020f10050919030210030e0712240e100e0303062103041d160c060b06 66
    0x100e030384842e501d02e400c00040e9030000304201c901484c003001c00c0c00e508190181502943e4410035041055040400449480203201d21040c1005880c041040105000f80800741c05030251b036454481141d20404078003690403044003011040b080070010080b60b11405c0084d102000c0c02181c80007003043d90030040503e18001d5100103005070200051590800d0341081400785400d00c00c045e5444c0c0c031303950702c04214010300d40e80c0c0c4041c2d000411180210050314041341002c0c1454103604190b418149108082146a03013841d2103088200589a01030042d03160543c810303071140d08207281c01c0c85400864844075071910601d00ca4811603c50300c40301c070fa040102c500700c0c404d60801c4243c84910203c00500c0b4000140c40580040015806210000904807200d0701031000c106141c0c5004524507101c0805011003000c0b160326100e00400708128044441c1e0041c4011310040c4491a0700300f005030b1100031620b044840160617460a131a85d01e410b42c0d007141e0000b00408c0102d80020b80054030101410100300d1728030a50343c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 466624262 1250 466623012 466623023
    0x312060111211317070308131205071a0a0912060906020a030b040606140301260307031e080f0f4b0f0a02131703030703320c07 56
    0x40b44903441c080c000050046542c8807101c0100d0305a0300d4031081e584400009241c845500001003e101040b908402402c5404688035200c2d031650b40e86046081c074008041d01104d070b98100ca0020001401d001d00c009404541c0320a4807480c1420001c400303032003c3c13068170074001e02100341303800c00007030055950000b900e454010704250760760802590010010a0780b048a13510403440c1903404500284030700070712140c2040c2150300914590a0000b080005504580c810f500f10b00a01043c0d42220810300141080318400d403140111080c10864003800a00e2075466507041290000c101700d4408440d0048a0300421849641402905d40234010484816522661608442144015000380381c030f41001011a100701050155405180c00c0c0b8224885c00644480b0440b140700310215611031401d900401c40d01ca070700d4104c0380701c2d00d580303451007540401d604078003550302d410200c20845940e406002d4605001e14400303820141841510740880c0608081c040b030080724007000e0006155200802c110303101e0360307080f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 466625512 1250 466624262 466624303
    0x10c060203071808060915180d12061d01140310050903040602100212160909110306040c1e0c0201110609030a0f0f09060507061d1606020312060111 65
    0x111400307400300c01d03070f4010241154111100000c40c0c03640494214000c06d80740300981810780848109951824000e400f5440f82a624010028018000c02c28000000425120b1640d5034003800c620104070383c56540300103091619201c24000405140407010b05403a44981c905400b54003000101c0d18004c0c890585018081c6032409016030098008060821038107140d0840d0b0750ba184800e20081039000b0b0710041c42400307014001180141d10082c50400301401d00349400344074213076104403800c141c0d41013070400550b2440010604c155170502c0c1c003135050340350303c2c030304244446a205014203280442e1108a250411680c6207110046a20480480b54011048011a000c4d0708140700203c1d100d5000008441c0401c001c03006c1801c070540a1032100d01c032a080703602c910481d031b450544281e482c0d6010040c202c0301c2e165074082c0c1d003103e0004040220040301c01c40004203c4206103403484c0c04941d8040e0086015540140b0444059a184a003000e600603801e10b809540c6c2041c84641c10301c0c00500844141851502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 466626762 1250 466625512 466625521
    0x20c100c0c030c210f11030a0b0c0a090b0a0f0509030309030312101d190b061306030b0d02150f070506070e0102150c0d0b1f02010e010606030e1b010c060203 69
    0x10010200c0941c3c10007007154502515000aa0316050316091004240f2103050717000c82d0105a99613a403152491010b0151072095a1942c0d5003d03095004440b0751a00c1c0b5400f03e0740102607603100302d080c006010401e8800b0703d4440c442d40040d08205408004900704440001c580c42e03141c4050065800078500901100e484e01803241c0540c0304904102c03034141e59a802d0000000309805d03c1c990003842c402c040881d11342641c58105182d65090042040f100e50303280c80390001810340d202c4000a1440901c020213024009090a10090a40f60342a140c1442454081144005a52081c0c0d03c0701006800751016030395103009406400103401103160140a90244400b0050426005100b1040240c0d00341d0a0b1761011a8040900242540c244d5603401000001c0c0982d10b88002e4550000a0011004001410715440000d00f000e9040c0585040f400603519120344440c5081c1c00d01650024100e24241030101080420300030b0351740c40b683c80c024110040c04803d84086640116204000e517508002c0955907440d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 466628012 1250 466626762 466626773
    0xd0e070b040b070b1303081501030914030909010f0501090b162405070314061003060b0406090602010f0e1f060302060706020c0c01080c1602221b0e01020c100c0c03 72
    0x10803c0709843c080490000542240b0a0780d854048890303041d10368a00b42c2d00c075022076041d64074a4600b05418150740d101041c01044492030202e0703900b10018000d42e80c0310303d204d05100305444107910009070b101080b141408a0381c1c000440000b61031040401c0d944501c000c0d0115502000c0c2c0b4503014120b015440390b08140c56590f601103401c4965814001d0201b9152035000f101100c8081c0c0908000e05c8094001c600c1c01d00d0b04101c0004404100d180101c3c44c9922f0307405110540d80140e100c031001c41c0d1031802c104803883c0c0a010300000084100000c01c09246610880342c0c590340c503510100310480b4a42903841540480e54443c4c1d0140d80c015107160703152145442c00350002d40c0450301d0581c05202c1d051601a0640c1301d007207442d100d408044010f50070701090880f00c021054110f4422684226642c2c580c0310201030100c03409102a10850021490071074443c04c07403901b09204805641003040c50703c444030031641c000410380041a030030341e50a1250a04c61400300c035042d01d14a4001d01450800700c00005019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 466629262 1250 466628012 466628017
    0x1180602010903170c04030305090301020c01051503100905100903140f0901140304030c0b07050909040f030e060415050a0e1f030c03090b04020411090306010f180c050d0e070b040b 79
    0x80c40b82d140c140740070f00038a80e14a90130900300d9040240c05000c00003800040c0c0311b5070241c50030f5035014001508143c051804d060a4400488040404007060360383e2100629041004065400c0c040108000c0b00400b9114940c0f0f4001160001050a840710314107010144540b04128180c110390340e640741c40751444882c0618542c0000880750010f160162900000d00c000c0c82100d020300d9041d11041070b5031b05a17075034580700d1a17001841441448402e20810101d03840d401030303c1c3c0c404c610a109000d00005545406010729040c41511406902d0500080c00022042c25004290500741e0030200c0c1c541c005090121800000765119681100b04440382406151038070b14815403401d001e4406210110340d62070200d08a1320050300140001c42d1040c08030b405401c040d8041c001c2080014100c0e4581a40c039808a4600482a072024207020183e00f01003202200442c1c0f9204c4007990850240f00815412070010403c4c020000340c2072440380c2c0d80302202c2c4200001c00c0113070002e102c507454890300d0303941e2440c205a594 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 466630512 1250 466629262 466629281
    0x80405030f0f0714010816270f2702180d05060a0605060a020304090e1006080304030501050f07120b2107080105010b040510080705090306010f05032b0c020118060201 73
    0x6100380d01001c41c4104103005110494a410781d60b141e2207030380c2c152241d008076144801f54401e002200e2201001401c0c071885e00c800c2c00030555503014005242c8000c2030902011644500122021140764021583c800031005892000250016071203100213050003d4190071075155581c030840341da0030441040000302d14144240302403c41000160390300c10510245115828564006800c100300c103005e80c011a034061101c3c1d000c8801120945014005488203e40041d04100007036070001c10100f04004090041ca5030112812101021505041c0320142a1801521081c50f15070b407550401c0780d084d00c5485182c0100c0f450004002580350800308065110382c0d090040342d9065003801d0012a0f69250b4100311030844602a00201322105284070880d441c08024000707008202e0308004916003590b0030000c4130b019242401d4258a0146400e003010f01d80b019031030b400c480940100380758649aa541190b41c2606aa10382460f0310048018030049600840f45c00302049100495080841e802d64154080d0511 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 466631762 1250 466630512 466630543
    0x30303050a1401181112090309120703170a26071106190c091e0509060d0c060809030d05040b10080708030405131409010f0b0609011407080405030f 65
    0x8581095500040182c001d0280f0180600c5008404800c014543d204842036a403003030f051410115003900080580c0070507a0106000e034400328509074503207021380c40c0301c241b9031040009110307151a681c0d805d058240c48070ba403100c0301c44000c10340c1080140030342446008001100c0d2144800400d60052180445081c0d85071300c00030325403c1d20754801d0b090014040e4000c441600e805065958407010050141c03030030b0b0000f0010407010050020310b144d1035008202e5a0340e07a01c290600c081e41410144500e196000340040d1180b0310800f28007010507101c00e403007401c1d00ca49140c114003d5868200f450b2440c4940c503000310205180c40d081005200302012034a020314001042c00c01401c1d552200d443e41d60240e4000c1487c1500204820041460814105080380004020100e4440b80380e0294104200e0111655a526510381441c0b092034007080c402e078140c800f4122081070074484240c0c00209a40d0141c0d0b0a260325400000340e10b030031b01601105a0f0000c0000404540c031002250620588440c2c40c00c3c4170040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 466633012 1250 466631762 466631771
    0x150c06050106030e190c080d020604200d0f17040308070b0901110a1d09010803280e01050d140403090311060702010c02011b20180702030a0804140106030303050a 71
    0x3070141c401d00809000b43e8940d00104040142a0300c80940c1341003402088420b1014030303900040941d022300950850700340e40e070003410061500703052141ca12609a810785c0b0714000c7e000303801501075983d48106a001904285500e40c0e803030782454058070043d2003004440f4000d8010500200308607000c0000d0040d64032600f06a034041d03e50f0425107003030f1001c8424401004100f80007200e0300030300c01c4600d241c8803010b80101c4442641e008002c504114000e8000b521550400a0f0407a4001e91402821000440380e04603d07186c1113080310020052800200014100300e00040c19141d00000e5822005440708107107100040c03030a0074900030b0022240c43c481103410441018242005180c005c7c1907410160301a11140d410743c1c602d030300448641d0031003041d84080380c8100c01160081111400c01d50441d11a04580d5110a031b5031a0400c087c0000c1c003004450b460304503008120883c0c1e80030060b500344090740c0c00c1c01c580c20346981ca44200e251910070300404a0350300e0460000189541038001c0c034020901c4000400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 466634262 1250 466633012 466633019
    0x1819150605031b0312040f0e1308030c0711100822050f0a0510090b060405090f0709150806010f0b0a1202030a0203070305010e10030308062403071812060c09150c060501 74
    0x151140a00d1180100c006c0c030f0a1003c00965508e440041c0d400b02c0100e003034000080c02c2c1d6482142540003580c50940c240d4001c10500200021581c0403881c08000b00c98220301c0200a4100500d01c840080101c7c440e80b400c40084c0c9030320b0b18900c58640b4800e40c0203090359000c80541c200c0744d0356440c0d500b00603a007900c61001d4220040c410f500c20300704150713042800512907544450500010340000b501110b2907105400c00b07004845030a00c810b4000c3c00d54040049030000c6402880100709141d40c000b9034041d003044004202c3e840120f4102800c907041940313600d80311102107005035183e1030032440c002c140358000400c0008041607030b40118480c040648040015980742e407001e00004000700d503510414110380c0018000309014110030f5912840c010030320700100210300250324a29921043e01160680003000348244160446001e050403c10051140c1209180a0b07041341c88040d00000580300a942d88035043c1924801c0d480400078000341e07031040811540c56030004102d0425080d00fa9105032600d400070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 466635512 1250 466634262 466634293
    0x11b02130509012009060901090306180204051608041115071104060f060206271002190309030f0f051314040c09060c17160503031819150605031b03 65
    0x50071001c00c001130281055580004d1007040da20042080c2d0500c0216000000060401d001d07500c02407244202e20300c19010b0610601c415550044c4c0740c44648050360490824117540030040300e40c01780d0030660849614014001240d415001c580071989142d070000f4000c0280400c00960822108007075030104a40c5030382d00f0000280744604e0090200581000c0301003038001500e5407404142c06241686001004101c42c1600d113008984103054141a4000c282260198038002d03406070500d015040038000000c10350b900400000e100440c2405000c400300518410750f10480558540308003507041f0f0858917443d102102142c1030002d59041c4150b0400945964052040720000200d483c1d0b034458020b4442c031a6902c03501c2d025220340820603030a0038082e034603418224058400c100c0d40210302541d964201448080c00d07e030311041c86210f440d441280d0480c0c0e41500c0d803c80e070300e1003504503140c2a0f8a0303144145e444041c1949500166140c85103824500e481800c1019581e0134000490807a66891080e1000c3e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 466636762 1250 466635512 466635551
    0x8130602060c07080d0b0303040f030204050109020f0a05032d0906130b2404060311090109020c03040603091a0702030a11060907030215130311040f0b0d02011b0213050901 75
    0x10780b540880c00d0218100064a603000b618075102841c2021400820f42c0f00401d2950b0090750000d598a54510410003d505151007118050648003c003503140242d80c1402170902d10800c07800204005000002510700c814902030b01c420706c8101900b081694003041c0401c64120015110018030f8011103012481260844000c210302940c807484000c040d07a6406d4a880030303248001340740b04d8040d40c090152145955203114010141d0310a110b44044482094288000000140c0122424910400220f00c0c0d425001060b01c1c101c44040c80c001c00c40200e9450601d20b01102d0300221031100341c0708000d001c0c0d202d4020000c2e0030140403e60380c010703e001361200344d55601c01040d1200d0780c1d260030050040c0090304000d0315140b14442d1b4030054034500100c06500c1c4180c0c00c0b03183d0007075411112508217000c65282c18055490b598034150800e2051400340d600040241c042504000d06000302e900f12100c211460311000e40005400030492130f0a60580e5038242c01030802100c0540c01c95280c034106804840c0040c0c2d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 466638012 1250 466636762 466636771
    0xa050709030201082a0c0c01020a1709060706020712110a17030405070806070507020102070f08101d0307110a0e0103030504031205042601050a020a0e040b04020d090813060206 77
    0x8450084601e035400640b012003018040208251104c9031041c0c102c40e03c44010150f203800c0300760300b0360340d113000455041c141064505003504540241505501151540c6007840100d454034150b01d070f80c3c00d0240300040d000d1150304401403207a80046920010300078031120304192070780c0039100d1001d110314081901303440f500c19103402006410b9980081c2c0e0b00400c5400603640c0144a501110115a1100041c62034500c088882c132000441c001180310440d6814056540202010003100c0c1c0d6403400e00b09407d49402c2484c5c0510305003550b442e9510000f000d11101c48143c04138050540b565070b1044d04181e400c91103207580392409141c0001c0d0020301c64441d4154075040b41e8055070384906290a55448541002010512004114050002150342828810340141c00c42c1c40b1071601d010000704a4505007511401007040081d02e1060014441c1c060700030301c911140ca80111000500d02030107000060003802100c02a00711103251500a104102c0100002e06207083e03c4449804400d0759000708aa6900040381c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 466639262 1250 466638012 466638017
    0x6050904270803040501020d1b020705010c0c170c12031b1603020111010b0405071e020c0f011112030c030103140d020d03020a021f060f09061229090706080a0507 71
    0x408881c003150105000d540c210f0710600004d468107072a101480d0944009020b401029400b10550a5800c0e80412044000703080a0a0030f84c2c055030a92511900184144a51141080c480010b10101e00b001c0c00035000000004003045105d0324642100c583d29002090058003000c441036084c0414000011101c8211510310348681c040c034250742c0115a1f03803080c0e24481c0710664941005402568450051070320507a80e075a1102c0c9603440381c00b0558800301e4030041c074605641000001146544549071901c04d114020708180d082d00c0b8000011a00e000c0e00541c4114640001000344004951460020350480740180344025020070841440d0352031f00001e884200143c0e01910082501e14060340160940207154016101071411124141715007050301e1182644450751218140300306203601c1070100c050801c121080180d503080000040e8116850752000e4200d24400840301c400603000b0341000c09020500d01c0500c42800d007591090b41c2c0b0f0f80a40a0400455004400a54100c61901c00c091040195030f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 466640512 1250 466639262 466639331
    0x16090905030306010c0305040e090c010f080417090d051009051608030a1b0506070c0203370813060f03060b0702010e09070201020c12220f060305070c060606050904 72
    0x203c0196200506543c088081c0502440001504040003162510403041200507021108000c00010304042c4052440001d010040040c040491582c40c0025255030a450415580340c1092000801040c0c80e050020694400e0b401420840311080c0c200100b404c0c854422030b1540c45041c0130000c101002405a00001d900c1800f202e0105441015905004e58076641c0b54134281020762180c50406004650407000314107058032030b40440c10200123041c66003c0c1c039048021160700b1415995141d0140c50090702d9030b040102c0204060212001c1102c160038881241000700c01e44d90724002e00541000403402000c43e00d03100c0001103d40c0244100d07a59658140c3d41e5404002442003000355004002d41140c007159402c1c02100d181c0f072420001024045580072029481301040d580c02030708006000c00b255036a402c010300c1000010100b0384800c0c02d0f0b440d01d003008941581c401c40c081391085020100601580c1c00c000d07001070101c1e0003c000306002d00c400e0754103000d05451810000d001c4401e40c080c48500300c1c00f2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 466641762 1250 466640512 466640521
    0x40203030f04140f0121020901120e06071206052805030703030f03050f010e04060216150e120405010e010c1106031008011805030a120902090406060501080a090209040f081209160909050303 83
    0x50361f00500c1401814107081c030b01203081784000c4e0100c4000d292a210a903101c54240100aa04159080e586a4810200344030703160505c0003007680315001c41810b0035880e10060174100101c2000c61321001500340501100d4a555481c14014910000c0c2e800d60000b103881e1902044440c40400c0c40d190581d01d00c4d14007011780d910355550b07010003580700c4d0030003040c6010111440c0300004c0d0000c07905500e03500c2c0c0c0c0b0004206d05203155034440c20800b2143c40044883c402708000c00080c1d800035054079060b402404d080d15010319506080d580d4007880300207168000c0d070002c2000881e000691410f404e44101000170040c414000020130115845040d020701507520900c10644401d101e40e84030f5000000141c008a441d102d1540440d101400c00d880c01c90ba01c40c0c8441d07041c016940d004141c44e9011009030801e01c0b0403c059008182c60b410b018002400e0403940501c0301c070610141c0d00461f03648406d142220b6049140c0100a07030340300c0a42c0d0395007a5070b51445207000280801c00d80964510300703410001441c03070768a5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 466643012 1250 466641762 466641827
    0x170705070e040218091f1803032a0206160201090b061207050901090c11030f09040921020604060c0908070e0603120c010606090603090f0209040203030f04140f01 71
    0x3008200304c0c0d100c0c0c030914881c4100c10700f0b00d00d014001d0104c48000c1c40e00000041d042c843c0c50214001c5050054a044d140d64041811251120358254042c1400503000c800820404400d80e0b151446901c1804040900b4403119030005407688030702110504094801483c0e80c0c01c0382600d510510117084daa280b030700490102d15001418952031030070030f802c640352143c2d50000725220850991041c940d142d83c0300310140005402c2a01a540c4d2442d19005d10300d8030f26686044061b901640415a0240340c0ea0f4110204000741c80d150411201c0e503111036610440c00c4030000a42d0b0303c03002c0310119200c500301003080001d00c1c02408288162b903066000780220300d0074040c26a01e0340c50014002c80e814445e07013518000e00311f1074600820f11882c5000000c070340e40d402c140e0301410384011075000c002010700c1c2c21503010228440b05148a00c4503812504c18140382c4483c00024614042c2d25841d4450f8040040d0000e03035503004440c8040c1900081d148800105042070055610120782065030000d036502c540280340010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 466644262 1250 466643012 466643039
    0xb0a08072d020610060f020303150a0b0f0d0c09080a0b090c09091501050603060114070303110d0c11060402060301060c030903120f11011e0b010905150717070507 71
    0x11042000340d0039414104088001446200d14002603040f00e828000034059841040c0b000d0822400c0100c402c10a600e002541c03880020907902d204100e00c09180c146940d00d80302ca8000b8a1020281905d0314400f50102c4019401180c242d1100340c5003000304e401160051a00308115031005011b40343e0a440c039100c40081040051248000b4010031800c186036683d01600303140540c54080051034034008207800385c202c1c840e040e00310714420b030014030400502c0d03a4808515904041c1042280c3d44600d02498244c01401c5c00500020810b0008902d6120007201e0798821041c184d20350356000c920000350003042e80ca0351826038009e900584104014003916024801c41402c45201c0e05e40f11031465680c0d160810303614040d1801c00c0020b070921405000143c0c1c881d17510a07504070350030001c1255000c00113a0245580e400040f004d4241d84a08036070702d042c1e0050006030001c1c000504910005d000090345260f0682c0182c0041f01c00401800340440041d08050589808990140003040103504040316108001e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 466645512 1250 466644262 466644287
    0x1140c03070506040602070b07030504080708280f02190b130212030a0c0605010b0c0619020915070201091d0f150402130f08010c0203090f030f0604050d03060b0a0807 73
    0x180310070018400002c01c2044203e2003507002d05001030700c82115160400a4100c0904010205410704c410711000c607500301c4c21180b107180c2c01501d05607503644640b441210714102400100407864804e00101e411a0031151002030801c990303095402e0601013403002e0300b60b541c40200c060032500022001480c500c600c114000b61680c00140780c1c0d005074a0501015245031311070040e29002030700135070100f4204000e50040902400c5600fa00e0344c1007100085510780d0710303003008241d0030030f000c2c4004421b1101105a8100c428485001d4200fa00c0301c01c201c1e050a03182e600000040740080c0c0d494100040100c90781c00d521581207015855605103450300240c1841102c40a00701d801c12508601380d010481c1d031580300510f00c04601c0040500c0031454a407168a400c0c1c5158400d101c1e50341000d100960039039002c4100c0e000303250110b034250078101003030010a1504d0403024174050988161028003040c03000020b100c008030b080c2c55805111640c2c0b50740d42c0a000b03001c0c401402e400300f011180401c024600507004013660 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 466646762 1250 466645512 466645537
    0xa09180b090109060819020306061e06041205070b040b07110f0a1203030b01030e070608091c1d0f0a06210617061501020a17040f060806100e0114 64
    0x12845030200149510400381e105000c00c0782d9910341000010310a010b81201c102042d200ca480816060f00802e0321007000412061094044002c0b5085400d480e01102880c50320181c0010f490b180c03104400e06107084140760a5900d0308c2a4200000d1b00c00390b4100b114140c4078240e01550400e00c0c0741c0d461920384400d400007107902800b00b150000b1f0170b407202c1d200040140348115148000c0c000c1c500700a400c940049690504260a000c2d2441a0b404000303030b060704035249803810845c0c587d80c60090904000211546101940c0c41d41c1510266540c0076400e02640a80f080d10b41041c842c20404001000d154010f409070810f40403481048801c4c0640d562000761840781201c46a5a40340405070380480e02d0035005801d6002e04400810f4511104011f030703581c010005021080500f556a00103590b1341c6c0c0103940100804030704a8007118460002043e40d004142c800751034110541c07174480140030769100700e0385103000724079a0b050340303014511904040d07c0d0103c045e1940d40c030380c02000354122400c0d03100b807440060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 466648012 1250 466646762 466646771
    0x1101110a0c060b030a081215060301051002031e03010e010807060801211403040801060906051c03050c06151f120507090b070c090e0a0506071209061a090c0a0918 71
    0x80f191400d02407228420700c00e020840e03840000c1c541d51041941c000e82940c80e1003d500300b9010386500c030f48003103038155032045800c000c03504001d0908a00d1841500c3c43e52146a000300010340203003144501030342c140c40403640c0c1520144e8840500950343c4130310b4415070000852502c01000105001c00c81400120b0a0000703041d5211903580b240f80d500b801044600d100340e0300020b020040c4002c00c3c416400500030900050050703902d8400094440d9a002c00c10151041c0d402c51104100f41c010001c0351102c102c1c41e829201c1a15041031024404805046603030f004041d1040d00440940d0150080010100f040e02d03107209540b01c054845005003002070031402030012100000c140211948040c000c0c0d5440380a030300c1405420302d40706205a510780381888800350f2114500c48005038001c07464503840511440d010b0450355a050841c00079004121b4054011031a2441044401c0c0000380321140041058990410a45030607540e54880c1c422007000c4070001e00b002c00180070514610501e0101146083d00109 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 466649262 1250 466648012 466648031
    0x50a080411010c0f0b010e10060509040b0301180606051005190e061c0203061201150605030a150e060306070e0a120204020d0c020307061404030807110703060c0c031101110a0c06 78
    0x1000d1070350202c4c007a190a4107070001000481c80325103040307a0050700a0408034440307150680c050902d004119203070748115198014194180c801b503025080400a24a4500011400c0c0c1080001007903940101d600801c003019092003064000c0c012a904059003007640400515100d0003181e03103417001e82c032003980f0000070040351503090f2a01107540e0180d0800c041c0166281000c070300700003030b102001c00c0941709a410b015048402d089400c2460741168840d007003444da01d81d140010720f00140114020f00f140c2e1a411903000c15441d0b603030a55a48601d0007a02110803680354100300f914418103130b010341d5602000903441801000000c1210380100361000e0409424112540b0b01c08081d128690203210041c3d00100f08032040c00005d0254802500300d0350b104141c5401c6c151801003c0d070000400010070301803400c81070403c0080c200030030001182c2001c41003040c46c0544000501c061140c21040d00004d20360a090255088180f00307010b460140c607101c0c20b1422078408025200f81c000d0020550342c0e5645d405004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 466650512 1250 466649262 466649273
    0xe040b010801050f011e050a09050a08070b030a0e03040b30150d05030c0d0210060f050907050c0106290f07020d0203160605190806090a2f04030c0501050a080411010c 73
    0xc403500c90181c0b00d494070340100c28030080c0303071427980e9104d5031041d180b5000401480101080102c06c0d111600d03072280c1c2c0da64511814802800c0c400c0040308251100240000300d01d0f0007403028022446332085411501816164a00d1144048152071400c1624000104a0180c502401e0819481c409464124805003541b070300c900f180c02902d4041010b80142d03e11903507040e03050224650b0b003c400ca000b00500d9080070505060340e003540c0103540c003800036100810380082c01081aa803c00d4080b1000384036003503ca001040c422016402070340380100c2224880038110580a064407690502c58545900b0814686c0800440c001461700070f030f13014055070001c00361404071428090084c00c01c82d10703940c4da5940c0d20000c1c0c1d40c4041401100390708000c07646007400541d030b4a04120300d400645c8aa230102e4030610701c1602c0c00780d0700302c072594446081c8040044800310804007800b074421a405142404045a0381c1c0c801590380c2d11503041141d00082c0220300290010b100c1c80e5820245c2001071510300020003080c0d454 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 466651762 1250 466650512 466650557
    0xa02041809211b05061b0a0c0303151205010b010e01140f0a0c0210030504050c0405060306040b100b181503040b0f091501030f060b01090513020f0f0304120e040b010801050f01 77
    0x10350b010781048041003006d49807210421124002a58102d1509000840051484103401070040401d40c403110040d2031081181c14030b001a1801c550000c2000c0064070344039000301030225659022501e00580144190f0094004118a14411000515000d0b40011031203480d480311903000140300c040036040000d600c07a110a0740c07a0780070030740f40090340c0d05190402d50300d081030b06500c1620890502c0f0800807a41c601241076030704107070300c070000800d261102d491045803c04140c100640c110404580001014044a55190b4811003a200c032920041c2200400c510b41c84202e802034198022040406c481000380d40c89183c1c044140c0003a00e21400c0c00c0768581d2072401e000c0e4002c2d2000e40e224503164090060501c80c440c840b10090800e0314400385420086059a21400b00b121601c0e90b0210304803c00d0840c0400310345498203000d503175aa0702d181514001c2d400e0400e14003c2400036504d60410340003800e0070f100301c40b84044141c40e440d605a1800007001207480001d00d5050400002c0c0320455143c00c24400c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 466653012 1250 466651762 466651817
    0x711090c07140316030f1416112d09090601031106031b0d050a0b040c080604150504050c1e0f1819030b061201050103080906210a0204180921 62
    0x32039800002c01010001c2084210000ba1f40070a10204050702c0b000d000c5145100105070300c1100810003c5141000078815868141300e641200074000701000540c81d0440c20840e154411110780145032a12820259245800d00004100d1540c04410100b28600840610307480b861314803010300904903c0f404a60a03420000910741030703948402c280040c0300e2031801100a0484240c0c0e0400c500880c404004104810103040107020781e0303403210300006441c02090f528000e89406070060229003080d6103546815404ac0c040c2c1203101d1010015040c50240100441c0c213641060300c0214105800b61042040c401100c070012544007840300e007000d4030f21082a020400075400b659500445161240911055a07400704220640380d00d00700040c000220760a003030314401e078402d44806494208400310101039982c02011307103582c900b684041080151041c0c0051059aa080465800b000715142c038404c00e9900c5104000d00080c00600700e0044420b1080d02481c460b051460890041e00070994140880d0000d82c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 466654262 1250 466653012 466653017
    0x3090706180f09060f061d21060408180901080c0f0109080f070501030e0a0308190b06070b150d02010807030c020c04020a0e0a050607080318150703020711090c0714031603 75
    0x300204400e201c0c405c0500000c01440c02c011000d12034a001c440c0c612240b9401c4580304116401b4030319030401954524079003058000c0210703640383c102801c000300503801000d00240d06042d038086001282c14520300c458120b030303040c0e1300621009042c9010002860030f9080780c40e0403c100000c00007030f81c08080008081c112042000790566034141800102500c2041d031860b40d0716801649000c00095000c540302d944400b4103107800d5041c40d0341000700030141c242d00313040660058001c600d003414060440304540c040d080c04e45d881e10313482d000341d41445405c84809101038040354050001880c4a80250070000c0e11502c1c0c1c1c81542d08130040800090203d800240d100000240c1c80e01c0003039000e061200104000d030004485080c00c2c0211681c610031079100040034480000110100402410000c005404056040d400e20031020310f000b080c001c00a401c07a2a0996038001084106d1010342045103c0c0b070700444100c0c0034245007411607102c5e15442d0700746000749605844100104150340c05003802411146210b035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 466655512 1250 466654262 466654271
    0x2040501060e2407080a080612062a07050105090d17070f0f020717030417161a07020406090504124107060c1706030715020a060f0f0c0503090706180f09 67
    0x11024400582c1000302c018040754056410b216007001a1108400031184010003140000e462f6030b6510070b180190b0f8401003081d801c141c18041240000701d1003690340001690b44071000c2603480109201a1800d50300000843d000b02404080248925243c002c0c8502c0e9004a40f0a259228034103080c0010702412003034140c101040c10700036040800c0008080c844a10300800c0740030403008802e0140a111701c00e0580c01c803a20041000212241d0b801c3d07a0001d5002403042040c1692201c4c42e5001d41001c035022601601d42e2404090014050f41c81484111100b400880e50a1400360b42035107000010480360304240810000c005491008070001d0500310700c207403004500a20b81c0c540c060010b00b0302c1c40c02020910345000410200d0b40300011030000300d85001d00401c0b4040460300050341803ca59003c058100344c24001511242482e58121070384140c0910310400455030000d008440f6408140c500010300e41011001700300c1c0e00d10400545504504003000ba01c09a82d450704010664201c40d444000b820781c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 466656762 1250 466655512 466655521
    0x301060f030203101215060905010303030e0a0302060c031806010b07020108160507171b0a050d031505040209040204081f0c0e0306190b03070e0402040501060e2407080a08 75
    0x2000466200c60506065041d42040180c0c8240e10185006400e40820486269020b00803440d40700e0040c000c000c1000c1000d02d4444c000313100540b40900040e00801d003410503411442e400001c11a0000342c01d0780c040d0400b40c071801107034802c2e980b0241c0780450141c40f1038119200b03c43c09010003402800d80a03c142d0f45c49244d803001608e003034401001c410440d48101f01520b0110f4100e411100400d9100a4007000340124140c194042d0091001c10f550810540103605484a4002841000903000d0380c2150f000072441207003101900d200c20030000101c3d424407010042801c058001d4007040000800c05410301351944582450014500c50039284a42a0465540c2030041c0388100c0d4070300005032170064100703503100300400c0c2d4500700030f00742e44007440760180c82d61200c11081d8001d8448c81030080965403130956507501104540001c2c1c1d030a070310841c40e01000046440c0529140c408650002d071048078400c5031210b00441c40c9152030500f100c440c4c02001880009015480201441a915110381503a03052 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 466658012 1250 466656762 466656767
    0x9020a0515040e062205060102011b020f2a040f02041d16030605010e06091203132310050c030702150304060e01051017030c0d020106050913030504051c02090408030106 74
    0xb019180501985c2d0803c4440a000e406821900001c1030f50500881c040c1c85040040f4014403510f103840c0c4801c01ca03040002d0005502181091800e1580c20440f4174103030401c20b1000c0d00c003001c010741c040081300f47d200e01d400d00e0070726801c44c0c240c8140c0d0440c01030500ba40c2e042468001c900b8001c54848402558003003106c4202000d954080c03498052034100318650030200040c05011801d0140ca00c0303030201013040ca020343d9441d0454280e424450382581e4440c403490064101800d03140c050b4019a5a00500350340da2a0b40303400071402c1a80004245881a400742c840c103071407582c0007001200309130004000b030f40b0140c0c42308100e0041414031402c1c075a0343c1c1e15041c01c10304200c81000c6820302d1141d048c2700600c9100c1c85180d40f0001a5003030340c8044112865040003192452240764040c1c074580c02000d0300450f0664040d48a85c045500c03d41e04502d003591400c43c0f0303400c18007008030014040303401070005018500b404041c14611411014100f615845203030006401040c04883c00c031440c28001005200c400d6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 466659262 1250 466658012 466658039
    0x21061f061b020d02041d0c0120070e040c0b040807050a090504150f0f1505090f0f071805031005090c0a0b030609070c140601060207050a0e0a09020a051504 68
    0x900362404980030600010004803052524030060701c504043e054050545d5569803021406414813070164400c0c0b281c804200f80c5030101c2420f0355001c01c84c4285101103800f2813441131000a00b940c0080e0002030309000c40740c0c4010b040a4410303151a4406800420b0040060000340042d204010080c40c41c00c0c5410204584050ba075004410311601b40810301c000101c4240015202e83c01e0004c000c0b48018042d070780031004110051105e5003060401003002c0c80394000e40114000c3d2842590180055900e80581500520050f21a6110f001666002404203071181c07a0070113a014034075100310b12982d50358002a25000c0c0c0d0380880119155140c1c240003180d02c08100a8619640c2503030340101091a040f0030b4000c41c04010042802000d0220008082c240700d0744c0380d1031040b03620030070310103804481505c815901d0303800b40030301c0340544140c100218261800008650480e0b41019101c0030b556540701c2c10002408007a04200c0c3c1201410101013042d5076103401d50b40c082d1062002c0341d520b492070305c82c00c80e0344070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 466660512 1250 466659262 466659269
    0x403020c150c010501090c050d240611010e190303050a090f030f080a0b060f0904090618030801050301091e030c0203010c120b04020c0616110304060801080d0e0f21061f 74
    0x4e0b2400e6030074101d59800c401949c020105000c80041c00303040071081c056070180803d01c00c000f0040500404940c841d00000c80c082d801c51007400803c087c143c1c00c182103541d10444c00032031200c2110112070f01c0020b84240c03c0664030035000070010440d110243d480c8200903812100490100360f81e01811800c055119030300d503900a00f442c6040c0104040303500407074110f124440c0c001200030700000b5910b2090329290440384c40e031503000c4402c000c411000c5801c255021a0941d0460000da942000080c1528050180031500d90b0030100d5040307484d40100b040718020650070022014040d00c80d69110150764280328001e010b0040391100300c2c48904071149002220702602c040e0f4485c41c4140600706852100003040c0740c3c007445c031740c15204640b448150241c0d0b0b0803c400e0740c1d949007840006000700f00264850314041c101d4040c1c4c01101d1980c42a00815100c40c00f11411035a0811400220844640707040340890650349007641035004024003803003145090803421154803c0c0c1405c404480c1c10803404400000004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 466661762 1250 466660512 466660529
    0x2010b01090311040c030b190501091401090b0c2401050103060e0c030f06060c0a03030b0406090e0a080912031206120615010f1704050106090e03130b030403020c150c010501 76
    0x1107402c50783c441d06501c03c004842401682c1e580060001c0b680179500001128100030801c5182c6110389024640d408164095180003580b4500000760b0403c81c018403465040c016121000c0b401c0c20501c41002c25003001e003108895110f80ac0c94503101000d4012480c14002402c0186501c3c1e43c10300c800941550344540c054102400301000700207032010200c0c160398010060103044052901c0d45400100c181c001c05107010300c10b000364a60b1004050305503104a0a142c006e86091050965500b6510101d130800d16421803680c01407500d1a001408040041c800c40800800760844902400c07200e0b85181c00c480150750382c12400b50107004e40e5260619640700403d0200c4002c025903d000522181d201003079290341414031114180d40c818641c001c003030001ca03040d41a400c40c0660310b010b0134030601034009445064552403902d5502980070f103022040307a40b03181d0007000c41c150807441c0104240c0e06620052060302180507109051407540e40d00f5060900c0c824072103c9c0140c4030301d2040401421501c042c0d110010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 466663012 1250 466661762 466661777
    0x9061003080f1326120a050711060d0e06010504110702010915051603050d0515010203070201120902040204030510230103140f030313060609060605160503190f02010b01 74
    0x12003070422100c0416804411907191401c0c2c0b4282c001a0f0015048000c440340e40328041802903041481524800441c482115240100003100345018800d940406001580030407805000c102101038034138549802400d06031030b10031061000000c03503e42c4903c1e081c568001c1d1004211910b0b06016184c400a0700d00c81c0b4034a05005035002800c510036030303c6030080204541402c141694040c2c800e0b01d01d140c50005d40d41c22250000d1030b0003020780c0d01408006015910b00004500401085030102802d2501a0000d51a1202c00d07001902d040c141c80c9017a1401c01d4030707811494011389407400604000c6105800400500030400300c013406403219540742900f400001c005c10303039040d0540441a0304686d04885ca998a881c1c7c1f10780101c0c180305032103945071420320001051015000c00c42d40810016030085504100305a00c0e09180c1003a90002d01c500400228148080783c04103000c5040084403034410411a883c0408064139150b0003114082c120011807500404881403175028016074081d101d007464040f2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 466664262 1250 466663012 466663019
    0xf061b0607120e070f0e0c0d1a011704050304092406020c031005100932060120070b03101d04020a050910140f0a0f0302101103070821040b090610 64
    0x13007262021b4807810b20041a82008a100307245110103c1d80c1100700341509200740c54102404912510041120500180c1c002c810700035040945503205000d42c1d84030019518040c40c0c128600c0c054145140400810200030010344151954001d2100040107550040c1019000500801d42803018580704c8595050a000c104101c002c801040b6900351080664005500c5000c4210b65030310743d0760501c80c00c0303040342903038120702c152010305500a22602090307980c40601812078a0000c0d403a13040f100310362401d0384075030300600c550300c02038000d143c1c02201d9440e407490403a07540b01c0f5804030020440100042800020a000035030400100d01d40c050041500c400500c0e040030304041a0603240740c0b14031400381c0903044031b1151584d9110f0188030740800080c14242c4c000d0f00d41802841d01e001c1c2d0b00c422481080921800c1c0350180c01101c1070074450b50f081028600b00100d949481e0456801031003000c4082d00c3c481c240d8075400c401510294041d034000e24820105180240c0340610385907010b004120f20544554082 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 466665512 1250 466664262 466664279
    0x207030c120809061303050d050726070807062901050304030e19060806130b150739080102040b0702040f0e0f1510050f061b0607120e07 60
    0x80032201d112040600021840c20301a1060041c0800309038001c000103011060120b046801e2810780c1e0141f0140c0303104080c2850709079454480c5000040070008140014080f140406860b1744005287c0d14503c0d107070407016540c25569610503441100c803182e903103148201000035841c001c05200d07006140000c4c0e014036000040c21501004100600300311225541c01a0368650041d400350700c25178909240841d03034442c40047c14200040798094000c030210b0511031548101d0380551440c9070000b614848405120703104005280d03000c400700b981c251200c880388129801e0041080c10402007d035200000e10f44107560b002d90042819805000d40768014801400000e10800c02c42e00413a504840c00201038409a41003005440a4505081c5c1c074003458005d0001c84402284e49018940250403858913942da19801d003051000b18080c5079000054545480c4480c18803400404003043c0807820359524101190f8614039182c0d0455012000412100c0c40300001c50550045a800b40c640074003a1180d2803d18410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 466666762 1250 466665512 466665533
    0x30405010b0f0a1401030b0307081011070c120f150504050f0d020304050d1104060303031e0203190c0e090705090a240f0c0501090f110409171308030c060a0606020703 73
    0xd000c804d01d2103c0240c110f50f8081d900c011110800038003554801540c501c00c41d030700e0302410b10403c0384da0303420147d46183c0403014404803004035a0254544840780e007030440c071001100b0000340c1100c1c0b40403101496004a005070300745c110202d6407202c01143d180b84c40d00c0c0c40390910094a496582c0366000c0c02940b00c1040c2c0100a840a9400640b1280104440c5090200c2c0b1945e00c06421500286000b901005265144e04803c5051240c0c480b00c1c0441d42c1500d501e00102d02c0300702d07905015086114020180720000d40c10401e9a449540382060300300c58081e000489000c429507916002c10f0001920080901b040c40c4030034010104400c1400c000c0c00d55000d0210760010111002040024120441421034080c50101391a150414020005404c1e1460810000b4070010000c0e01c2d03918410f09002c00d00c1c5402e0141c0c800e01c96014100f0144034405072110150385e00050415000b00780c42c0140400c42c6c2004001805240d4401c400512460402ca445402218100e07000002150840070b0f0600100b008e04a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 466668012 1250 466666762 466666769
    0x60f020d171513020d0b1c061d030c0109021302160210050417010605031002090607020d11040e16080708031b0304090603060213080106060c020d020d0b0705030405010b0f0a 76
    0x12100e50301e698100b524003001c2c2070070510aa001c04800d07030420001c6416030240040184c040d6040144240d04010030030700720390001c00541500768203e11080000d00a400000c3c0b04840308500c4108906070034442410350f04448854082d076991084000203516203250a110301d00e083c1c00e000c40c0b0b815070b07100806007005031071a0043e0183e0344508085c040360f84624100c2e401040c148c0551020340000c0d142c8140605014400d80b1305c00d02c0b070210983c0d0908154801c640e2441c5009005516000180c0c0c280900000060403d980d90291a20703000f41d651174074001c003240c0b04007101c007030191030b0001d134000f030041200c035000811542e02500b014411810000704555000c0c0d00212a9071240d81d070855528510b109175000b40c1040f50500d4000000c108458010381203c40f04540b24403015510303100a5400c80b4000d22074800003900f1645c074000507041440f041c062150024041d10000b002e1620343e406114001c0c6e80d00701c0018000010030090000a1207615090401200c28940d003408010000d40020003500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 466669262 1250 466668012 466668047
    0x1030501211709030708210315040e121303061a030c130b030a080a17070801060e010311040e01050a060e0f0402030a1503120207060201060510080705041e060f020d 72
    0x1401c00b089034500c400e44400440040032510b115482d405901d4407224040c480c80100942c1e0700d0002011240901500e200365110026504e2124072402003001070700310000700c1d11f0207020707200a001d0069800d8000300740d00c8005148088000c0d02c0d6180000440385000f1307448101d08001084200c4680d404180d000d201d040c1141d81d458a81002c00c150700040c0190149181d0500c00c105504041000c3c4030301602d24880755413034901261005a20800e0a80c000301d54682c0020001c03001880303400c0c080c500c008070300c82041c94001b40100c5007505486282e0b0150304500401e1038190b004000d9031402200000203130003285411400c4200f00c0c8003281904101c07090040c40742c0d030044001030118509604c0390300940385030b220701000159a401d20703000744240030301c400c401400b03040008200240140203400890358050a410188001e080d0203d656080280c500400c1120030400041d0078240082c04503900c0c1d000d00f2076034030010701c3c220340604503041818000c010b40d00f041c00700703250310780d045130a408020040701d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 466670512 1250 466669262 466669283
    0x20106030b0403180e040308012321070902030f10080d0804080d110a030c080109150b030a0213180b0109031113180c08070f03050d030c0c17090103050121 68
    0x1c1094070300825a00014081511741d410007081c160b021000038101c4942c11004106004206090410101440d00340c5070403612903030035005c450032441603040d46031400105550805880b145c002c0c06270f0348160f680445480003541401040040381041000a01001c801461680a01903001e49070107c01040034050382004039110f08a1800d68000119200317144000c1c0743d8800400401800030702034003072110006440c0c480003185820507132107444400320b040d280c40000545040204480c0303a100803e00d9a20355020700540c022401c90100110161503007164492040440324004021205944201070400625160410110340e848051440c6440241c41c1c215207400c0d01a6458060303d803500051072124401c4440e0001d0001040118065407a4481980c4031541e8401050101200d24040648a50060305980300d50500235032104a00c2886030805200082c01c544401f030b09030b980141003140c01d004c0095640943c1d81d26204150150414420b80089508208050740b05031078101c400408600c0f14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 466671762 1250 466670512 466670537
    0xf08090115060201021201080d14071110020607031416030b010309200406050405010308030609150d030507050d091a0f0d0f0e1209030312130c06021c020106030b0403 73
    0x790003501040c4140040307038685503a200c1d030080c000c0d8080801594004450400807881d80008544164154032035650103540000d0080f111096034070000044420140f04003d03d4403940310202c040c8039214940d000b40c0304919241c08081c0c140c0704507040030280c0610b4401000741101d100e0202c0b01c0809414500012002002e600590003002c00742000f43c22001c404005450707003800650b140081c2c00d003e5070144507295566041c042583d00a0200800007a02440018007906084105640c408141162003014240c0300010505c0d05480510940001c1c100203070381c0091020030401e084892003186004980c0b00e10700022041805000780c1c2104c410b00300012a01a41a8404d09884468a5041c3c0401c4001012200200102855500300745540181684200480780c01000e03104540c4008d000366140c002045460a000d400c01088281e884080605500c00b00701320480c542d0250885800400040520986035241d0402c41441e80b400c5a05000052000680d80e22903c0c3e005035050500b512501d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 466673012 1250 466671762 466671781
    0x302190b04151d0303150108040507140a030812180a210909051314160b0702040e060403030e120a050d02090402041d040c090203040f030e150a0e0a0b04060f08 70
    0xc07008025407107450010383c041d8010310040300640c011b039040c3d120a200c100f18500151000101100c002d401c5030802e01e420800f00c0394400c04201e003913000404100480380c0341e80c0c605441d500042501c40080301c6110400c8a582e11043e00010407403215001130000260300d950306282c0c1c180041004050201c11518820468041d1200002402d5001c000b80504d02c3e28003400c200044407840c043d60084285442c245200c00c0101c0d850341d0010008090101c91810308103281c1481e40080c100300e07000b513941c022010b101c0d1401e0140e5030159100e03680100700d1800a044035031a20204c1700c80b403944400200004400c45030004100d81200d92503c8000da2900301200024009010b9a80300c240c0400c1904c0d08801c000c1d20020301588201d11414100100c140c44015000032800100e4001784000074000707600d0301081c042c03945032a03030b10390044c0609801703402200740468a0300a079603000d0104010050303642c4a803515031a000080d002e5020b1450601e440e00f00020030961002401c4000d21a0380300c0869900130 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 466674262 1250 466673012 466673021
    0x24030b0c0c031e0c3c03180a050d1104050606041409040515040b010806070507030e0603190e010b0a09140615090604171b2b0c0b070302190b0415 64
    0x3034918080c1c41c4a08000d071441c0c00320b4910171000b900d00791080361821561181d079030b00b00000c901d5094019410052250034942c0f00006000c0c9140c2c0c171010010001400d40d8503070320020721592080c1a141d540862650501055440240c0818481c0c1d5040c070050040c21240a481c00c40c0c070700d086a80300e4943e200ca0402e0b43c200740c0c1545028407004010020442400710001e541c50403103100c6400c5469944e212030040b980d5000d20b0200900040040a1901480c90031030301840e0007c51340366030030080e81c8200381408219100401c5009107039469096003d00c925141080c0c00042c941040d0502c4821540c401040c03001038010036a61040c542511300000e00309a260945050010291007d03a403a900c4132103181d2071b034420420120b494410b400d01901801802a151048440c0190000901c180081d12800c486045492140c0d02001c1c115200c0011840d050310103001000c40c01e40d03ca40d60001820003d0504090804c41c0d00403100701c00724040000d02600c2c20907845504046c900b0702d611042d103503800142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 466675512 1250 466674262 466674277
    0x1804020907180b040306021c0501080a032601240e090a05070c0b090705091f03120216030c080606220b010c0b1006021c0504050409020424030b0c0c031e 67
    0x4c5008002c00996034010100030b01807064448025006640980c103513842401500c030785170407100c0028002030062200c1d0308080e0203002c0c00550001403807041201d040090340080c030785c032050b80c0c0100c40030403000080c3d40e60407411b45488410140803e02081d80d0b941c024008404003a6030340d0008245a2090800100895100d4040e29403820300050955440c01c150048a00c00c494642c0840c050001c0d0070a180b07155885144250138842ca1621b9460752000c0099260003540220200d030766030280310340701040165101d411009066030508031541e142180040c032090250342d44918182c0e84c0c00c41e18150b071060200c20341c001b150f40303802100125040003220000038823411a4400303112440261603100e00c1540e032241e0840b000341d5003070b5140d0300401c1441036411012881c200020f03c518107154000640b000d0016102007810b00001c090b000084144d0000700e20310710300741001030040200c2c1d002400d411202c14000c030f40c00d0414542caa01c2c3c42c0d00c5041d2942c0860340712048641c10585402042c0c81d40f5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 466676762 1250 466675512 466675529
    0x70c08060705030a052d090f03070f0b060d05030d0e21070b0601031802150408120c0c03011a01051602060c010608010b030f15090312070905180402090718 68
    0x1036090440025000303070415100e0110741414000000c01c90207400318000b5801c03544500080142c2083e203c0100c0743c40001d41800600d0007919440d03000301d50300b000100350701841418901494002400c1131031050780d0103404c00e40b0440480c031480000c200d000050719000410b554001521002d00404070b03180103110352440050381c50111300703c040f0504090107007030f0080c0620707500e102594400004404845100105400429114009401609107248030301403c6800c01d00c40c91420751190b60441c0b50021710214009852000a0b106012040c1030101200a00042e0003c0c008810803022081da0001d4040700c0a041040104400d02c84854104c01c000085401810349030ba140605152103001c0d1515000d00303402582003a030b1101070360400003140309180401c040540941c4529440014480340040e00d01d00c401e1005100c03880703468414000c068041e070100d465420303590b40343c1801e1214000381408030081c007401030810040035842e80344101d50f002c2050b29004501102d6041d2444005019400840c075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 466678012 1250 466676762 466676773
    0x60c2006043011041a22090b090c030f070b030f0903070f2001110a03080402060d1b090e091c0903060603060209120307080f0a12050405062406040506070c08 69
    0x74419a21030007043d00304141c40034028121072895030706221100d480055007100100090f0002c040c01c4a40d598038040c000e0344041035007090382c2c495507003105050b03440e00724a402030361080b01503180410901c1d0000c41742d4000380c681c4504c1d104074003a9078000200b5203185048040c0004464160070710464041603805a030b034540e00c4110342000b030360002d80781250403400b000750950070b5100d40c000e04070101c4001040000b03041001d15543c0407034807244060801c070b030400303024881c1884024007030040f4440d509200714901d14101d010300005090300c0d5180e0060446400e134009006042101044501000741800071014044e5a03601007103450f903002e80d00107401540b811102004101c4d00e40c0013030a44040c2258007801c0c604420242c42c0c1c6920441000400608c0c04011550304005a4400b400e0b414441d403c0a0014a080400c1d280546508a60031900c9810030020010140d00b0b4044c54500440c641104000c028590070208805100317600031180b2841020821004224004400c880600b420b0015078a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 466679262 1250 466678012 466678109
    0x316030e120f010b01031116060b09010905040b010b03090d0c05031b0303010e010503030a02100c0c08041805090c0a05061c0e0307031103030f04082101060c200604 72
    0x54a542c482d504071400355080400036a011741c800c6c056840400d82445845103000d00e01701005584150000088401c65154059000541d44440805000706070002d0b02242501d4940303400f08142105800c04007a40e142401408002c042c001117644242105051180c0442c42509041e461401a88900780380d081c4054580c2c3d0304841e000c8050b5040303031740e8500030350034507600d48080507101e0044031140c40040c3d20500c03880d602c0c0308170368001c201d00108078100760001c025a6260341d2481d0340141c204c8500054204030700b5030800e11a201e00b42d03000183c074015200c024a030100043d044c030214460a482800301045070270401540060031610f11201c0301e420440350b01e02503180354803900701e00707015030101301c400540800405010084903c522001c40640000750358a61b00c1082d130b5001401020030903070a050b0121010444c450781c5074060040380d102c0070250079107481c0c1003102000f100c15500950011140001c05900c420060310f040d510701080c10314000d1400000d03030300b112110241501c03609150000d1507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 466680512 1250 466679262 466679299
    0x8492706020c06070503030c0a09050d080c0d03061a07110a03050c01090b0a050a1b0210030213080a021e060d090c09060617011a0c100b0f0306090316030e 68
    0x11080350541d40035615411010390401c4900d0003181c03000780154000301b0001d890700043c0c500620301050581407a0031001c0e00d9401142e131038031401904444060740040d00e0040d00c4010884c0d290342c2c034524503091110754181903c12558501000c046c008c000720118200c000c0008501c0c0c10f072120f24015001d00f0625a4a040c2203564505100c205030100768a1080400c00d103500404890300e008084e101d0314030f080c08021003224070151072030800e0b14640d8290302d00c00040c1d0340e0451045010302c1315a005038403000280001c42003400140c2c400400b65100450703031401621000c81c01108050b003140c1084000c41d028001c61501d21401380c0e80a000d07458141045c0400404517105015500a520208581074554038140c2d00d1740003000c00c0b6034a0100400040004100c00043c0b41214081100c41a00f401d212100d400e00d0880840d403208112912030740a425a410211307482c08164400b01d00800032420103a800c580c907032150810406a03059a0268030007814000c111000000c2c8001d01010b080343d4195011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 466681762 1250 466680512 466680587
    0x915031101020d0e0d0f02060a0f090909111309080304080a12050106021b01020f010c0c051c050d11040e07050a030e0c01090501050706150849 63
    0x100d440454a001038142944001103190100c8242c1d120320b842c02d2600001c20081a9444904480003400810f4040050300d0711005170014929546410443c00700405000d132007580c03941c01403040d03c0d28082112002c2900f09030070003004081a5525803240a0030800382d000b034030018201814000c00002400308203d0184001c02c07070000c050340c80e0500e8070301107410402603c0080c0300c0c4400507030065600e10308101150700404801d11050045a400550510b0b52509441a0030603040c00700b44c6135075910b070500100340f01c0703840c1404180d401d108d83c2420390080600680a00c1d0740c40d44001da6203402c9180c000b4200b0040354080e19035029804680e02d4610f80c010309070303802000300000190401c50401c040f08400117a142c407041c0141c64415200e4240801150f45400000b01a40c8164482d07105054030030003006048082c00c50078010700528211500c6d201d0a80c4a4142c00601c001441c143c40309003010100d00c0d460004810000000d5000e074110300485202d8114640c5541709030302c00051a050b107018455 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 466683012 1250 466681762 466681769
    0xa02030403030f052b14011d010909240209090a09150605130b0112050c040303080c03092e11090a0b19030903090308070323160605100915 61
    0x11101816562104101c03550300a40c070803540259502e0355940843e001400c0140c4030100541400031b02c00c00014000c100500081c0d20042c2017075506000340d1500c40803510200c0c00351203001c0e0f00740209152a542c81051000f0400411202503041420102c1d4100980482d2124100100034200f182411030b41c510081006090881e040079000001303403a040d405029150442c1d40041000c40325089011181d0003a1990740c1c000740c100510407458000780d16081c40366600401a40980d01d0311241107140c0070388003450262480b80b02e1032083c1708000e40440c1c00900c038032448610200e0646500c0c0441c000d4424500080c42c40700c511810900380c48481d81c0c500000e00302c003480c122600000c1d5640d402222146100d4140c850390304140c01c403005198240283c10000c5114864604240003695a4540f8651034104007400c60001e11070005924040011f00090b039000110581c009240106044c8405581c010144000b00342d85d48800002d40c034079015550000040c4107a40c3c0500054184503985030241b2400e00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 466684262 1250 466683012 466683017
    0x15060612180f080307111b190f12060204090c1d0d0312180f08070c0611100e07051002010f060618120204020706110307031a10180b0a0203040303 64
    0x380300e40710034204840101c4000390007051046075401030b0b4585029680c401440602803000700c01b404540a00c0030004c603090310014824800f000081d28040000b9402806d00c03800d03580400302418412038001d60341000844190854110f0940201c0c41c3c114068000c0b580010300c92480d00c42c203151255080041d695080c605800c94400054030f4104001d0700c810369650203000196010100b440002455103c912806d4240d031407035240c004503076100c0b50040c90004003190744610225010f03040286610310b40002d0105420421100380122046a40d0754000702901e0501940f20103e6560b8904144642c80280034003030a0b4951501c40f00340e01901810707208449054503468400d000940a01c1044000a4102081200c01d00d051a01304606040c4c05031003070580c0d1040e802c0100c0070004990f807080e502040701d0344000544a04d8804000707011035070085800940000b0420400800d075036601c0340c40740d1100c050300385400d280806a00c50410100c06811090b0a00f80000b050141c454000000e4021607201b50b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 466685512 1250 466684262 466684271
    0xf0219080105190b16061b18150507020d0b01060c0203071e05130e030a0309050c0102010917071b06051c0b010c0305090f090a02090a060c08040501080415060612 71
    0x620500a03d100004006200016680014842c0d401c0d039100070445480480c9007845c4603102901c807041126050380303131803030010201540402c0d0036030001c0c0a416100d0303030201404e920324038100d80e444480001d6a8020100100050244215602d500c03201a0007900840480079075a100d41c009495840342c03441c164403911916500007032070f00d0854440e204c10002444d0350080345250200788011081c080007040c44040d19000c1550b4111020000380422240710b50300402c51180d507040c81c0b81031a00d207850032411a41406c0c052004901e82c480c0e18860702d1800d1203000d944030030600b02010081840c0c01901002d554510340003504607840301c00b5002000900c001042041c1602222008079a0301d884d0042c04a4a048a4100864040c2014000c2c805020b0003408148245000245520300f0840313000704055400300b44480b107410b042340d240300503005909045241000c141c44001e83c5004508c58507040164140004d81001030340b0103481c0c81c18031504814000e031612560040c05441e0016510242d05182 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 466686762 1250 466685512 466685519
    0x6030c060313031404031e150b0a0e06041116050114130303090c05030a030f020f0d050403061a030a030905100905010f0806120a080310290d0f02190801 67
    0x18004aa0140403442c1c0ea92070b80d00e00c1c0356000e403510441c1c0c12a00c030303602c10103005c00000b007000118807099001102480c00d03c3c030740c06132030300d1601018450b80891030b4a242c03200381105919a54402c100b510003203000003440c4d5a031480020064024421141c007910b00c0442c00d40781c050540c0c02d080c4071701446840240441c4581d0b04200b11414000c43c1c2c240392004810f030808012a000c0e0384800c14450085000017142c5c0e03181c00106e850015041c0c81100042c1d40b820b040707002c803a418020002c02e0081c24001e096a0004080010114012400080c08031603884204000c005944203c01042d000080c041c0e82c000c2c581414080d22017180ca200c1d06005030381d00c0070b140d101d00d4890b89015050700d00503100c0c003106003043d0808440c1240014005500040f00c1e6410000041040004142c61441030801694a2500a46240c070000687d80180d51074980c82d02e0304104510011850388043c003d0404441c1c81d0071b1048405005410101030b10312905100203600c028803602009400b59142ca01c1d15101d84903684d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 466688012 1250 466686762 466686769
    0x5120102031608060415140109090608031c0e0d091508010b030f092506030f020c1c0207030206040f0501030507020a020112110712090620070e0c0714030306030c 71
    0x1c0701c5000002c1015480a20054090300c8116000140a800000d076803d00d10036035600fa1010350041c00c030b42e68050301041801e6030b011105c02d0240c00041024000c551504404942d00d010361000444100300c0307100c2551030032085038007601d100e9071080c0c2240d04102150b1409403404d0f125025011898400301d00d0000c0f02405249030030304a600700000075246585261100303201000190440781c80d0701034600320f507000c0c000c1400b01650b50341215a10b90845450b0103006001c81e03c81c4001c0da40214018800c07109038281c040b659140c00480c0c101a40c1c3c004e46c00744d900300c0c00c012003500001d500c000045004201d104c1407105190a40d40c0a07201040951100c601c180c0c0d8032144e840d0020300043c512031504010b50220f0f0071042842610080080c24034203503907950001d00e040d01380f01c040003401d00d6000300312081d40068107224a1481c5d00e600d041103d116504580c41d002070f4051201003001d50700104203020988011111840e1b04540e054003040c0000550540700d40c010b40f500c0d4841e11501007035104526 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 466689262 1250 466688012 466688017
    0x115090f0302090c16060f0c090e04050d030c12060b0d0b0d020a05150409020c03070203061308030705030606040305100e0c04060f0e2716060503070f0e0604081605120102 75
    0x790020a60f06450303503820100480c5500101c0b00e010021500031031407000401600a120f5266186071000c54400b02c000d100a126a006134018170590100c0c0c42480049440400c0c17410b800c0b5a2031902089804949205898007403940242d07044003407074000c1c0090b406204030050024031580c0300d81440f00488620401050343c00802c40a940700040e03001c108410325207002140844420444600d080590fa01c19403c126000b6080e252a5604005459801c41c0b90510030b255005081c1c5c400e03003441c00655100c00146001c010450424498000003142c001c2e0768480a44009541c010202c0b11010644001c0c200540301a4411120a100b000183d242c18989070203914252030240704014807840c980801132041e460054603250b941102c045910070351502d400c0981107600b50080090001300c001007841c44008482d5444001045418018441010792141755a03124801a04e420b4001c4941100051034500c1194080c900c50703c1515041e460310010040140b0403140e089a8dc105141a21082c0030300380d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 466690512 1250 466689262 466689269
    0x703020405100e030f01090605040c08030c0d03020310150f02100501060f120b1f09050f0a090b1513050102010e0304050105040e0a0e070311030d30140115090f 70
    0x184148000c82000c5100d510043c001010080440d1950b5000d03901c040d003111a550b0b001c1d22181c4d101c0c01000103010320690403400034060719000b1450030b116414125101c2d4903424107002096000804245805880c81803500904a61603c0c0c0180e40083d0741d018001111075200c0d680580100e807203004003102d05120310317412581607807600200e09103003180c2200c0d66800d03910300140c90390399040011503544036030000542d0f00008a403c9407820099403009404100f042e401079200c5d6074904201c0c09035890305d0740c8075021a90b04003000324540111200158070200d010030a03c02d8800045144515003407607003c88c00c121102a0000c10421220a604a45070301c0345000d540d000c1f41c0204010042c2c100800d50440d801000140d0000701c1d900784c02c2240d42000820f5000b41d40d030314070282440b00d0303a242c14001001c461949040c103c017607000c21058018003000300d807145803400c000032108003030751542604a18541d08464000c40c0e5190384504446c0d03482c07000c0346e800400044c0e003a200400c8150f840382c00310055 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 466691762 1250 466690512 466690519
    0x2040f2310050103090503120c0901080c030402010504171f0203150105030103020a030816150501050a050f1f17041a060102060106080c0a0c020306100302120c010c12020f071d0703020405 82
    0x100b410100154090510201d00b220b41344010801c44035007038900f80e480740c040c40500810b80c7c0c1e00d03021100010103410000c0e08166206404106100051b0303002000c54048030312000110271221b600020f40c50500545082500d1001100c940c99003a0600300c0e8020b510034030800c800b00072009002e20044859000900000790482d101400030b00101c1c14440c06002c1d1014200c2e0562030501840d61140d9101c80559a160801030312003005129500e021850740019282c01c3c0c0e020504070309041d0005e04141c0d100c510318210b4203042141050785030700c00c42c011160144a03181d00201400d1034588039021040c0043c1c10505210940b010914a6102040c1c0714104c40d1103503280c000c40d482c3c4409003907250b4030041d140014018400d04400060700c007845218442c000080007004042e286005201c10803100c0b41c1101401e4201d2014860580c0e0800304031804290801c4910708070340b90b048800d03460650003c05040461040080010301d10701d250b0b41e41e114a16015031501840c0d100e001058042c5e001d0b60044070790 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 466693012 1250 466691762 466691791
    0x90905190e150a020912070305060703110304030f080601091a1b0d05030f09071802031b0a140d021605280209041b03060218010e0907090302010c0f02040f23 69
    0x2a41103940c0103007402983c0100006c0d100d21074080058501b003420340c0211003a801c45010020916014401ca0710b038102003120540c55898541e50040440305220070700002d200100011414691250200d00041d1034400ba00410725524280c9421080c1c110020100780d000340d880e95403142070000300b03c1c40c00200300c645503542152a0801c40e10315100c00107018003900e02c80d0303040021300c00540b1041100da00d04104001039030380c00e0100c00781050f01141c610340009800208009a14140c4c0050744102d85524182419150745440500030040e1007070354902c0d100c00c040c14445030188500031811020010203580120060070110034804124802100065800090400000c000c103000700d41a00901104c810000c048075203d80d60791040340c02c900e001d02e03070340241d09040c202d00396081880303461a480c0440d16001203160040004145500d2404003c0c1000b0f96001e0784020400d50702c6441c1d10083d401403041c80710481c0729000100a000036a00001c4d805a046003414404000d21030301809440c803c0001034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 466694262 1250 466693012 466693021
    0x207140c01090302240d02071208010602071e05031507181a0702010216061805060301230a08071409060f090c13030c03080d0e1615090905190e15 64
    0x3607200c000b1100200c402c6020305c505140d0940140c01440300401101005840317800a080110040f00c040c001c0c0000e1100b0350f001070100c184c0008900c0111502100e558034548003060800c0d10840195000c40e13003511554014042e4034208480c039903c5030b40c2c0c42d501d010f00302840f080c451118400501c6264080c40480d03d40c0805000300c10000d058042c01030048a40d20801d020750082100425482603001880702c8000158124940903d200207005c00c40e111400c550411141004012045101c1c4154010b521244103d540355244200d005101a4058421169840034010021400303020107030f201b071038900c00062103403402c1e5001102103040506408120b548404440c842c44e03000d0009070030100000d0300c0020000e10a08400f40c065403081d070215031250f00d0314520205440b80880d2047c402c0e048420086205800303529001d0884200301c40210f0348165081c0c0039115400f4a03005550b80314206002c011000da801c14051a0105552804004855134003480c50f8842e118000c0c020107038400f040100c2e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 466695512 1250 466694262 466694269
    0xb130f02010c0c0b030406090b06041103010e100e090c040609060303050702100315080a0b0a0c08150d080c0318030d3219030b0301180602030a1e0207140c01090302 72
    0x8141144550242c0001c15210341603400140c20446e000c50b0040c2c1c0307075000c103002c000708908095005401540d0600c10302a00c02c0705c0b030101e4081406805110704a50001406151500b80c1510003007129254015480c10311001040d1a00d8911504500681c00c140c000078011540e0710841c412250156076a40c1007080c95420440c0c500d21402041c4109921110744510070360540701080c008080000c0141f130146800c1c600718880c030b88014030038543c441c548221400d005400091040e84201034400030f9800800d040001840c80b03d80f8200038026103408903030010307112030010040801b48181038281d2807900c12407080564407810743d070341800055007240440302c0c00ca07038845040c6982d070310b225007003904105c541040e52026080382079401480003040303000030292a0544070380c120210050b40240035080500da80003a549203189401402d040d4000b0002e81c40144d0360b0310060811601858440c0415034444816002e50042c0c0d0090b81d9000480da854555400001055001818186c4440444071314507000c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 466696762 1250 466695512 466695527
    0xe15100f0e07171b0c0c03070e01030c05060d091b03140d0509010302070c050d060b0112051b0a020c03070305030405030d110a06090510020f0d0f02070b190908040e01030b130f0201 79
    0x240315000c0401c02c02c1503d0086400341507517150381401030130500038503010507152440c542d015208858103500107101140d0483c100030281d580a844441e901c02d180b0200100a01c0d90140c090030880c420b801686140d41c0641000c03007164000d40c0c030500203602e880351913900c510030044520003241e030800508205500980181c10258041c6020303600d0241c0e1100810050500c0c42402c0341c89513070702c0002e1a06580c00201e1004c2c40340726042c04000e1460300e000308e100201d2520254030101072022841000c000d01c208021011588003800350741d03400b41da9117041503032500300f409101e00ca40102c1013804805841070034603d020b007802c04c004004000c1c0d2503c51200030402c0d801d003901e40e401000200814a055030004100006075a000035560b4011210b028045810b8810064000307401000a20042031001540c0e03034102d015219012150284c07404104001c0204100040100c01e001c600001c60244030840d207412240213a01100c01070340e446099080040060741d004040ca07046100c0000503510a022 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 466698012 1250 466696762 466696771
    0x607080a0507020703022e05040305030a031509020a020604050c040209011d0d080a050a020c0409020306191506120605011e03020a0207170109020406081b040e15100f0e0717 76
    0x60740c80407a240d80220700303003031042d600342d00460131131481000030152917002c400c0a03c7c03103520b090750a2078110b1791641d48a01ca0f04894070b0403d500c1e2020350600074512211280101445d180841d80c481c1c60301406522120121819200c0d80215810700007681414002c403502d40c00f0580d41c001d10320000c0c40401c2a280c280145541d0040842070664002882140c01800204c445d9201d0b0380c1c50b2000000024501407450144c64021400c00e680440141c40010300d0540250340d0418800c0c50031440c400003c010100034002c0b18602002c081d00080b5160029803d244881142c50706104e155265030041d00c8030443c0003c0c07402a044940110110036220303a000d00a240c03081c0c03041e1003005503600d005812548041100b455203943d5070314000214070b02840340d14010700d103003000f800401c60003034110351001040c14403a90180b0b8031444040d0f1010780a00095500040010000c5014100240c02c0d1406030054000c1040380c801c001c0012580000d241400c612841480c0c3d80c0501414090303030a461507040152 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 466699262 1250 466698012 466698017
    0x1211070611010e0d0801030507120b070c0201020a02102601060e060706150e0910050907060f0207050405040308060316050607110f030a060e01060f08030405010f090f03051e0607080a0507 82
    0xe8615841d070f40130300491a2044080d5190601c650450a0a504180c4250b108440c0c6102074820500010700d040400d650003001428441d06220076400140e0404124541c0294007541c02a1a0030741660040341464405003111205072200500300e400b90a146804c0c0910340108070501c1901300f2a240550061100320711401011840890410a001071141c585d0055608964500700b041b110340020403088200c100b48010601a5062410085494500b540076410401103070a8402184c0c60007000b01000401029004000e075142c1400c00511181003960301d18440d00500c24010300007804404d90032305070f4038014046854501d07a0717541e850821305008286034100b2070000c4c5d1700000356010302001006034000d84000c03c0007106610003d00311500713600005034022414000303020099002044c0d4054440030300f000b2445441c896400ea4008a030342c2d00002103076504400200802c440442e5000401101c0300c19000c4403000d881c040c90300e88008031041000210f90740b00040e0b0b5600d5030b4210a800c83d400c0d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 466700512 1250 466699262 466699271
    0x11120421050a060902130b150a020313080105060117190203220b0f0a06060801031403040503070f09060504050c070204110d1514010503011a1e16121107061101 70
    0x107585079801c00d40030360303000d4451503030b00e030000404e6040079810340406031840342e010842c1c074000100003880002e40d032501034040000482c0c40c0c11154001c00449511146080f41108526507492185010304011100d040c00a03020002e00c56000090340310480c020600418611000502010840c00a4000070074030b15840440050039040544e400d01c00c1017036540070340440246460400660803a54401a040c03001040c5000f004101840c0c0c86800a815264017038050383d400e46140d18800e10714004c9401551f89400b880400003220914500520300702c66280b0400d0042c1c4e50303904101300c01c40b1011903c003003607204100025801450182d210241c0790240c404028145484117040c2000c444042040f481540e00c000c0d82440403e045a100e0940a4801d1a19a20f10340c1803091030070646942d11007042541c1008100c0e048403c4200801c840d90800e240580c03900c032041004100444031940c00c4c1650314491291504100e180300d4103a500b101c5926000030080503282000c12900712440c0800d54406542e01d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 466701762 1250 466700512 466700579
    0x302060c0f0d050108060a0b0a0506121009060810050f060901060c060f0626241302030d030f0f0b060405061c020304060e0d0e030601060e010509100807111204 70
    0x203e106081c0600310000003420329192907504a000c072005140d1f81c034814083d0200400c4255030f6403084850680e040b51070529142c4031130740181c10502498100c0c814072818503030046082400081c10000e04040405c2c1801a40c4945440303c0598030103888050b00000240018040d0390701401d00e1100c840d110340000a8109190340500c81201c007c0d42201c0f02d070450519400c000c110f0031000c84005078805001a2124104881c0f8001c414000702242c0008c0000c3e29000400f2850242c01c98a0101e4000d4151482800c074044d000f8020810400f1591070309207840c5180400c001a885054030002000e0310841c5040c3c20401001419004400300d80441388649100c08141c011500145008601c41c20380400d0400404049a003410500f151200402c03075a1030040125680014030541104d820742428038065288100483c4c4911800d8111904504030044000c00030b64000900ba1103200640d803800846500030081c103440304003812100007046170500081c08000903d6018201030072404040900e107900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 466703012 1250 466701762 466701787
    0x10060818100e06060a05010302040b070212030d020307030902100c0f0204110c010e0a060b0613050603060a03050105070807090b0405151305031516090503060f06120f070f050105070302060c0f 84
    0x60b8480801c038541c0140003481440d04005c0d8030707a00503140908080d400d0078140b0071821500e0195000c0688a10700c010400c1c68110014030031034410b80d424980035562440d000b4800740141c48100707402c90003184080442000c20f1311684010b030680f944031040481c840013540811000c0d22602c2c0c02140d03924410007494040307150034803420494465400c0502402e5a60342001c0c01240c101c034240600a8004101540c0200d800c3c3c003040e020350741d0465419489856450115030352020f19000203003e0342c03810702840f2800c0d0300301c07a10350300c40d601d540e44079099035840d030345400e6a40c011440740940015420310580d042090341006045d951500300f00801c440c90303803100040c0c94244c200310380c02c1c0c0d16031544060001c0c001e801450b9005480113402d04280c0349140402092b52460b0044c800145a0300241c0818500c0c1c2d55030559461010030300c01241c0f1222250f4208645498641c801c52082402c20400000c42d54010401d840005400d60040c200c035076a41800f45142d588040ea8425100c5801c01c11b2041221 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 466704262 1250 466703012 466703021
    0x41112070e1c0b0106050f1e070206040314060106030b060d050a1103071e020613030807020c04020c030a080108150402091f0303110c03120415090302180402091006081810 75
    0x3810081d40e00002c00560074007911520701a00f09008006040244d58401e5000d90201c0d1104030050555403901d1500b0b0303e108106001c0c00200a5210400140002c1800304030078a660200c40450280d81f4181da0b503203002d4045504c00c1d0740084e04481c0034000f02200f06071030fa1005902c030a504c140460000c000442705401d5a2007100c0a4003c41c091810b81000e5080400a40300529054001810360b4202440503d03000800030704024100030403180005d503028424071180000d00005007041d510f40c0c40f1408260b8503504245946000140d44d1400041c1300340d00015182c2d4101e01d103400c80061a100c6809214100c0710041c02500c50030365010030510045113083c210341c000d50007a0749062a841d408101c950800c2064140c00d4407a502035088d04401e1240c4000300d80031194003d55400510030758a809a07480300559001a50003142c80c03040b6a41c605c1c0c1c4100b07461140d8822200d0781c1140ea0350b13046802d2610801e000700130005588400090214900c021907440c0a02c140007254496803041c10020b081d503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 466705512 1250 466704262 466704289
    0x504110403050a050f3a051905040603150e040602030705040b03040c061e080c0c0c21120c0703120e040c0c0c080312060d0204140a09020a05041112070e 67
    0x140c0c85210104084801030251500c0e043c000d401c4000c16040724131010011040d50403200c0714a81c0c0011b0002d49650103142111464805c910b80503007004502c1001511540141c032681012a003006001c1064007049101c0c9029103800b6070030104075171555107490001307400040c040010301008100115003078103820301440c41640708259410905083c00802428a42c40c80d01c046400c0103c2e92604019170b80007000a1f0f805490303600c0e007a03100c000e48000c082c6424031080c515038002c1d103020115185d01e43c00141e200e02c0a20200122441c0d045001d041e04154486d41000f005150015038041c00020401403481124005c94580744c0d9260210400081c1107401032014640420804194001000b4a102c507280c02041141c02550070800710301c040c3d410442c3d0003840c241c880c880120281c011580d8a51040082c90f1058061032031900d0150010801007400e02001c0e03111b10810440000c891420b4085c0d100b0401c0400340c00c60510001d03444104600c40040d00305420f102608031611400d0f1203005079940321 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 466706762 1250 466705512 466705523
    0x2191a070c2102031507020c040b0301110706050103060e070f03060509011112240307030b090709050f012d030204050403030603050313062c06030907090501141c0209010504110403050a 81
    0x1c206203881018544200784917428001c00440c4104040103801091000080c0400d0f82c008c1422440d15000a00500c5440ca031104034000c007040e4001800016400103050745d22510040103100c480d030007165980c54036441500c0710f003070b001c0740c003840081d1140c1c00139074200310054004603207005094240c150581119030010484111041003244960b1000010b0340c0c1080c560030019503418210380401d480b001c441c04040c00030040700700420380581c5c2c1041100c0007070044202c20802c40c1040d07011600020001e00c142c01000001c4000074502c2ca03010460b80c9007100d40d0b4010060ba2600d10f600303200162000500540c00e2544e505000000320348148010030200300c070f80c45140320076424104060400705c11030211350019160501c4070303480d80500341c0c950300c1c0d502e20440d03540d0345030766a413040c4900e4040d4580206403858281000080e4503802100102d40072441100c40140c8813000c1c40c0840c2003003d41ca04041e501c014518010001c0d42007540c04a42d09042c6c50185500d00707501d90311000d01d40200710804441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 466708012 1250 466706762 466706819
    0xb0705100c0509100f05160c050d0f0506090f0d0806030307021302040603180f02040207080f0c060f0108160e0606090a0e0403180b0d020a0c14070302191a070c 70
    0x41d103001c000f031300302ca004d282c24224035481482a00501a0050b051010310342265144900d051203d200f500301c000704001480c180503500185440d285000341d80d08111841d101c0c09011458010300413030159904920036000307103800c841001003110b1410000c1c0c02c06806003c1040b1510240c2c83d00392001c8840c00f982000540d480b4a4510014101d031240002201c0c0319101c0c82c10400050141c4be11401c40c0d07a011900540c55050300d00300000240700300001c2c032180b020001241d02d11400d000c81c56030f20074005220f42e808260b81c2c4180300b90711400180048011150604014030000648001684d00b080000d000c141c1080e12076000311b411502c0e59008070034000c01020800c030406600c0004c54043c2100020003894042c50056130450074041c003c41074030b445030003080001c3d28a1007803000d291940e130020b0305204502d41c442d48064a840d0a13000580c000c91448401e00109851035456078212071032522115041c140c8518051096005081e0481e40b22000c031400048404d8070014429181003c4596030701c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 466709262 1250 466708012 466708027
    0x180a05150105040303051e092805100219080c010e030903010c03090b0c0a2a12110c0d020402130f0f081203070804050c10030c080615040b0705100c05 66
    0xa01550384580c10000304000600009520000383d80451102c00c50540302d8a0031403c8900d4540580350034550030401b80341c038480c2486802050328010090302e00e440301003944c80d541440100b820100740c0f2405a0b1041ca032062109024035400178140e4010b070b10860030058491000c03401d645d4a5010860b041d440821074500038a000e00c522a21108541810810241c06513644144114000c0c03107a40401c40c042400e2070024068844000c08000142d180d91000d08108511404803808842c103496400003c00d21071056401680c03600d2000700c61500400003032184204006090403014000c82e00150240000c802c03210300c100c4802e001c3c004400000388520708061801c0540446940064010ba1001e00d400703e8408000049940000f09468080800c1c4d031103051444c039280b10100030a400c5400075403420031469040c3e0013010b442113142d40d660016100c180403c20303160040340074055441c10411040084004c01001425000c0c4258140c9200720141506641264484003404000c03c0d00000c030301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 466710512 1250 466709262 466709281
    0x5030115050906031603031d1c05150103150f090602040305010506010f020313060e0414040303051905010503030412020a030c081c0809060402132c0d0207150e180a05 73
    0xc641c408821380c002c0240401c0300c070ba00c00224070b2910024051049110078080c440d030b040c003144070000401810508107084c0c1950040c0c45010307001410f44290280300080c8000c00002c04a80e030480341c0040034500222043c1d004c4200420b2500a841e03035442d55145454001400d80c000b50009600030000003400d85411740014001d880e1810028046400400c601c000100b02050302e441078030710b01e2400802142d5400f011500503c1c03400ba00390004c41c69039003000101581134009510881e80400300f038844034002c0d2840300c1550000e00a0320b50641050105004800007121482d030101d00090211000c680d40c1e403140d240403500780d0041c3d0301c10b0708444c0031001c000011141c910002000c51510364050305e884842c0a0716600007800081c032a01103020300c1d416981858010702d484044a02c452910741040300d031240640004909000094083e52405101c602c0c00883c554045030100c002000074180c1c00c02040350132003d80ca40c4079a03c51501c447c01c00c4112500310089120705010395002402e41000e1864 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 466711762 1250 466710512 466710529
    0x20106081501090b13020310150e0109031e0c061e1e0807181701061203050a0c0615060503041b1d1b2a03070f1b0503011505 55
    0x50116404104203200701841c0128403411941100400203c40e0307448800165440d80c040c0d031186503180040180f002040e66140400100e4140895003c40325054981c1a00d0702004c0110240c082103140c0c1041000c91040308060b083e136500188413004815070b5940f102d05080040e04101d0008035900c80c2a90748500c0704000704c210015a05104441c11910001c082c0080b016070040000c001008000c541c800d40202c60092030f80100300c8000c40342c641c49060744610700c05450f220804c0341d030038a200013503825003819001200c20f03055514146018401c1c0b41c161094008090202e030842e644400c0d034901c0901d6100250003500d00c542d180d5540b81083d0030208140c901541c030040720039038100810010183d800ca440026441c0002071103d143d03036400c0303c803003880310710b00d02c500c152100000c1c80400a030401c40d012124921150300540c00d00805508881d81d90162102c003c1001c58048000380101c0e13800c2101c66090510380c113054020780e0300d0701c001c44e0035903020038905060152212821310982c9003201c030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 466713012 1250 466711762 466711769
    0x206070c08100219110c130c0e1005030c1b060f010501110d0905010c0606081203040308070201060510110a05100f06050f060304020609010c05191202060403020c010e06070b04050d020106 82
    0x42c15400c10754210000c0d414541400d101c00c052080502410460100c10300c000f644003403000300b11038031035003248009201402d203002010000030841030000360030b49440d102280f0812540e03a6180d0541d03541030760803185076001c1011500e007030b80c00c60320140401204014540c4501001100109154500000034104500b0704240d520203821550220908691010080c0300303e680901e0041c00c6c0640c0e50900c0401050190411580b6000703103941080803030004802036014600c01c1c0d94118441e505c82030101c0c03c0310850b0166503070100d0680c240c0480c4a00c0349080003100212182a40c1c0000002d81e10a07240c60290000c8030308007038a03491138844540c880c0c4a060300802042d1a481149e44884000070910b04c0002d000912070200030920140592080041c10001c5a1100844104040d5540944c0d0441d002c1c80303080310089005403001074a41d1001c9843e9021f9980b640081411f003101d8401542c1d01c2071a02c0c203454000b82c00784901408217038020811380c00f03540600c3c01750100300765480c002030950b000350700b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 466714262 1250 466713012 466713043
    0xc08070b010b121e041e02130b2805010f110d02070501030b0a0303051b030f16050610081507030f02040b1206030604031b0c05040c030b0a050f100503130206070c08 72
    0x20754841820340c0d5040d4158003030307400310303600b406642c440d0001211b0003100c182c0a5040b041c00c1811034002402070340281b110001c04c55280700220020f6019250b07818040f14180e0510404600c02c00080d4010010201006030701d0900c40e001d002c07111503051800a000e02e1040050f88405000c0240396018890400034034000c0e1080c49030181543c8020301148924940e10002048120300d502c204001441511681d48000207415540c0d08407604a4003080550300d41074406018440105002c40c40404d103402c00c842150025000743c6017a8940c00c0c0380300d20000c01d900107160722820f0100f5645407074401170000e80304503004291a010715041c0c544810200910450003940310805102c0404d81240c1200992081c0d1410414910b07418035101780ca501c02c0380e100c0c0741c105080c8001c0700c0324243c140e0842d81e0101011344014a8070b503621010032408078443c950003504a0184032040e4a014415001103a0141900181074003401c07841e8041a840d034070040d42550000c1c0408424040703c03030180425802e118811 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 466715512 1250 466714262 466714291
    0x9130b09030c031209010e0f06010f0f030c03120c1b030302100e0604080717030a0621170703020109020904030305011a030402010e220e06090c03060f070c08070b010b12 74
    0x31280030740d403442088041c51481410400169003404250087e62a2060640585840e00d10451106a039040280181801c85201c42d0700800c462405500303580403a5013050b00c2d140190318588890310781604c528810005c00c40303042103110104001e50910460501c0355011442403074518100203043c200c0080020555a080c51550301c03160000040f555080754005090303503598516454000c3c00809151804000303242d01200304200f81200f9400401100c04401c20500c4c070a00344803541300c00004048004041d0789410001c0c19105100742d01824074103100b4000051064100e4000403100344003220b04400183c1c680005105007214041e1010a011000c1a4036066003400c0e030010b86469030344900c1c6400707059080da0342d2001908103403000a08038520790381008080e04150040e070b00c80d003046444100038460442003a8440c1000111507101c0d02c0803d00200007030710b54400480702d91039903c1c0140c45548052140c540441c8901e0b25940c000e02e0b050070310a80c0d54040c0c40702020120001441c050021400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 466716762 1250 466715512 466715527
    0xc040209030a11060d0501060207050112422d060509040522111903210207080d05030103030807050c3c01020d110f1b0c09130b0903 58
    0x2e80301d0340c0d10343c4810b418514400c030f6030110300070707010b50400c003110681800c00000b0380e01d030041100302c2501c40a0f40c60324403021403031400500b03507000300303030025114100c0e20003146892290003a00184c181d43c004d2014950000c407280f0002c0b1050b035400280c09041080ca6900345c404c01d822403180ea60b080ba15024a1203450024050014051083c0c40c41c041d82d10380b40000d280d8009040c403902c030b0312030078441c0580c17021081c2048c20b0400d40d000c05880c0994081e0104c40401c208071101c80c0101c0341c0c020b82c22400002c5010340f88444030801242e0700b0540c80760040204848400340181c0401800660300c0544035071550400074181a40035180005100f0100310103500204040340105880407624200c2c03200006800000c0544018040410340401080781022403400042d001032400ba41c03040300c14000314404400c205220f11410403040e51000f41000004040c0003c2041e00500e01c140ca400c6c1d941a508000220f1555503044425203000701c0d9143e866400c00242900e01c85d00501d06400543c200368a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 466718012 1250 466716762 466716769
    0x1031b080114090709090207150e0d032d0e0102070507120506160c12091509062a03120f110405010318080417191202190b040201260103030905030c040209 68
    0x2030382c0c0a06e410329500020050280b1208440e9440c031960300801c100014050300001c240c4440c0c0050308100040d050030091402000d070985141402d0b10090300803808141006032800040c4603044009107255001d001d070f4008141c041c0705400c01080040300c0014020351900d400c17410000000d01101043c692220560f8469501840c05459140c1c0500210407000c00c0840079100160142c5c800340b032010040d80528070b00d0768001c14070b90454010f80c444449049c0220901035000b0681020104018031100e00e400100303119201c0c1e0034082080300170000e249048031448105540c40c540f03845400042c002400c21280d41d00d40b046022050710341da548684590155a5504c1d940b107a481102410315080640310700703102c02442000e00c07000b00b42c141c00306040780d1031803c26241c3c664050a403000d8022803c501102d00311688a00340d42661055a0004582c0d6503801500c004418007091030b01e41044148900c20341d01100c20040c0618003a88805a101d40740c00d040500c1c14425041060240340103100301700c0540c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 466719262 1250 466718012 466718027
    0xc270603020705030714030a030b03010504120c240903090909170f0c0604230715140c030a03091104022a15070f090e0108030a0c0201031b0801140907 66
    0x201946409a580d0307042e410104e146000342a8081c0080c04892140d42201d50700000a00b04220582c9060081d400100205401c803102120060081c841f034003e05030803035105000245c41a88036000702d034583c1d0102107160260b03038070003103903242c03295070b5260790700245030b0810184001803220301028808a489a030710100b40000072255a42480c0000c21200302a00144050760010003025040707804910b018200981e415052100b141c1907002a20724899400d54081440c809441843c0a40280c2e10000784c0222481400040c842c0b45400b8248140000c040050004000d0403145560200e121505800c10300e09808500c2030b000d10070740c030412448202489065403960070f0100e940030384441040b0a030703500e4284040452200451030385e5070100000503400100200b69244240d03100380c12282c48424410480c030081c060100c003130b8010f02026600c0b07486901102c0081c1e2040c507002c0f03076452540c040e51580781800710049010500c48170050114007180540703040a4081100d8602040c24890006480e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 466720512 1250 466719262 466719269
    0x31a070f031d1f06060e09071805150d0c02240a060e1f0602152202040f06081908040e04030302071b03030f090303080601050c07030b09010c27 63
    0x1030301c0d1a0b030038586010240d0000c1010b030b01e54040e0342150a4450410562071100c44032241d80c58542040480d403144541200c400031600501202d01e16120202c0541d034500546502098103c1110000b081c0764a40c0281c0c5c00e584000210060b0b00c4110803c0e0002c15909486603100071584a11400c50310300710b40c85500e01c0e81c58680710000e2010340f208503248015202c00c2c1c00849030751008005001c1c400301035034580d00007504d410300a421003a48400b0126207401d10b43c0e21070402c500401001c5043c8980b40303818007000070215070000880000300e90202c3e05503901d80c182c800b01303950f440780104045401407000440502400c01032038102041e0f40e542d581d1a0040c0e0291a00203c81000051708041c080d5044403950382c3c120141808914000a15124070b02450000b140000c8020010303c82c254040e0500d40c084d40e03415214200340b40d4440c0d00440c0c05800402c44c5030060300c907408001000c50b90b89100c035801400518000305428107060806018142c40200f8010600e030f15080b01942417910f2144201034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 466721762 1250 466720512 466720517
    0x9191b08060d2a0e0c190507030e041805010903050405030c06130303050319020d0204060e120706030c180f1703030103030207050402130504180605091b040f0603050f07031a070f 78
    0x18803e0380d0310b210805031a107401c400502c12010042c46201c0d0161800380080c2d501e17851000301446500041200c0502680310018041896a602c0100c0c0f440c040d0414098200390358180000c41030301e9180c0c0c1c2d0944503036200a4011580020f018402410140540e0703103144003d036406840c2481c1c080031101c698040d403001070b040140120105901c100b1030000318040b4420400e00f5525206404007000c025170061150030081100d488440805080c204000b2090711081c00241114500e4030800b50003400fa00d04140040010703d1034503402c007001e4542001c0203060342c0029500414140034120700b4900c009034000d81d6690052004000003507000800b80143e80c815107015864244208144403040300d1504443c0e401420301d0100b0350400508910101c00398001c0d002441a83c0701c1542c8661542042e881c10070a52100448815650510380c114100000031000d00007080b81d6683c489c9420310003008010300c4640c200a504105000c00c0071068101421003050315641e600b841c920191401e0308101c2c440f0706 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 466723012 1250 466721762 466721813
    0x80a0b060118081f0c1e050d11180102010203060a03290a0b0306070504050a090207020f031609050f010e012607152006040209191b08060d 61
    0x500d40d01c00d1496000c203920380e48140310419220700c0c6160f01e90b10700040e41104070300f00405041c0d12685070300034004480126180d043e10310140c6010705d8444c01071100c01d00103000040080c000d000c2018445d121100c007a2008464440561814a9140b680d0f90031800703045a0040c410312020795036a00690b800c4a9226803800b8000c824814401c3e01084002d44207401b030220002000312114654200011500080301500c840d41c0e9000c006848a0059000702034006801c41010300c00e80410341d00803c0385500040c00d01465001a20020745030002400413006216000101080710300c41c5030040542260385565800c0c007641c1810450002540d0510841510110081c40c018000f07610788907460301980400195040192200482c3c2641900c401f002000560a446045403000d00841d5407404d07106c40d0300c082d06441d00c40303808006411001400084a80744078807162103111841d441981c00b03003908080c0000c555501c25030f025011a000403e041e0041140300307048400a900b81d280c000c800a070a01031102d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 466724262 1250 466723012 466723021
    0x3051f0e130b0708150a060f12020405060d0e070b0c03030c0304060e071707080303160c0201141602090604050405060408030a09050a05060a062304091502030727080a0b 74
    0x300341c0990050066a01e0b02c1c00e00000990042400f846281e10000b50101c41248205021108040303101e01400210000340c0409030601c560102c101c15481102e02500b403c0d03c9400048403a840041202c002950323b041048922a00b0b01240c1c00800c4c840a091342013101d140880740e106c2c0710040100404210001c00141048026482440340641500c111107000c0d17200d401c0000d040251408600561044800026076581c0c0001120b12502010304045500082d0704419105c510300c0f181c2c00c07410b0180138400c451080405402402032921150f03920070220036a401407000d980c0d0090109800f0f907050504010100f240083c509411a901242d029541c1e0f4410f13400000506d244100204140260107407902031140018115010710401c450800c481ca41d078198140b03a00c03508250440d42e40705545001d11403860310758071940710320f8080e40d03050610045c840c0070702040703074000ca40d0768002c2019401d10740e09004000b03400340c801c4012190000f41d503c3c10302d032400c0e5030394a4426000700085000300000c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 466725512 1250 466724262 466724281
    0x307050a0210032c01060503010b0d021002031207030b0906012a1407090e060a020702010813030917010507020706020303090a020603130204060e0f090c060904020705071802040603051f0e 82
    0xe0041c0003214812400a0341c412019030740c909584c5090080e0398200700d0045003c0c43c0620a004003048020301c25412500e950f400e2208616142c0061802d50005100c2e02d117101640340105440784482e42c0c8c1c00200c0c030188008210921001a000904001c00414000c1890b1245400c6004030440683c3c1d80756060024500000506a40900c46155010394440041e19424903000703114404140c2054600c540d03070f2005030030103d00841601034005010100400c0c034040c592401e50b2500c902030b203060240030340c94201401039001c11096244d003981d5298100b02299a06110003000740100d072010750300d141002c10310103a50f0050b640003c0c1c800c03080000820300c070030900d0310007040c842d038060014044075039122210102407070100e0b00305550a1080001030010031000c90025280c0000038105800c05a00704244802034004c0501185c2e14810800e01045200307280c00540c2c8142d165520141e030322420030200806680c0050650b403c0d10074900541490008800c00b000169500186141e89568424405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 466726618 1106 466725512 466725521
    0x7050118050a14010e01020423011815050405300303010e01060e030a051f0e010614060a021002070818060306091909081902060106020307050a021003 66
    0x50b40000340d90f01c4414245020f44100014101c0074440c602400ca9120390016580409001c00880030401140000900d81c4003e281a06a45694a40d10310841781c06000e01c841030707800032107480d40c6503200750f0999000303043c0107001d03041402c4600780000340043c9511140868030b0818800754507800000080780e04079044c0f0511000316a20b0f0110869200c008511982d9150007920101c4c8041101004400200c0484060f12540c0e81c040801900440b21000e4414400d03906101d0200050b03520030980e03451004c02903680e1541c1d070723450b990205c3c03c0c00303804c40b8101c0010348042510414407000c070000c1d04d030314459011090107200c1e02ca805c2000074041111029800240d01c40082c10fa02043e40c06880216440c54011505030302c2517640004d01d4101c00703501c44240c1c101a104c4403c19504205c03460040115001561904016450f025200d035044100a1f0065048400d5800b02d14441d074803 = true := by decide +kernel

theorem cover : BRFrame.Cov 466546762 466726618 := by
  have h0 := BRFrame.cov_init 466546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 466546762 ≤ n) (h2 : n < 466726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
