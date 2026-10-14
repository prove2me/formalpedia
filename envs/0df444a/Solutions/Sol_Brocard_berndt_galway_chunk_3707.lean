-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3707
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:26:46.138931+00:00
-- url     : https://prove2.me/submissions/a4a22c7b-f910-430d-b366-927395f73dd8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 666546762 ≤ n < 666726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 666548012 1250 666546762 666546781
    0xc0c0a090c0306140609010806010c060e0303011508060d1704050301051005270109110d090501050f0a02042607211104060605120a060503070305030c010b010305060306010603091505 80
    0x1032201d24012a00d840c03c000752480d152020300e000214010805410b000d0880010b4803030160007003071281044504a0f401001526910403040041e031000f0081d9280c1d0305051110480e00e16030042041800308103c02c0041950750180b0440030300d90b01c15150300e202440344803410410700071a00301a6155090600b00207104d4a141c005108441c01140c61540a401c942c509040c072040c2d2030b42480c40c98800b00010301c01e4004640000d001c81140d400358038038006810f84800212503111074101da069440d001889104199041000d800069280c0110300c1c01c1c2c038004414201c00c40ca0304060554201601001003004400e100784802048010b6866400e030100c011401103528a01d0030403514822504c00d001001c0c2800d00c2040c0580300e9a49074540f5007000c4520300840207a00a01c0302d00c80a480d0030300802d4541341407042c90020740c07040004649404420101600390754010302c0031410103103004c0420116075400542d5504442c00c07401c0008810806040078680c0d0070001040c0d800d82402d090902a000740c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 666549262 1250 666548012 666548021
    0x270f0d020a11150f1612050901090e16030f020c0a03081803120c0c010e0d030c080c0306090402010c0c090c0807030c03061a0a0504080601030b0f090c060f0c0c0a09 72
    0x900c220700c4002c180c840d4108100c50040050801c205924050180038100d4414074010b0282030519000300012442681e10500044c10000b20310700003070404034100c0515600035460102070250000c071520b151800c482e03460240540326245200b019120307480d26024500a9040301c0c4901d01920944117054002d040140240205881c0c00d1054140b481407011105408007d480c10307a040c000441c051902c03078103d5004582c0122082c0b0089550b10240c460240e001044002410041d07918082030a059200001e040100c0090041090860400030441c90390358800c04140d0203582401d020504941c541800c8004084640180700300034a0002440700254121aa00d40308601d2a0340500002e6400b01086003640c11610036012807102d00303400303030000010990280c045e6510a1034990709041e92000c0c400d04e130010030791090b86d842c4100340500451007410310889500c000e80c080281018501c100120b4068402c440c1c44000d8080c01007007200050509010360142c4090080481300c02a0f05d9810240080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 666550512 1250 666549262 666549283
    0x20a090203093c032106030705010309021003111620180118021e03041b290702030d1106070212040302060a0201020c03070c03060b09270f0d02 63
    0x14800c681040005024091102c44a81e00e991211501c1d010030060a8400403c4648440350600081c0a840001d94468404000030b80031701c1c444008505040301407505052082d041141054107080380200580c9032620203c01503007440c500003802844d8001c452401e030103041c40340a078100100c0e9080b41400070520110003103286908000300417010f1f5904206540c050030300c0421720700d000a4010050042c8200301e54010300d141b500c0c0035140c195110001d51000440d0b4810070101d1a010062005000c00d24004815024030541014007031400c0c4000810110940c0c000b90741c104800c008210189489981550f0280d50b014003110550201806e02400c041c0800c8550b00c0940305003000200c07164400141000c4a008003401c03145060300f55024007610780c0c01100d4400944d0b4080040e0000c0113020402010344e24001c4c075034695810704525100003a01d0060440f50305c19542a824000c44044094048907081030750003000d95009005401305007000000c0c07000320168001c948103440003d4011940313040c075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 666551762 1250 666550512 666550531
    0x503180f030d170a0207050d030e011e1401290a0302190302073806030106120309030b010f0b090d020f0a0b0915030c2508030a1e270f020a090203 64
    0xb04c3e500c0018074401c07801001d601030220361041e1040c80e0520f01030b0380a050840c280030004580d29174501c0148507180c074880c4401e4032295403070000384440b003400c031400c0340500003082e00707840182c40110304601d2000d140b02d011080602c0001e0310404007402981250507152401c24100800d1443c1c8002a0003034014070320998926468107401140c00450504c180d2104103040c1c202c041005100c5182d000002c001004560559610030010031505000001b0050b02842036807030340449400c6280c82600050180d011882c030801007442813040d070079007805542c402c080541c2c0c1e0107050141c80c0001040002c652a807590800f04200000c50f2450903a00240f4a0b140207640c0d2a09080391401312200d40d100c00c5800c0040001300780030500c0e4108103402c1c604808000c0b42e0226640444640b00c4541903402135550300400b87d0380b4010960035807039103482c80222560f030709010412040c070042000a0015011002031140c942d000c0c41030100042c06c581c1d07a03603450f0040c00300110707181c550030007134025030055070362842c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 666553012 1250 666551762 666551807
    0x210a1218060203030106052214030d081b09040207060f06080f06040f140304090507050a0e010c0203100e0f06040c0905060a060e04020d0204090c090504180503180f030d 74
    0x54506030403894504035411a401145540e203840c10845040e005200e50381061005036030112241050280110058034001c00788201001d8608101445c1101e034101c003a0a0011020030849060060400ca1380685d01c2048201c0d039032803010300024020712442c003000300b4032450103103000291940c0d0703880401030354201c00466980483c02c07a072030342d0f451070101c80040c81780300d06001890020303480e110610440c021107421a0b0030036803152803401c03d450b0100c44000006d08042407032604039600c4000803441c0902130900000c403000360340209441d20700448040c1041915030020740c015000c2041a0f060440e02042a240942030a184c01e9002d28590302c18800070358107040c0411001d10303080f108441160450f407107150400820105110194200c081a1040b040e402c0c8000541c1e4a07031070040600c900115901d09050600740700c104130490710740840101d9110a50702880c03000038400000c0b100f2680424008480507280100014075410030281426014010480040b050035041881802e9400c1414a40300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 666554262 1250 666553012 666553037
    0x1020a0815010903050c310506040b090c030708040503090a080f060c0307020d0e01050f031e1b0d0e01060b1204170711010e01032403030306090209060306210a12 71
    0x481250f410700000d4500c0d001004c070f2800ca444e12840340281d07821260290f9100165a03000c810300010104c8540498503102c07403c101480c6040d1240b001800001c603240585030501400040050200801550901444c1404242881000c00035076003201001058001250746400419445408011b0310902510850020076000c0d4010b40c20b40b441041035500400c0c2107003000728112525031291040d40d0611808010a580e00c9006400443c4104043d11601c40d504000030300c6d503050044014058802c1031040d10101c0725100c1c82c4001c851211140401c0490301c1046146071600600d01c0740d01041013110001340300340803200300039000c4d4480c3c0d00a140340d08c03441c400c03442a2802c42c46060fa0080030030030a50503481680d8007a030342002d9a580107160000e60388419440d4108203800102d050708039841e441404104046c2c0c035010b46800b40450250950a200c9440d02043c007070b010181c5058032401301803100c03695500c5600c00d00c0700000b0b40407003200c1e40500d45050519903440d01140f45000940703401d1044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 666555512 1250 666554262 666554267
    0x60f11031e09012c011e021510080d03051e01051c06110304030c0203061008030418020d050114030c1503041101110102160b01051c080f131e1205030f07031101020a081501 75
    0x10b1b0000a013a0300a00440d60640e140c1000d9520300130502d50018121b010f021440120400407900e101c03c0c40e1703c0015060810200380c900c5030381d403103490048011a45005105076254a03000650070349607000c82081e82c4c03c40c5c3c07800c0cbd405001603001e801040007002c000c0105241c3e205030b110482600035000e681e040d440303002401d0118071146c0201f1100e940300f00800c2007910f0000d01c90004d002040071005061250444800043c0e900c03ea000d603048094030702818100b07107414001c0b684010300858040c1004900385074903c00c5030000400c041c01003000f140c4203030a540d024800b84058600784900031982e40c4240403a203125888c4e095801c2d586440030000120703d82c205805603940044003ca661600144151340ba80c0340c9074000394460a201c4000d102501c50120314505242c043c0c403030044048011a002c2400301003031003042c1d21910544000c0c441c0c24011500200444414440707048100da81c551090a090303d1081591000800d0703584005420b000c001c0d07020760558040c5500c0920400280c0d51030004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 666556762 1250 666555512 666555557
    0x3060108091b0919093207030809010302070c0e100e040b0a0c020f24060a1802090402041703030f0105011e08060f0307060f11031e09012c01 62
    0x614107640320b000200d841c918040000c66844407038009000704480b080c001c900c040e508845021145441403c0c80c0703039100f240d0415260085250044404444100f500d0880d031741d00c8840c440074150000014405059074401c3d0110340c8201d07042001001d400e03564250403143c2c0d03841140d490207041508200483e40d100c80a140a000b60342104003a411515084884c100070081d040141e001d501c504404220040e50510403160a43e00b400440d40351426591143d003c00036008210034460304c1c542c0018450500001c0300e030841c8a844800068a03200c5810100d4002c1c496900142c041079600c1400400504000004522500b03498054010590781c0d4401541e40d82070a0074500034094020000c482c41d60310034400c0b00d50000340107003e0041c6010100209042207042d400620000d200105008151500404280240c11102c8021807806428a00000e40310304d02c14058800540001441443d070384c49044140100c1c0c024043c1d072280300d104008000f000040c144241400328000d5034640c200710014105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 666558012 1250 666556762 666556783
    0x140c03071b111e0a06050d050a0501050315101e0815070e04020a030209100503041709150a050702030f010c1205060303070816060e012007050705090705070b04080306010809 76
    0x320030500500c6000f0800070080011040300003182d001480d19560340c0e88181070380142107a454880d9035900881d400c3c0700342d84004140544160420004000b640c80001c0c840b8402c242c080054003950302e910410120706c4820b680f00b030203100b00c2144042c28484c00700e02d0700c3c0c08a49440d4102c0320300000101e090202080210b4400011502c0b00248030810308040e0014000000c103840c005141c000d15800103100440d819051000080340802000104043c2c00c10b28005d09404500c0941405c0d140c0c1300044c211030321019841151000403558041041c00f54003650720542d03006090320002c151911859008003201e031180700000b04242410703d11400c00d807041d24010131014016510708400f0fa12a403000750b2210380c507501d4609a80308420007048942c465250705143c0b610020415000541c41c03155040c070300301603001c0312540411070b810001d04000342500132610140c450f03124076560a44141e0f21409042e00103440c0c8580d110403c010800c81c04011440f64000741ca4491017a210001c41c01d43c9c0c0c50742d520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 666559262 1250 666558012 666558023
    0xe070306090b150c030403020d060504020a0b04030b0703090c0323010c0f1b0218010909021512060928050603060a06050a2d17010515180406140c03071b 67
    0x3000c0222151000000e042c03010f018000c1780d01c1d0650304e9020451080e401c030b60956640e9601c03820720085180c042c050000070300311510300504141c11601d500c00c50460180004090640d103803c4601080b080c0c201d0b1400458128000001143c0f94040c00e402c150280d5130300180d00d5207460a502032041c098070b0034500d2403c07070356250300c6c2040070704032985c0c61040c40b07010a0b80e204061005429007001d61440c141e01074074040c2808201c19040d441445040d400101000302c2c4040c0c02d22451150420305070103280d0060707085030b843c065900c450107038010481a4041e280c400c1c42c0314110f0301150f400e843d003103a402401c09604890f8140c0e01e49400000b120030318018140e205c103100c0010056030300d15001d0651340c0300b4511203100407191031640501c1b03030118070fa01ca0100740c0d841c8030fa880300c08002841403551255011076603641e0707010b60300005003640d0240307591444200d40b1a0041014070a05070b214070145029070000d8400c03410300e060842601d0704200d44c8500000c0c80820b4806031640b03411104c01d621a07020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 666560512 1250 666559262 666559279
    0x12011509170c06030c04061205010308180f060d0212010b09010503041b0b070303090b0618062704030804020901080102070c06050c190804050a080a1a0414070e070306090b 75
    0x44880c0005840c03450400d05100e1120616803d80c0c40000850090003a10480d13540d681c50004082c1c90000015400c0031090f01d4140100040307072040b0110f8408070314414810039441d0440000403443c4c1080340c00300c1e4000701d000c00c10b49464011380d8000d046404041d180c140e566a603a000c0c0803801d110307440c011030000301c06201140015002840044405840f13071141e41c020340e26603030241c0107034101100540019448441c24020711000c100c2440d00000140c0e040409848001480c140304030b009012280180c845a25000c1c2121003041c0c0660312120119800e861420107040060011809485c207030720441c0000000200d44c032051086500d03c0c0e9000c000004c50b5860301d0030954058103e160a10910300907030b4090784002e0300030b0300c802c6a0544500003aa0b110f904003402c2c048105810340100704d45600c140791003004603610f100d102c2c1d0031170700d89000c03089580c0c0c486c58096044040f0304951445842860f8000c1413001c2c920010700d200d00d560741e408002c00c680c0da480300401c1e1417600a8168010721803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 666561762 1250 666560512 666560519
    0x15130b030c010806010219030f120b030a03111519050705160605060d060507090602070803280c020924010305040b150a2106060b030919170f12011509 66
    0x9a40144d40400140103807441f0410204090380e6200681c070088000503410101311102c281c000c43d4500c0742e241c01c048104501b00f200d001195484a15000c05828000b000462040c61a01003000040c0d00c1840d507007003016820001c81341c1c030b035540f000c0c8080f480a906001c00a0340640c407410a48046000d03000c5040c00030707407298031641e000340713005401d40e41c02c16203105014000c10118042c2c05d0041d030403070740c8540805203804402030038000c0c2c40d084112542c00800c20ac11900700d1055000035080c048030320007282e41c0c40766035040c2e4680b20600c000940000e011030400811600c061011002203289060001c3c1426130b00e40110100c0b6001c17200200ba9401c0c0c1404201540407058400c0c02400000c0e14a0008640f604410281d407000b80609503400700b501c64941c3e0803c0f20714010340d001060007505503411410851001c40d142c00080c1104000300034a0000b8406105c1c5106406610080c8110500c1d030310030701102100781030750000508949141541c1c000040307121400e00020f1031642155100d0406504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 666563012 1250 666561762 666561767
    0x5011b1809020304061b0f02060108030924070203071d01050411030c310305150903031b0904050a1a0f03060c0c010212010b0c0f06241815130b030c01 66
    0x180082e50010303541c2d204848070101c1030361001b88482c00341d201e0740c00c0500076420080c90600b058004e181c3c6604188119a190348407110710819a4010120f00204454410100c0d2018022a000650305120f03a40380025080040d04484400b40c402d003c40c071041d1383c0c035041807000f603810501c03000c407a5110420029a0000c400c00251280219045900818840340c030513541c42d1400c0d512003c0180340c40c4500410422004015402c46086010900b0046181c0020000c0d207030f0000902c01c1c02d118132078400b4030100f00000c41c01c48100c0ca400810812590421166110007040e42841005900901c004484118904024002114600180200b8049c0d5640081c5440341d081280d0f001d44a640900424404660040726540a8038140481c5c0d915030720260511441c088000c859603030150810428040c0300110040c610700617800c0480340591248c188008104100b019000c542c80c48a140c00c10321562400d012485c00d08040121000c2d00c50384100300400086400d0600601c0c3e00d5030111054034801d50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 666564262 1250 666563012 666563017
    0x313031b05100e0c04050108030301080106140a121712070905030a240609091101080c0a170601050c03191d0112050402031c0e0301180201050a0809030409060305011b180902 76
    0x10f940109581c2c22090701c4e404541914001c1c0c200120355000800140010746091280304014440034414144141110004c901c00d0340144c041d003075001090240c0b06040c040e5000c0407520007509182c05640c0c821b42202504503140b03041e690400010003003000001d4600c0c0005803d4a80ba030403070306e10710100c015603030880201d1101e21011a107064848400041c4d141d694420035112a0188011020440101c800102481801040002c60741c4051160451b11640112001d05010740380307008541c1a250800140c6043c0980070000c2c400d4400041d040d1030b10503250494400100c03441d01c0d002d506418009580a03440c0d912100180001c90121482c2c0405800e5003000e508070340058241c03280816651229a8600321500000020070703181c0c081140141000d10802d10040481c3e00c400f07803001d0031f55000805600c2948180820800854046030b0456810701c102c5005001c01c5404002156403480d055018004c0810401300500d401000e60380d80034028030350b035895030125500911703885040021440094 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 666565512 1250 666564262 666564281
    0x9060105091b030a150b07050a1e050a03122912030301150c022b0b010b0a0503040809120618070f0f1502010902031501050f010e0f01031802060313031b0510 69
    0x203990005d4001407904511009006403801440a05101c6100f410300320a10151400000e1a4203101e90508000c1000411301d23010540d0f052518440304030000540002404080958400d0f541d42c090310301500162403465800904015180c010600028444440d01c2e800b09100e804000c40e9010211200584251400c660041c030003085000309984110382c0c0c032081036450000024010364640c0b40300c1400f209110035401054105506850103000703000080843c000030b0001444114042400d403610b40e90442650900c514520403a1103924240091704091031484c03003903003128024804085881039041c500c040c141d542c00c02140c051985800f8000c1c114071200203002d011956240c01000050358140100b101c0b100e00c00c103101419505103420840540324807043c00b410320060b504000790030b803501500a201c4610900700040d60342499403092582c400d601c2e0009601920000c108940e03500c40d81c0c07483c1820340c060350742d5000320702c18480d240c401c007030f2000c8002e4515403003c01c440024089030b41204009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 666566762 1250 666565512 666565541
    0xa02031915110310170a02040c230414040b10180312050405041b080a0b030c130203090c0a03240b040c0c0b0a0c05041404021209060105091b030a 64
    0x6200c1007118080841c0c0080c81c40007000c0300008140182d075840003c1c040050501c1410842061034550303000d542c0c0309a0b21314000c0c007981d02d80304200034440c084c41c40300c0394005102840c1d1154290750300e41c800b40c50303105028400d070402d844404036101d41400d10500040a001500880b411904010203940c50840a00e018500c0d00c001c282c00702c009001000f580da090541911503545403424039041009844059102d5a8460524500c030750a980c2d2000145403c2850000c0018101b01c0c000040703420000b030f0710001504000005c83c030f0040c0540750340c0118881c1c004441522884c1c061601008a0660280b2024054121540744071184010414040702c40903080c01000480c4a004000726041e1880700d1504000b0800304081d4809000007900041c2d4400301c0d40e44100104032103000050b0440c001c42c028841d008c0210390b0004215255a41141d07400041300c0d02142103450144d81c401e070346423400d000d0180620f03080c030003041c4914540b1030390140c0d4002d17201d01c1606540c0c8e450084002030103881c240400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 666568012 1250 666566762 666566783
    0xf15210f030408010504110916030c051b072d0e130b0411100926010f060b0d0c0207051008091c030e06060616080d0204050a0902040303030e0a020319 66
    0x844400c10002400200000070001c030752490702d0704140c010f83c4101515240549240d4041108001000d2480042c0c07580500780050302e2892600200d40c140075a00380400500f0400ca104401c00600080a2003180d01c1100a54580c40c000b8013403c1d50174906406204404c0b01400301400116a4012400c5e40f11140482010600c0d1741501c0b0001551403e8809480c5842e80c4803e04085090070395540c00e14000c00e00348940501c0c034101e18015000a0200500101c21800c01c01c0861000290041c8038251200d02c024806540c403000d403032046500203120044054035200030303150080d001083e02c008890b4000c18401c040081c0403420340d0404001807900a49000c1c42c1d44813180c0070900710350400c203450f6036a0b0008404550110003850028090182c9200d058140810048a842d0a0700196a1584114803684501040f80c03400c01038003c98010b00d610814010f0301013000d040360b60180c0101c0380a80d0703007030000c4621910f8041e1210f44240c00a90150008052456000d001141c0d20710300c1403180b0f100c0c03031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 666569262 1250 666568012 666568033
    0x3120311030c03010303020d180b0d090b07080115080708060108090102120103031107091104032a18051e0f191e060e0903031b0415080f1521 62
    0x244541c000c88603200001c40100c0140180742c1d0410109901c54840e0911655000403218505111582c0d4415039500000010b1414410119600010340b44c40c4d10031f0209074035060920000c0e106107000d01810210b0702c0000c04080b02c65104c1c2c10b1f260b0080a00307441d84e0280703451306001110138010003820702c0c49035074081040c03018510b480e101c10741c000c50080d615551900f440303003aa82d00703102484d4441a4801e042c00c6240c62403803803800488044035400310301c106a01c00d08000340b200e039880308202d4501c00d503c0c4042c0000c0c1c00c00c3e403841005d0b00c0710380040200030940e104907a401c00c601221040f03e00510561000809420b103c1c4501c82c2c000003035000045004045002044c140c0d8900d1004009481007258041d24110300e50041001816507141a00c0080c606040215034038000140900c200100901400725005282e000700e0780a40501e01040d21265000c47c00a8800c00d0180e41000607902100002804401c2030803102c0f4501310001c12503000c4190004081d4540721052074166154003c104042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 666570512 1250 666569262 666569291
    0x130f1d07120f0b031009060623060d0b09130c0f0806070c0809060a03090b0901050708040308070903020a0806090d0f0215090709050f010303030f09020109030b13020a1706060613031203 81
    0x810604c0c07000001181c90301c0306c0c1c5000c6042e120140e105461000c1202001e4607890325208016080290541b00a42ca50700c44001a02c040d16507552041c0e0090040c00c1403001c01080010020f07111402071000c42e180c02e5948041102e07104051003076460342e40062000c1420341d88074250f0b5042d09801642c515003401c0d450310009540e5030041481001280d5200a90401c00002840665114940400170021468074000252405600600003800c0242c0440003480c902d001d8071003071001d980c0240001820070703200d05441d0b944d43c000b6120420700d0301c00c3ca42000302c61480f580d5041000345840c0d0160040110342c5200d01c00354900540709100b140210717100130604501c2d80c821a4860b5501c6800b181a651540c00c0c09012141c00d002c00401d03081c244580e0302d0150741c010000c031044a03440101d0440702d6407541c100081800000038029030100d44180c00058140203010b2a40910380030b101900d00c66210303a02006414405d007441460b0486200c603080011840d4445841011001401e0104485040b0201c2c2d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 666571762 1250 666570512 666570523
    0xe01200105011403070f030203030307200106030f060e0f0c0d0305043602030106080f090a060c03020c0c0f1305061201090f06050106180e0c130f1d07120f0b03 70
    0x42843c40c6402040c05141c0d01c0c0c100b0684008114000c0001e00036429a00400c0e12840010200014408460070344030030866405030030398035080c241d0300800155440340752424546542d08002d84001e8148032172070105c103a0110342c40c0401c4000c00002c101082d40d11060017040e8114180a400780300e020311000030151524501c00c00c070b01450b10158200d409591800d40000c112540030a54001e20510050242d00d4119808a4101e030704110480007559400035103134a0002005401480281080d0410800b1781d01500a426126844803d44041110540a209640704e5102c2c4161744407030703194690001c01c602540b00b10f030841c00181c4a8034941c803100c0c01c00ca00b5220018801c50b2206100c5107007205020a911503070b805069903280c2042c903030701c3c81a008051180b66028030311041d0913000100d80f00c085400100c0d100120b0a102104e20280c2d50710b48089803032824881c60300c444002c01614446801030311205c2d4401c105989407016801540307422040240914001c0442c0790303984014440c0f4a5508208 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 666573012 1250 666571762 666571769
    0x1110c010903030e0d140709060b0406480b15211603031d06030106020c010e040609090614010e06010206040b28020309070503070b161703070507050f0307030e0120010501 75
    0x201f150302e1504100e102120032a03808a00480010301c818480950300c20041c40408150100d600e40c02c240014400528014000500c001d10803501c40c0840c1212030700403010312290003407415843daa654081e4a41c0d403151050012076001d240c0392064601036800c01042034409a00070120745030f03101d10070b02d180340e030204030f800c1600458040d0a20486030480d0400320845400d090b1800d50455141440c069500c14541070000d05100c0314856100d0b02d51641d40c0a0002007400d060103000c07951072420002c2c000c1120310314040c45520328400100d10516201001d41c09100180c0c0103002d1990f031521845040040170300340120000002d07182d00c2d0182c07400004510541a2040c0040e0b41e4240000901d00c2d105681d4040b07800303078021903400c2050030f01000643c2e14900706011242284042e80c07070106e0030500041f426011841b0b0120601400540c41800742c081d0910030400c94440700000c20701c056590203614002000681c01e454191403039403003000071f402d80002d11a141120300526400290945000740c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 666574262 1250 666573012 666573053
    0x106050a120f052505010311090103050702120d0b09101a1305090705090315061e0f10020c01080f0606030606161523010f090b011806050901110c010903030e0d 70
    0x4c681d00c0340740c907881d504180204800d09040002840d42c282079440c074020b0300003e5040c10b41d11400941642e009200f251003414040d581070380d03201e03420450341d40100b880803007043c010000c04001504c2d07203604048400a0b00c010707581005090311100b107039164030390107404000241d0000c0c2c0740015803500c960740702d507020704003a440305070315420020103140c035002002e0175040d0442d500300305005254940c0b489600c0c1a1400f071150410b1983c82101064005c0703500000c3c1500a071151964000c030a9010540d0240c1036402d070795000702da84601d40200000001610b600b58080001c1002c60300503d069401001d1140c041c60f920740051100361600010060f80d4514104031a80300d19284100d1411500103081e4000e84c0359aa0240c0c0d4181103100c0400c4082d40940446d0316520843c0030120b038081d05040403034001d000b00c2c80c0b8034181c85503070080154009012040c041021941490002880895500345204060307540514103840d5450031100303a024060281d0304140b8565504000c50703121130381400f160301c070031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 666575512 1250 666574262 666574303
    0x210605040f020909180a17071412090d0f0602030406090b01270908090907030e010b01050405030a03030c142107030203060a120503190c050706020106050a120f05 71
    0x54244401d80300c0c45480000240e20400c9500c81a0b9100201650444000313148015502c0c10000c1441c41c4c44c0344904050720380046c102c1a4982d020f03401000f807140d0b5205118047c010141000500d0352190003005c103042c452804d000c85c0c161030600d003055030680c0f8010202c3e00902c0b8a00c0d15001d00301d900c2940e095804607215150710090003443c82429004220034581ca42c0040802190103400000d09420b0780030300340d299400e90741440448030030380e41707a148020005100c5060070880a0000c15448460201035402c0800d0350030198040ca0030b071011100041d0180c6410200c40c0d0b0100d000f449103041c203205000745650755549040b00f050150040302111501c2d50030100012007050549000240b401d802c0500402c01c120a903100d00803140221400c0c07900101d03181e5050710780309040d03005155000d003040c0302004070500c900790320050590b5203901a0054861407034452000b00c0c26100305000d13003900300420110810900900c00d80340c0888600410001104800c81e44d81c0170b00b00134034206808040710340b9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 666576762 1250 666575512 666575519
    0x27120501050c0313060e0a0210050a02190c090507031e0e062208030c07060504060501140a03120507060b0303040303090501080a0b03070320040e031309060f0b09012106 74
    0xd22481e07402c036108105032419440c00d0b03071034410900d02c0d1400090660b03854103042600c2e09410002c81b8006035005025882c15540703a00003d006030000031100f801841082d40040e08950401c1c4951b030425000f2002030340180c1861980006488064200810036565080001d005800c3c1071022a22109503140403444a03080461546000c0014100d0503000c0000030340904503032660a000309042d40d001d1040c0c2e8407562030204800f000e0044610107402c580c01c0c4010001000401d034002411790702c0e03682d10085505852000c0c040c581185000003000703808000315145607136004101802426104200210707014801801090854100c1e6200310045901040144419031304000e540e030344003103520720402503074442d540001e6a41599110280c01c2c464110401010480b0a0480652405000e007051015401d000707502e40c1d80790301c65030010260b82800f940210700007001e40503610498411044e078810190600b40300101c00d502600d00c0d80d06120945c05500d4407105c060020f2114081c40301d80c0000c81038034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 666578012 1250 666576762 666576773
    0x60a09090f02010e0d331116021503040516090209010c03030506060921011107080703050a030f09050601060e0a0f0b091206070201090201140f0d2f0d0b090106050a2712 74
    0x101c0c002004603c074108080d0382d1f80c0e81e000070295015044c0c040110901d00c100750002c00c0006800b402d42400c03100c0c0c00000c1009208000402009441d411031680103087e95981c100d1302240035110f82c4034009880b200000002c84d00c250000c940041d8000c0140e40b5180742a0000351203044004180306070f441c01030324003201c098800e1281c44004115aa07c0a290185560711141c1d184146200201030080100746015118032952210b8010b4403165000c110640281c18032503a518003d100d141c4c0000d00c0010005500e09120152000311904044c44088440c103103822141d1a412002c605500034542800700034146000300700440c0200a15000042e68814a0000500c00a0200c0c0311500740b42042121001e85110070080310003050000900080030144000c40c2c1018030019a20a5020031143d0710f0700d1914803c940c001c00030302001c004104060300d210300c240075610b8400d01c10031000c40c2090040510440c0100e4000c1c00c00030b03d4143e0407040c120310b0250f44803480016000392032400d0044030100304000c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 666579262 1250 666578012 666578093
    0x21020f011a0f01020a080d020f0f0c060619180905030d0606090f06030c1b060b0402040f0e06030f0a031425030f021507030905010f050708060a09090f02010e0d 70
    0x40a102400c407080d0076031681c46c224407800300f00c1041c1542c0058a01c22803800b0006450b12085003c0d0425621a101f05100d603803004203437201442541c0c0803a04800f030a01c6000701d2401c2398003a07405440c03122580b08084004110354101a00d0300d0204204202c000d041d076104100103406a511520300031070400104070f06240998201000b07240c580b210080d1516040b01c0d200c014209035a06201020740c1528180d00588014420030303400034000704001c03c406175074180000a682c2c0d00c6451000650f00c44081503074850040b04030758240e801c010301c1d05020900c241c440148903c8030a101c5843e00d0706405d0b81607285134081805000c800d1051610008040c0d11220700e48040e802da100900000c0600e0349218420b220142c98801890fa33581d501104102081d00101d64900201800b0041841c1056000d00851400c803030341c51041b25a84800b2449512522481c1389003908040c20003c10034669005542c00007020b0307140c0303500c0580d1440d01400500424500c440440901c2c0001d03010303013100100007100d203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 666580512 1250 666579262 666579289
    0x9050f0f13051006030e060a0e0a050105010b091002031e0306061306080103060509030a0e01051309050a05090f0607210209091e0109060b030c031506040807050a06030921020f011a 79
    0x5044c1200780e21b40080008201d0340229003000005500d400103034000c2d11700b05160078000c00e50350900000040308801c001c082c202d41c200070340303050b00303070510b0910126122311a8403c003a440d442200344082442d0340c0c480207183c1c01309001c4d212a2814104006100400e122544030300001140d120061081000030300480f500101034000450802d4015100517001d00d0100a070541081804911f40310100f01882101d8028541010308001d0345c10000c400c0e20150070308441c10041886010140300000320000340242c821080c0c2c1d66116041c0280d400710045603016515a10360958090203d040305540304908103020302e280034402e09035030b840700365080d4080c0416403051001d0ba280c090208018440f050480f544001b4003030029640b5a90202003d00c81113040818a40124010130081031000c0e0010300030041c2d80d030444041484964070001201038990351807005102c034001110103003449110441080d4010502d0041d00e015a40390f0440508407165001d8020810030300b04800311440c2000500c92090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 666581762 1250 666580512 666580517
    0x9010b0604050d121b4b02031e01090c081c120615052101060c0206090a05060f070c050a030203122809080f0a0309050f0f13051006 58
    0x8080c50080007500100141030064210001460712880c000d1146003080341c5200161001c2c0e03518a8541401c0440306c140f810440800400d13008180511203414000302c2d1002c500a000c0400000401d1031808611945a01240c051080a0f58489140321380852008003600171030001070412031605005c031700e0b841d0302c0c2d101081c00d80100e0351009040c40003001ea0303600c014240c02d0442034484001e4016000745582d41c04046901900141c501405030f00400900d0458405804e6055a144004e85104452020300c621004101c0e030700f0100d00141004c80107000c00e00c90003002004507682c1c580110307135182d00c240c100352001240059070000304091781f40f080c000b42c2810380c0d1403071407681160b0220f50b40e040c400d488401d48640100e00414205504200074110031081841e80b00c15030640180901201b119000d00415401800c5030300000002c00620252501c1d096900d002201e031804080c44142d442d940035180d00300700d4de0602001151118a08800b54003446040082c142c508041045201c89054104c5000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 666583012 1250 666581762 666581767
    0x308090d03060b0301060e2d01080705040e0105091806090706110313053006060108010608040b0601080a020909100501031b1d01090509090601060906020d091503090212030309010b06 80
    0x100780c2510003070340c1c1510020308101e84034002c0034001402c003240c0c40d4980d0811080b6506e84405484507200c81450230002038070b881005403a031b8002a500c130700481c012810a403044200400440c603065400c990042e02d10090703048880b030442c03001400c041c000c9805c0c0c0d01d5944105820440700350700048120078140404043d41c01d004042e101d4000c240c1880c41840d20030110000302c03500e00850303208401d1821014030180e030030360040242611340300c00040b103003d03010a19140001540b10f00850940348101d0b80200d44003080d42d1180c0040d6208100035007401c911aa00388410b50450321481440b030301031921010030b01005441e010005003a11141710544400402d9070701c421107182e40120b0703103824140c200c020460000e1454001241e15210076880140e220b250941448009080418028160341a99135006403840d1034540c02d0b65a403110502c030310700080440008010a9624070000c1d140ba80b61031401003001966500002d081c2154903020301940e400c00424028454070034850b25100340819917040b030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 666584262 1250 666583012 666583019
    0x1b1b0503120315010e0d060915020a051608160c09050c0a0f320c0105011502030747060a0312050319180c12022805030304030308090d0306 61
    0x4000c0c007001c3c088421686800000c064030360301a08050000e140c0c094442480c1c1069030074100c0203000c4030041501c00d4034031a41320a12a80c0c0c50300845c8c513105003d40380c5c6c42c640803181003910100c4440c2d0354181d4000c0824031240005001c05810f50a206000e0042800c042d400c08040f8001c860005d450102640380810104070601d801580c0485000080d0a22851010b010310b10040304011074032070114240c0100c440e0895109500c0050720403441030000822076a82c803450300207a426003981a4401591081c010007000803201040286841e15580210b040d0600f00d021404640300302c8403500c0507140040c2400c4030316091600310254003420031907012294924589a00800100c00c41140c7e041181c000002181854110741107540c0d42e07898001000012a2941c0705034070065990411075041000c0540054925003002220340c545800070310b20708440c801010b648080405264514848606010001482d990180003400045d406903c5042c46498115010750a259590b508d11043c146006001d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 666585512 1250 666584262 666584293
    0x3030f13080c010f020309011a030303060d050703060204060201320a0f0b09040302070f0b0f0d0c020f0a080310080613170f0403080d0b01050313121b1b0503 69
    0x8581026401410305681100340c1008001845603040640d401c0d803c1240318086040d10760b0055200307079149802045642c0310f4401901c1200c0b0454a1998598014004500c244c90700f41070802d01c46210354100d4018581c1c90340c442041e84c000b0b40c0700d500907035546e222080500300f04000a140c04262003080001d020141000d00e10403481c0900300c0107080d40d690741d0840b09250580d000386298500141001c0d00d624051030000c0d079540250048102c802400d00d80020012803440a0380c0e078207440081c1c01410410600110001001c14030500710444c400c182c0040030f1094180700c0d542d1014010f19120307a503072a180550550302c841c207910448855208030708120044699043e04408154410740c8440b904d019400251800c0c003403c45101c1d01c01d41300181c00410042d085009007101c102540c1c0c1404031880300d40c01555140411192011203a280364a01000510800040c0c1c5503903071a41050550100385070780d00d510310400c20a04076403007e0605000307c004001c0ca42441c0007400120010420844c481002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 666586762 1250 666585512 666585541
    0x60b07030f080601050702030a1212021e0706090c06030b0f0f06030a240f15020d0203160303090b010e0921071b0302031501090e011b0509130c0c03020f0303 69
    0xc40c0411120001240e0f0903032180c01100c00d2141c00400301d401c0b00071541800c01d420050b6002540116035031a4407582101140d00945090079028240c000c0c2d031000481104141c1c0d44005800c5030419692040000000d00790b1070a54080c03c000d99000809058900038440c00c0c0ca450700305c040c82407900540c80304c1c0b00e0f40c0e0b040072aa400b1106610220364080011512411401c44e82110101c3c03d2ba80a4081100d969070388900007161014480105207110900e8140d03202c00070b806804006800c10010341d40440325180a84c81424407a15000640c3c03c4079484562250000f070b0001428580f101e001d001c8041020441306003410105052040c0081000728402000c1c403a40100402d500c0b0400142440360000c045600000d580240036122180207421110154100c00d004101109150171910340d1880014030400401e5900084503006e0b400126809881d69002410416402110300c81c44c00180c0415004849001e0819250000045c129207400307410020580ca8217084c40c0c0c014020015902100c800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 666588012 1250 666586762 666586787
    0x61305010e1e0f0c0702120f16050d0807030f0e0301020409091a10120203100e01020c061b03010b0c1c0203090a05190302060a0c080c061504090314130e010810060b0703 74
    0x5a2985e2031160307101065124000f070903400c1c01c0340120781d0841300da0200442e502c141c40078004504d110003a1100b08105500c1003409014242603801c1c010302e00024090a502c070a0003040741003000d4840d1000c400282a6441074100d10380c0180c07038410210400c403d0070440e034900304081c030f101e0810340713041490f000900300d00c2e200b10165541130652074019034074144503a4401a0300144144070441200c0c200b41c3c042e62190401601c6031040400040c2e181d1415569800400808545585903910f4060b900d4220340014440000500400a141c044081c0c60407500001c0c1a4603000746403148801010000041896441107004a4011840c0c4d003800c1d00040030340d41500d0b07048a26644039908442c0840d101c80ca03c90303004283c6000041c400010038400982d8a01c15009600c03401d20681c2d004042c0070075228405c8008001c50034401d0f100200381c0b0440d000e41220080c41072480d10351641c40e0849501240c0aa00580d541d8011900a10b4080da07a4024310740940002805203280800a0350001c141440695 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 666589262 1250 666588012 666588031
    0x501050c19050a0e1017011211120606010807270905130c0302040e1608030403060614011205090316030e09071119020d120f030e0606030a0803061305010e1e0f 70
    0x2404085038a00619201c250382c2c0559200681c1b80d80c64448402d03106000900965428034000182019807a007040700c0d0a2004a01c00580300c2905d64030015264200041d0282042c0b040700c003c1a50035140d00c18502c0405174292003142d10003841c007044881100d10207806046135603a10500e080100e9511909a4121781d03064400240050a5150060401c82c000c80003501100c1c0d0007000244102000000e801900d020b00f008000003551400c0c4104100940848213000c2042d807440c244000c032065000340d9102c0760413029203103031806000401400700c00e1190f0807004200c25241d14096402c1044d405940940d55041407200c0d00410041596203140d2080030100e1800c031124982c0854a40b0101c01c1c003669400040b00000b04002c07035001d04003003c4c20b10004002031408079083c507010030010358a0b01801d000fa02a201c817140640312009664002001e19803ca1600e100381d80103982c2c203104290092540d207003414818200b040f082050f0003d8484502c2c401d06886090160003a1225400c40e040382085 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 666590512 1250 666589262 666589279
    0x610050f0903030a110111070f061a1302130f0b03162a03080f0c0913020f0315030d0201061404020a031b08010603110705030901030203070c0501050c19050a0e 70
    0x280002040c51141d112010780600010828500458200140e90101c2c005174009210080051502140500424030050420840b840060340802c000b0f0740400e090703442802c229a155104030b00031811221808228401903640040c1e051a400350540380d160191204a4a0303100d094506103400003030340406803520229032440d94080d9415130040441008406a03c507455914109941d803040c008180060240d010501d99400035000d1903003000580e10580c1000b030018200240d80d030a00904014101d0f6404900346c0c00c2043d003040c0d07029440554811054054802140904034017070504040450019109580c1441018049122850301c103024600b4103940043e281c43e4161001c40c0585100220381504012640c4a54521640046907030305075420350703c017481000c41e8141c00e04802e05c1510700c0642141c00c04e00c601101c542c4a90000c40e0040c03c6490000c5080005890307480c00c4175010b0381c110092407000216052000a211a441d440108a0914500f810000c180241c00c8030302c0c80d503d00b442401036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 666591762 1250 666590512 666590527
    0x50f250918020609120d0804061107120f14070f0309120b062b11100f0905100504030b010602070515040312081906080a14030a050706050910020a02010c09050405061005 74
    0x50305411010260005c084400325105480003904c099011b480907529207007011030760701c0031000300000c0b0b0f411603502c18034110542c3c5031440216640c580009003076040083c807103d2485d50111200103414141d0044840700002c05603440d02034800316031944a030307a0204222120b0004150401c10840c0d000b9001e451030511001403d901405102c0e03a008040d01c1c0c8a0007020407018840500080c628410042da20f4041400300c4401c2500c1603c550301184d80041c1c1003035401c0c071550138540394080e00d86003170342480382c101034595450381741d0b800c001d81002006911200d400c100f82c0c035010342c15000501d03800c8101403801d829a16040090410103006c0c030180541c0c007011a9901480b41c16142102d4140380c020072030591224900c5855000164003035900407544a4808440f01000c81114542074903911918a00b03122603988201802005041d6501d0740220301c2544240e410034002000320104550001417144880070002d0005c100c0b40d040907004038030f800104010354032205202c000f02b0324142011600c9400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 666593012 1250 666591762 666591769
    0x81c0b011e2c0103060b03010f0303110a0606240c020f090405100f0b031e0d0f0c0506040303060617090d0c0c050d050c091b0f07050f250918020609 65
    0x18a140c09201484444400c1160442000b5021119680c241d800740101e56aa880e000c441e40403e0144020341c81c90b0301c00400001e070081035460000b40703404082e103000400342c0c2c95500031156103a0000401c0662003c080c1100c40748800404940901c1c0d0601000d401c0b940d401040c424140d0500181c000c44001000ca02407040070048020a0b010040c001c1c000700c40b89080d03440c0582504540070307010b4840d4007a04004d503007280070078019070b8800c44d0007040840c1c01c0c02c4040320120000211641485150400d800100b001842a00e1042d406078902064991911400900d0040c103c1441c18009000c041400f0300071501050440b0020040d02d894010304d2511304052440c290264050f17035210162104c0704c0100701000c00e40304409441110603265664038102645410203d0b028585a0060700b0058141030800c0034001e41103050062049170125605a9011481c000d1003240740120303ca0501c0300600154881004240a80110300b401d00203904441041c001c0f41c606410000c0c41088003286040c031130384 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 666594262 1250 666593012 666593027
    0x60a150b030603010f05010b091309050d0f09150e131419060b0d0605040c02030406090e1b16050d0c05070902030c090303030109050a15030b0a27081c0b011e 69
    0x1761401080040d03596a1803858030a6100e50072160203002c000a404c8122680da100d4a032116030007001400310f05a02c0754003214283c00d00d54129060108015010916024031413400c9a03190386030300c03200c2e101210101080301682811700040309184c180300b018545418045041c030b4200701080c010005081e0014032500140c64550487c154140000c100c0d81350080040d086601103800030307a8100a40710710144126128811401803c0c0400c0503e0f030108520040b004c5402d520041a5030710040301e40100c0501c1c20161b1204020114012035210050b050000034848c18204072510300f060300f51080207980e0191100214030a400c3c00c9540400017074081c1000304220b4822860040540341c0d2503845070b042a00809080c0c40f05801249821268800701105029080660360000300b1600d15030f983ca00c0010160201641c524010b07002c0f240c1e94041c4c03d0050a034400118458160551280340000c20154030354158202c50041c1d0341000c104801031f98004813009818103c01040c07020002c4940421384400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 666595512 1250 666594262 666594281
    0x30f0b031203060f19230901091d031e0706090c080703031106070518130e0d030f1109010c0503130b04050f010c08161109040302030408060a150b03060301 68
    0x50081d0708941201016040c029031241074201e0341a00001c040342c09002c03111040c081804000b0460345400d004441c806005100c078009944030704e6411110510214829110a0740319450030358850585001d10282c0c801e10140c8030f000c3c0d800550074041400d601c0e4440c142c40c4100220541000030313840301804226044901c2c1c16800c1200d640b9820303503c842d00740d0380700d22612040e00040c41008004020041c0071418a004660965072a4180b801c0c9591001c0400703524881c181d402051280281c0114a00e409020704d8900701e5805410528141c6d20090b068601c14003c481c01c82c0d2502403920140c10220781960180b03d420305e000718100d41c0d60b180c02c504d10710508002807075500011600054000031607004000350345068510004020b01d490054a1014010000804180b014481d00c0c0b896401c41c4520940c09010b6845e000701803000f1000b2072201c010070750b026070068000143c18070402d00c08205080c2c000070300c88400c0000d9a80d020845495100600440c03079002000408a480e170b69094000c4d000c0c0d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 666596762 1250 666595512 666595519
    0x150c0b010303020f060907030b04080d0b13020306040b0a030b071412160e040b09040303110f0d090201170903070f0602091306170c0108040f0f080705160b090d03030f0b 74
    0x95071070303040c041e6076040a0000b103465031040500050030203402180410480ba40310507664610313200d40d0b54401990300701108501010b0398401145225039101030908070a05c07403801340184e89040c0041440151840b0010700c0740208c1400000304001185001c256a01160610f022010880e010703d00d50002e01c0391010081800300300200b030042c0081d01564010300801e040d02d0b030101707030303007081c8240808d076007440e080254051200c0c4002004030f800781e006003406040e90a02c80340780c0242500c2c882e1090b0012010015290f60b038800590841d6000010300201c4203420100c0c50452408005690740e910451138000c021981c3d006a00b01000000e03010b40d081c5910050504555100c1d03021344100504152048544103030b8105000603058901042c00d4450801c10ba503070726840e0b640ca48442c18803035840202140c00f81c21040c1540c0c04200000d024159080c0310f00040c00704101c0c095043c015040c20b030740160761b0806040080301501d9980c0707511100001d600d8140400c0c3c104810100100404100c200c41d5003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 666598012 1250 666596762 666596783
    0x328020607300e010c121419020703150b060d0209030102070c0305100c030506030c0103090f050312090105070219030f0306260106170c2b0605011d090601150c 70
    0x12640346014020150401594500789100824401140d1410142c44050b0400304041d98440c151880b840080d940094034030f08881c0f50000951001303450b0230303d03121001c0040e0441c07502803040114003e41c607041c03100302140520101c01c149002030600d226400000400d16400101c622040d18203405840546030404172200003940d5a00b440d540b1441c0c00903242181c00c0c5016074202000c0d00901c101400703a000076000300914000c202c0150018024510b040c1c2e0104040120307000021010801052000000b442000c400d080005403a400d4801c003410040564101405510310104084031085902d0341501e800000d1320703101c0405900138850b0741c00085111342c840c00780347e003d103d003030080e07a200030102030007001440d50742c42c098440104642c200354071681120081944070b00e008090311125020046c4095045400101c045802614070351041b1a1641c4900c010040404101d10354000c0552014803c030091802c0218a074440e181401446041e14800e1540c880a62161000c00310321039124881c4103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 666599262 1250 666598012 666598073
    0xf0318030f0806010c11060c070305161d060f0f0616030e01110a02031e0f0102070f060e1504081608070803040203060c1314060c0d09050328020607 65
    0x1040281c1094403540030407402404141c25500c606010034030140c11950a6480252000401c130081d030005280004d41c0c46034100c003102103142440004d424045d003013007102e0400d26220152040c420350b1001124401c1d240e6041058540301c0f0400200c01100c21209031540b0b881c41c80003e42c003030007a00c1d25107a00244095101301050b40141c449000d4446c2600c07038500c0380c401c01001650b42c44200308000d4168001665480003064405402c01c8500500403e545107007500d00511030880e001060180c0340759400c2d400c2c000038000c039885449141c040c80000b4042444da01000c140c007640d0040e10040c0450b0300003d504010300c10511524150395030000d00160780c1c01036400d040d075a0703070070554081c2c0c460301400340801d01c106449000c4404541c040550b00300c00034940700301f40f603581c41441107058004600300408038a1920034801022202020384580c59440c1c140410305103002010903462050080403103285009260400340f015441c5d5040300c6a69584211b0700d400c0303500942d18021071694561700007248 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 666600512 1250 666599262 666599267
    0x30414010c210e10050406060806070806010f0f0c0f0302071d060406290a02070b0307020109060608240c070602030429060a091503150c1e0207060f031803 68
    0x80c004500c50115000080b05440c10210803140601c820b003003e940000000c0c203100c0d00316000903078003070b02800000683e503544150b554100407080301c200300040c1d200310400c902580c203c0711014008610b442d003141170301040000504480f09164002d000c1c00b40c0e640c4a402010710800440c0003621004140040c68128010201c2c00888140e580610039410403a0200320b04811090303149103404902000c007810580b0080c03035809640030b8001082180184507001ca45003201c140218000d0403070f0340c0000f0782c00300720707050100031a012034001300c0b0541c104044040441000d103103811b44440501804401e15241c4069044452082d420014061070000c403c000038019844007000003814030100717618087c0340020601c0088442122180d92003192041d0500c0303589440c0d407204444e6400400440180c13030f269103808212880d43d02c0110002500c0714428804194824000c0030000e030955020003d40b40c604cac6c0080e4503015280145000c10400b8007080e490390380700303400180c43d030741c000c0c0385440e040301460600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 666601762 1250 666600512 666600527
    0x806030f1b2d0111010609061d090705010e33131a030a0b0402120a0b0406060806031525021011130e06030109061812050a0203030c030414010c 63
    0xd840b030b600700d0106480c900088068004002da0300c0041c0846807141c14010b444a403d4021030741032540d690500401c840c6514400d4a000d040b07114046141540c0341c1401c250f04001c020302a5800b81c00c0800100840d0b42c1082d841700c042d80003141d20304060440c0b5400b030b09042005491950010b11840790040380d46003601c0c020310050950706850301e80c0075240c504004900c00e14591581d4240d500b040060f10a22140e0301400c440c140041016107808040b010510301800180c0720600c040b0398410107080700d40b0f45403140200500a50070241344510b483c5e000130781c4610400041d103040c1581c3d0380c001290704a003500d81d01412620403c0c084000d400c3ca46009564904074a01d20084a00e4024404c4000500800303a9000001c0d05204011060400e216010700c510090803040e019920b80c0c603d00e001810354001c100c1200b040c0c843d500e00400c145e061891403c13040d4898101400000c11003101041d40c04000c982d40b141c80c241202d07540b6121483e044400c81400001040e003546410411201c7c954000302 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 666603012 1250 666601762 666601813
    0xe2a0406080108061b0d06030803041407090903020303061c080a031406060408211309051e0f0f04050a020604181b05070f02041107030903051009120806030f 69
    0x2614540c076030f220b09070240d503003509448440019407000742c0941940040c80c000c00403000480c5010078625900e50b60450603801c10b41d822219054645109c2d202080c003001800c00900100c1010301c0b83c1c80c5a924042d4603072001900e01400f0b84a04c403803080c0005800000106a40d6110009540c1e81e0390280000300180145605400700f07401c0240800c0c00c0d8a40b002c20b4805032010760707014060000c8001014208034064100708030b0150000c1c4104401e900714001d404009000c2280b01103000d29211020040920181500386640000902481065518001c01a60200b0050b0300d034091510741d42002807901c16030410080d07014034001404151405d03011540919161000000d001d141c4c241032001c031100c520207002c4d43c005035050040e8004170b40c00d9400820b14a00103000059000080003201032544e000c40404d60206204400804c1080020454030040e8140307800c0806c2207521030340d90301001c604104402820403035808081842a0350510070303058480071100480e07001c0d10000c04c840110120004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 666604262 1250 666603012 666603017
    0x11e020c12010c0c111207060c0b2d1f0801021809040b06060d060504090f120f23040f0306020a09060e0607020d030201020c16140307031203110c0d0507061a0a0e2a0406 74
    0x404292215152040c0c3e110410501440401c128107641464801040040044034101600713640768070b04040cc80f50307441c054132600d0005070361800c03400c040d040b6104058041d01d0285501d24200f0000c03500301c5a11540011b01150483c3c0e079010901d440c40050012600800d6009140101180411443d810098070302c034410203031070301d0003542d1440540303066410001c00404104000e46101109110300e20741013980c81c94042c1c1e103081503110403030245010b11680084883c1507000904a01103034000008400500d40340c54440304018007400406c0e424022403100901a08000c00410200341c002c2d0143c61b440d03900c9000b1280860058054155885c2d2180304800d11515191880c10080c100401d00e0019a50006da04020600345a50300318010041400c100e040b03043c080c40032100020050110038844c08880c0e4805864010354281081120440021291362031442e4541e00314649901c6132900447d0586100d000713540d074032420203140091030781d07843e40d18104c07412000b07031a80c1c00a100a08241c54059 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 666605512 1250 666604262 666604283
    0x50622091e0516020c310f0b0a0305120715050406090606080d0c021c08070c0618032604151d01111b011e020c12010c0c111207060c 58
    0x4543c01204155810507010040c2c0203051842000c2c1024a40303506000000d103010038007250013082109019800c511440c11458682505151015544c05000d034403071421500b00c6d0020f855941c459580b22003c030301803501c125011030b0311030a008903442200e4900c410104244032a10305840c02c3d400030103c0903000c940152502d00007160700c140004509030180c88548a100079000c2a40802030b040700b600d80c003095541040c0c50540000b60610020340240d5102d4070a00c003880707003031940242400d1103000c1c081d1107001000c03808002043e8201d001650004015441a02021203281102d90a200741d40245680000b0f40d04030b007400030f6005030705280030144107a508503420140b000454129403606582403440d401901d03500e0762154050b807010720340d410505060300e100e84103008880300d001c20480b0034800361300481410156810100d403d405000d285000800c6411020000a041d81c61243ca010707000c0303100501c1d100215252038174101038480c48142110280b944e10400101000d0000700c1c12240b01e50003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 666606762 1250 666605512 666605521
    0x5030424140313110607020d080a080124050c0a08130612020c030703050f070204050709140108010602120a051204050607140a0801050d050a02090408091801050622091e05 75
    0xe1003030b6070048011a000000b041d00c182c80714101c201c8540100c5900202c03c004181c0143d1300c40586500e4544100009900d50080d010003a0022805a0000b00c15030071140002040414080102c0c4c88900141010345d112044c11103214501403860308002c02150001030a008007248035900303201218059980d52403c0c088002a20301a070041c614003580c140c3c0140036540019000300060502c0d0007501c000c09050100d141c00090641384c00399024800303d107290030180500c0c0001c942d100050003080c04d002055525015009644903445904491480d002041c144189480f440c1150417116401e00120b140341450704140e510307824182d8101c3c000c10387d15030042500503265001c1d2000240c1986540b5038507803070401449202c40b401c00d03084980d4090a241440145ea40041850042d4040c2c0802d41d113451151081c004180d9030801100d100905d0000100728a90700c48089a00c48204840d045050744040a20b541c0008103d412445026040c100c4ca0400c05031800c10043e000117500d0300900064a4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 666608012 1250 666606762 666606797
    0xf060708100b0f09060a022b0e040915050601090503010f1b1805090a02040503060f0f09010e190602070506090309011818110f0a021506040501080601030f05030424 72
    0x140d003020700a03c1c9420301400300e003854040b024010346805401512218080c51600c00c103c40240c0c001d1013010f00d1034225804403168000040b000c580ca094404000002041c1c03100203e000020012100c116212000104140d01c103800b090020300025000744440d10100c0054005449111034000b0081e101c074019040b140c0c0f14032211554036841c082075555150402d0709101c400345005004400035502000001401c1e2800c1040c103101c0c2e40c0f0b02c2c120284505040c14030500c40303280900202d071103078180240072000540200c0d04007544e04080744c6000359180346241810103801074144c06000da0050004110b80c1d954003100400b1341e140241d8510f2502c2c50030b42d100b40b4004c0c2c4140203000c1d28405510568052561a521070901c0041016205d814174844401c0420a0741c0500040401604120580d80b11038460364100ca4020108513001d002c07e41c1040c85003075580005100181c003482215a0040a11400780b085070060200150000b240841c60003840c240c0e10000303080381002620251030950b00300c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 666609262 1250 666608012 666608017
    0x220812040509010e1f0605070302010f1505061c05090d0e0105030f0a090c03060203010b0d060506070f021c21080f01231201140f0c070203030a030c020f060708100b 72
    0x190014880c0b5001d90900d6a1410b80d0100288210601c0700102e5001d00204202c40304000141910755550343c2e5030b0712a14000382526485420550b1041c00c040c15050841e0f500d05482007500c5c01500c0041c0c4502c04c1c6c0d88588810010b2464850b50149000300b4019180300114030702400d041c00b9200d4a86c441011401180c545c4030407144a01d0580d00356003c2564155180c00c83c4081038003071110150f01c5a00c1c0c0e110101240c2c800c0c0d00126183c40c00103407010300103416010703060041c281120340382e080c00400c0e00c44610360091000000d1180f05002190b200002c000301c90445055005080c2001c580c4861480c80d0031109a002d100c8040b42400b400244a06e09040855041c4c0d82d02c10611502c0000115040303031290780403140d0700e6000f00e50b168286032144c130900c40c0c04602c20702c408104103603040c13209151300b080001424080c0745c503c080050070b0150302c001044403d0801180350009070101041c804904114a54103d16075501a610500a1084c2d001410034001c0001813030340d9000a5950b00e5448c141e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 666610512 1250 666609262 666609269
    0x1502060c0a081509070e01030e120405040903050418060302130506180603030f1207090806070914060405090a05040204050a150b0a0e06030a1a01081e07030222081204 73
    0x48001c000c1d803000c0c03501c620212a00490304804012003140c042d800a0000c003002c503801c0000030105c030200702031503915019811510341d06001900b8214840104507416105a01a241c0255102c4030114200340c07240d02158020042d04a02c2603404001c41042c0010b4005844168895424100720f03050046c068851980078503401400304000c000c54440c80c0d52000001444594540800d1018024452105004103844014002c412200e8508424003401d1a0044d403c8005a94001e07020400c0311604030708030105444107005000440d406020004040d07114a801aa4000c452041840f840580d01e400c9540264800c503801d1010b69aa281840f0445881d0503800072104d0b83d0400030811190380030003c1c0907200092a1003990184904046806648251600c02295a681701440ca85c3c001c401102e0694003c240f8001c1002c9c2444811703004050141d0b26040800c03061900407446480c01f0f98110792802156590140103000320b18a02039082600d84034240560080540e41c0001094080c01c840c10ba = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 666611762 1250 666610512 666610531
    0x105010810020c210903010e06010e0c0a09180b0604030b04060b0f06040506090402041d0414152409072d0206192a030f06180c0210060b04150206 64
    0x10340d070008410792280130300020140c00141000142890340342030084422000d41b0340020840c0c1e5150003003159882c40b004040b07041008041c400d6030b03482588500b101c0c088a0003082c83c00c60302c0c4401200d82d0001c2901e0149158404800100001007200c7d01c10300301d12560054508018103501c0106201d120031541c440f09600c820100014001c91030250054900e442002c1c00050800e40c9503580060460944064031b80314620f0081040104440350001d84244030034440901480f1030503d44e01681c500000d8a0300f041420000100790741c115140b180c900003107000a040007035600707003180042d2a080e440320701c0e055804030034001120700c4050780800008001c102e078001c0259969503e07084804a400521b035500480c0c86911a092800000306107030502d0100c100d07500501c1311070300c402030304444071500305803802801c1850820952824404015080c50304038804070728007610b400e00f01d040100710b803c41031000e850054003061074080000944103488011000c01e401841484050703988044c102e81d407091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 666613012 1250 666611762 666611773
    0xa0305042c0a06150e1c1415011e030b040f06090c0e0601020111040b12090f0706030b010e041407080a020f07080408242703221a0403080c0712050105010810020c 71
    0x91800107540e030000c18901030031484030002031038407c450503c2005080c6c0d242c40440c13540148000070b007a0720201048403401100c980103a02d196521881d1170350060002d401c03000b00810020500c41917400084800740d1100f100714440c0c0e103901c2a40c0b4080c00c00d42d8820700541c640001c0f500031504000885083d03d1002003c2401c200700606001d030901d5000782000340c14003c13201100c0c100e4030100120006003c0030f481c00303d540360141c13000504080505801c144101d013005007030001d242c0d02d9600c003500400c1900d00080780f543c480740340300003900c50b880c40382d0000300d0001000701c240300300e01c03020b03109460811060f2800130401e101c03092034110309060400c0c141d40c406004a0054507050350782c4495581c20a2403100c0031203405902a055410291214501c024070407507042e4134081a070341c03c4010340a40300800f84801524040032096018900004015910000e03080d0a81c3c602040a03500900800340a40b401020341e01c1c001d40a042c085c411007040d0b21419015981c040d6aa000b0b481178400108002c19 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 666614262 1250 666613012 666613039
    0x603050304090b0a05060d06141804030309050321010e0a020310140a052107060206071409030c1c05010e0109031403040f02130213080a0305042c0a06150e 68
    0x40101244840a130344805912400921601e070700d405440c285541e1000040d0181ca0914045240e0104440c1c041c4603680b80000910020246090070350044d400d4034000a1102c00b40c0b03002880d600c0749100340c84c055a8116503000c000201c1ca42840e06a4080b04441169a255030764a40c0c01d0307010903135502124141c070300b0040c8221f404101a110070003000502c03243c000340c0c0d81c030b0108141d0906007140c50241101407880c2c5400c0f0b01308204200080c500742c4010301351071610000060822840040301c1c8000780001a148641e640d04120f000000f1000625080544e040080806409203c60310100c40950078180c1d1402456418460600c0032034141d00c1d80d901e41c1e42d1030040048254402070003219040d046403450005600d41e82c41952039150880d00050f920010000c0f5003c003440c0940c40880c10b0b601003009080002c1d07000c800c3e00c0c22a48081804055007080c550110340c410130400800fa0700003070240411001050b11b41280c0c1c116204100e40300301380c2c81e90b200c0031901000180c0c5c40c59000704003a0303c0c02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 666615512 1250 666614262 666614279
    0x50714130e07061101140c041e0305070b07240516090e010e270c010207090b15070c03080c01020415112107050a05070e071d060d2a080a0603050304 65
    0x30301001d1041000090a102d4130081c086d6240c40585c0e040842c0540420240030015022052200031041c042e06c0355403440c5196541a940c0040e4012502015400300d084020005184030000a0303044488581c0d80180d1010740321b500411003100c0551896175614089072080e80140f154500b920311066030680c2c141c5c00c0401c080c0d0300040250840742480c1e224440403107a00070b00d60a02d0410070300000502020032900c0002494040c694200084192501c090301d545980c840603034440b44120b44001c942c89003240d061038100c075007496001909c481c0001400d8401010107500030010303203c44403040009100152400c4a40c2080c40e024181d19602543c001042282240b016002d20610f80100344d00c0c00025030307a19814889502e4040b9265030241c3c609000640b84c0201090b03120f811481c2c08039111100900c034140c2d074000b0f84c52032030007800e0009899000c1c11176504410144680e03115a01d150301010000100800c05103914540010408070102c3d050b03407840d004040032241c10100460a00d814402503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 666616762 1250 666615512 666615527
    0x30305060117040f0615050a150e0312090301050f16030f111317060403120207050312150918030414180f1605070b04120c050714130e0706 61
    0x410303041c801c420925491030006100da05100f14850070800e80712076441c0c50298107603048441c0001581401400a001d513845440c0a801202c03c200050004668180c6080d102e80d1207071114079405004400c2d42c0d1000250b54001800e5900c01034000b001580c0da0005d0007914010305039401c1008400306403603040c486109801580381c4005032240000c848072001108281ca41c000111184000780009081200c8000d0180503c1c060131004064038183ca407031380e0300500382c000020300b00b9195a800b05200d02442400c0041c1c4420300c5005810100900b000101084581065601141304241c40f10005600c12074096a03604a611540d00450070f142c240100c004201445400c42d03500301112003103c01c040080c0d064418010720380e05031410903d080c04140d544056040704803074814414100440c200041400a21607030064000704200c5501300200c0045405525a640c0940140314680001c2480104800001d4041a044070044030b030800102014064800004900030641c00018040004500490b803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 666618012 1250 666616762 666616771
    0x10050c16170315010e04050c030403050a02030d06060c0b0603010614040b0f0d1a0c12041709120d020c09010e0103030305040201180608011404050906310b0708180a030305 75
    0x901401d003440d100c0e5100c12a00200e50382031903d20340c06188000c40d604528103031010013055400784510301e090a83c1440c5448050030060410030002150041e40d842442680e08290303e40405201d403c1da209001068899080010b542c00845580403d06c82e2a0520a00b02219503d5048544080c00081003000902c10445e1136504080051560b81d219074891300c11241c124132036040902c5500300071440303178036003403008024110800c0c0c02c00a10288140c010700d4070340d205510030903200d40485d024107041c50500804000b2a001301440100e100c8071803010400108640380e0ba403c0390042400e03c420424050028818078881020b200c006102180c400d400690b4401d0042c1030400e10b100900b001c1e01c0841c502ea9000000058694006200c415840110321a0708103089030b080c003403401c00c03415080e110035000c1e00c02040c0d0702c055101101540224400b030303104035602f1103084400003000d04240d22008022a0700c500081c5c10f02c00040e822203d11804203108520000041051005550301a001414041d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 666619262 1250 666618012 666618023
    0x140903030d110c0c01080106050906070c030b0405150a0216020d060612120212030f240402070303050f0c0c3703030c0f110d200105011710050c16 64
    0x10196554200b4090042c000815280940c2d540900800b103074103102d00b1030a41810010345800401c15260b1140c150b60034220200c414950312a191700d40403039a01c070030380d00090121142c40100003d005021465605015001940d50304558604601310100c0c412100c14081145640d040103015042c000113803038500d4424000090030b15207a00320100154080841124884540b22002400b10381c14412649150048902c460031801c0c51071710800160030040c00c03041c005803e00b2031081c0d80d0041c58014020b40101034800c55503050a400c0c02805040c00300d5040703216520b100040340139550325004450903403141201a00740788440c19020030190081d00e4869040300c01202c0341100c0d403030b50201c914140c80e200b41c40008442c2000f12010307180b241c84c080c28100340042d06488029820700884c0c4100800304901e000c40c003112046e2110200101c602c1c840c0b19a641c03030880045540b4110b103030403000000c81a8100e4981210001801054505c00c4620a81c04c80d0b0a108510480603c85901300020740302e40d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 666620512 1250 666619262 666619267
    0xf060f09081603080c01060f2c0114040507030b0603070509030f030307140a021002120402030c0427020118080d09120c0e0402120a08091212090603060d0b0129090114090303 76
    0x101840c241c1090940c01044200d40c18040f807049d1568400140441d01000d0030318a0302940c0341c401c0c0c0c104040c3e4002043e5000d1902d880000d010300c5c0c8650301814034804020a4161070b0b01f84040c0040060f008040b880d4000c0c803030508181708080d4004296407041e04144e95010382001240e01c10302e520b4000c61044003d40c4940c1410404620050015140303040f1214a002001c3c50540109450a802c03031428a0041d450310507a00910004c00c0c582d034000002c10542a900d860702ca1004840c00250200d6041a803911a800800d011001060040030440750b03589410800d0385074085d00075040c4c0c0402d07000349a0740e007a900c20444008250005503200b80014000b071540000340000c68104024800c00b100c4440000555850741e00d02840910b11004c03c4200500001e1074954018400c0e100b507100c094030481e40800001e03a01c0da15403038481d8840b41e00038004813055a4408151072180a000c40034040404140c5052504100b03040944000394016550034100c02e020104800c22a401052034a0b01030008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 666621762 1250 666620512 666620519
    0x41b0c0309030f0f0606061e0302180607050703060c0503090c0103090305120f070801120b04020f060403080a030605041a1c0c171006060305060603010911040f060f09081603080c0106 80
    0xc070303e0300310003642c0070b0404402040c0484c50080300721845504003406000e007980b0101020a141c07407445244044a040059841d18803a59480c05189451052940f0240010390f143c10840f003c40d1050489210700028800320480500c20341c0e040c02f04545601050380140700c114055031098010001e454000d0078801d203030a5082000c00780c8103000703c0b101051500c8642c140f01d0780d9588481d03a2401000d124101840d0a01c455598444598014201034441c41f13030030400717484c248d80321012030b00115071142000e035503508501c0c00540030309a80e10071184600c0c0340c074514249003181c444451014220040417011045a07007030650712461003400d010381d00001c14420103c0c0c1c02d52001000200c26190360b006000754842083d48101b0384020f03401403000c260400003402100d0320b868045d00c1c1034030410100821200041140b142150103a80d00144004842004c0051b259030000060144005203603100104152034081050751018081c2040e822512000030070004640004098034800c2070003000826919035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 666623012 1250 666621762 666621773
    0x14240a090602070602070b10050a06050c0709020c0f16140d0312150e011203020c060a0e062b06080d0c14070e06031b030c040906020d050103080c0c041b0c030903 71
    0x16101110001c0d4001500000c0c0000510408d82c4488103101c10900a402c00e40400c020a44034810300c4207101d80800c50490540381032100c4800303421414000c648038401020b101d0364500185013904118001c0d0fa25004503240c2510640c015100d060801011000611083c001c1080105900ba000c21402c6208006800c43c02d0046038000064080d0f02c4d250b5905191943d07082c0728060748220308a4803903545500002ea0013181021055000302e0342180c8441c40000180c49d0742014501d22907020400007180500c0a11035040701c05007011300c08400c42d0008040d04014101e1b1101d002da44510741c8101a400304181c403031203407002464411401e18003030456880b40c0760302c0c00c903480c0c104040c840b0030b1404015060900704268044d00c0f4000b200104112049004170380c0316606400c03124095906c1d0103803002400140e8044903e85a203441c1c0c204065a0b4a04080c1c0e0f46802c05100440c00c0d028150030100a480c0c80d0241a0050000b00c200c00d0005140c18010303100c440c2d07594000ca00b40701101100001158 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 666624262 1250 666623012 666623017
    0x503060d15050603070905060a0e040206130609140f030705062203150e031201050d0314030f0a0608070e0a021b0a1b060c080a030e03042114240a090602 67
    0x2000b05141c03c0c540201810004d903a004058150f28000820180c0d0f41d4401401c41100c1c0c28841d40702041d202e50020442512858040401010700c20600090595100101000b12190704081418000d110020842050101c003a0b040c1c0c9603011802c14072540c075000004050741d2001c1c5ea1801140c0b803070101c0b4040c0c41c2116900540d00c2d90015001801c1c089240c0c0a42d08800002c80040c0d880c00c152101000640c43d011f0151078080e181c8100420700b0180100344000c1e840b16032004036626440e024583d4031042004031511001c80d820304400146821000429038207440c0040d288402c942d0750280140025001003181d10308440500c208110840014003551901c01d0243e0211042e81c100000d00c0050168603034840420040c0c0300100e240424800010384100d07041520300480d02c5241c05036241d10350300a6810829040060304004502c25521074680f520062091404068004001c49019112501b8048803200c40c0d501103030240f000d40c10500113550100c100700c000900042151120340403178 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 666625512 1250 666624262 666624293
    0x6052703100603021503010f0e071407600e0a031e0e040b040e010c050c010f020a020d1808010c0e090901112d19090f150503060d 57
    0x4903582e4100348290305080c1000001c5c1c0c0d181d4505c46155526001c02102e841841d071190303d500111000210f0700c00e500c0b070301d916844044001c41c1552900c01c0c50410505a25100981070b04413080085021032076245101c4c2c10209480040001d885060b110314440d100510140a18440c6400300408040242e442d11421b16510340c82402003a104400e85806800241002c0d464100c01400c4901003464903440300d20389965100640e00401c45d1800080450040c0c03d241c5803c4102d03500784010701d00030a40c04405001d0401a09000707014115421050200324400d05044400680040201c4602d00d80180c82c82510b00d000c0000c079054980d520369080d400c58908803003841c00205148041d01d19840c1420071341e034000a224000300454102c00d0141ca203588600c0003500103100080019503e03002a5018201c241c004480515590341101e0032060425540b0308001404a820040040b441c02049840700e01500c00d25200003044035483c907801e03107076504000c080c41c0d44030000d500410001504980b11a190303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 666626762 1250 666625512 666625543
    0x5090609150f03030403021201140a0614010e0d0c290c07030b07021f0507110c0d06051008030f0d0507080408030a1a041505010207062606030a0803070206040203010506090106052703 80
    0x4019220400c2b440405000e0302103101d03d4244001841800348850f51600d12030024284514150b41c00030118014010f00d00b4082c3c403508042c2c400003101c02040d4402c5501c204020301d880000000884c0641e00c1e4064403040c01310307039030281006000254880f402e10b038000b07a070350045902c20701800d89022000c42d503410206d5501512007050111050300301c070041c0e0110061001502c4401501004105a4140300b00040e21040d101e1000c5040f070900110f258014182541c01c1d00d5490348926900241e5512440c0c8191045140c40b000031a4544101c000e203024a921455051454413124000300240403501c007444c035200c001451038a51a512480f61005000c020f035054010307140340200280c140841980300500f44010031030001507182c45106012214829084d0203600c58565a01291801d00169002043c6060001c00d2141c4950001980c07413045108030001d2119950740c0301030000c00d02080c030480002c14018010780e151901d80030201004412a600c0e100300c29031042c00004d252112403001c6121 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 666628012 1250 666626762 666626771
    0xa03090510020c1906020f12040b06030313090c09120b040213020405010e12190b01080c010905150a11250506030601051210090f0605090609150f03030403021201 71
    0x1040018000c0750303614501c5540850074020394400e00350725080d0b01c0e080a01280c0481c5208420400b06505a0704030100d805000d50b103074448400c0c00c1c1181c40003500c0a41d1341c00180760000700c0070f250000441d0100034900045000007480d09039040f000d0140c8103030311410300c21014001304100b0b41c0490b603001c100e406009002c100f410f090050140100540c0d050000c0030b030041000f13201c40d0b60440c204642c555800e0f5030a045c2c00800191a41c00c2071072a00c1a00080c2916103006000d10402c0d04985050324a07240940b00b070702c01440010354480e0382d10b2207a603400c84a403005c00000b61030b2401c080c000e80d0b080d03814429442d000c144822030401e8a40070843c046068421065510062444110805483d0a079040c501e542044000a0528060703070502d1420b42030f000c0e00003100700201c17040d010010310b04260140b0000413100d0170500a0305440c0900307800b4903035800000d911403400c22102401800c0700361203107400440c04410700414000e403690180c0c01d840f0400c00000140c490070740003006129070000008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 666629262 1250 666628012 666628031
    0xb19090b0403030c020d0246030909020405010807030e010b030d0206090c121207051207080702010f020c09180304080f0d08070203040f061d03010f050f071715060705030a03 76
    0x404031503040310072108651000c0c6c00c40078120b4002078001e0341603494103915840f0300d01c0e18a02c907011200000607007000130b0f0300307600e00300d0f03810351020941c5122482900c40f22000d540b1010b000c803c9024600c0362a002841c0240440d12140c040e0780100d000901090011447e0070180c404a403034059480c04240050f80700f0000c0050003603080c8600341d402002111002c2100c1b060510440c3c1d42c1f15030140d0545503000000300711082100800406034088441701200341c40346054208040b1a4001e2042039002c50011488101060310108030081c1010006200b2400b0b40ca41c1c00c1004684404605001d8882c03004002c04540c0316800c2108a444458800c01007a10b5103110a0040240c08007500c000705640c0700340014041050b044880700203a4006150020503010a000400900c041c2200c40035055480e022404c1000d4000741c00040c4206c407540c0c00480107031200c080468a44940d11400c1300134149650100b0021182c1d40c003c084c1050000300303030508103002500d540303007154440048440843c1c0d550310b005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 666630512 1250 666629262 666629267
    0x20c0a15090b1807080d09030210050c0d12150b1305011707030f060314030307020705100914030132060103020a09030210021515090a0c0c0b19090b0403 67
    0x140300380080c0c80d041c0860841039550500d145409400995800e00c82d10309000700e0601046000000d0034110215011035821400290103190710b0300081e8010404403c5001c40d0360b010300211106d004601c0c0c02040300740100e03d800c9601c000b006609240306a143d00304496103507407407800c540c06002403942a80d612076003010303440c0602565900003810b1049101401d0102c00c1ca803c50035503c00000e0501140ba43c40aa42e0140100280d420041004544014203410700d8000006907208422640032204042d488408200f0202c0c06040c403400042c24008051045e140b0503074514251040141c00400e10907000501c0150035540580915480048001203459a02008000981007d805e003811803500e5071400b0018100022400003a00a4a0003069441c04610030042c1074403001d401c8240b00305c0d9081800084804c105903c50003841120b20801140e0100640d06c25911030b104036441d111140784d0151784060210710001d000e48640104604140e000b02103e01442d40b81ba80305100d050414585072401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 666631762 1250 666630512 666630533
    0xb0309030918090303061c021309060e010b100302072301271a0402030c03061602070b030c0a0305101203090303140306031b0f04021b2116080c01020c0a 67
    0x41c0c05210b1408428000841400300859030410030684030381102000b003103041c1c0b81f11109000300a400454104201b07112501503480407940a20400341480742c41d42d4028050b003030703a150843d2603601c03144803031a100085d03000768003c0540d18880c1c4101200d0000300c0e03070b041403002c0c9241315065003a5103428070140c07000100500c2c1912200e4441d13017403211a0780b5444000401085507900042c00780b40d040400c00750f46d810000312888450040c100d03040c6140003613000881001340450310000d440b862a01190b10203c4005681c81405090707040c41c1042c601000c2180580170103064080d00035270501c1c020603114144108a59990300a480384a05503140d0700e0014552100903140006d800f0301030003400100c0e60080740d0007640405880d4500070700180100010103844c0386140d143d40c0300c0c2c070001d0345640304054141e00a00403800642507070701917400070b4081c884044514061074030300b0004004225000301c81c3d0040c500c40a001b1400241051132803922a4220ba01c554001207071380e84a4940c0108006c0400c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 666633012 1250 666631762 666631789
    0x50a0e1006020f0303070c020409050d0e0f101e1106130c0e071e020c040204030b0907080609101e060b031b0c19020d0204140103061103040c031203060b03090309 71
    0x188070f529080405280c80707010140074002080000c220500941d51140c100800003504402603688031028040301405a40c10391703080394083d54000c5202c8104d4035004c4040c120001ca01d46400f0100d04110031112000c05c5460a030b48280204e4402d0040314090030042644280002c0030000c090401d14108020940a10340c0a04140b042d4a070422039490f0307002c900c10300042d03101c0d98000420300d9406001c1e410710608046564000784049400024480503507021805036000e082510801a21501a16140d220880d090040c551168484100020940e44900e907000c80341c103008892f100701a60413509880840e80050740c09030000c424440f91400144810184022030f10900c0c0c5080c40700c01c013003a04c44c1400582d00c2c85c90040a1580c805640b94400039503a0107500602c200201c1c84560800c40200d48280800d85516160a102040364411981264040da800440100038280341da5560b81d080d5011044942c1016100c03a00001d6486945c400366004203080c2d40556110907505050120f004040c66 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 666634262 1250 666633012 666633017
    0x51305070b0a180506090907120213030c092f040315060608130b1b040914040c12170c03070b01030302010507171b092b0b0f1501030f06050a0e1006 65
    0x100c2c108135a50790403040350800c1030140c52103080c650302c98006403071148901e580716660a00005007004841803504d001400d982c0b1601035142c109442d60744090444020311b802810890841c841c0540b425104441c2c00000e030700741401d0314a404d0312950ba0400711040f15800a500c5c0742c640d00305005540e004400903612464800d5100c0649040c0e840c2d04c03040d500054002a0241c1d464032402200300300324821a8090710141d80309210750895026075801c00e5408850a64a00742c0f451404110b1042d0030181c0c611550b00000843d075001c1d0300c02d10402403540250340c03101e4984000c000410000c0c88505000d40218020740000600389040d01000e09450904503401008400c00070405c1100442c425900b4001c3c099040e410307840d1020380c0003040000c0507001046030720074038080381d88605070300c9804008407481c0b080e21049826190180c8082d0a80c0050760090000d44c2d4000d201030304e552007540400044107052401007001c6aa40780803804201d03454225140d0b103070000c000c00a50358031a03500c040090081c0d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 666635512 1250 666634262 666634307
    0x204260f0606040b0f1c0506090a11060f16050a0501050c0a08011a09060c0d0f05090d0f110604030f050607020a03021e01021c0506101b0204051305070b0a 68
    0x2881800e03141e00c40100401d20455031090480308030f8072812502d00344440d028051003401c58900c0b1200c9402081c208040719648507440001d41c022501240d005c8146d940202036002c03106840e0208145500040d4401c01030241c20f000c1d1281e500841039800404602170300c05018201c006041080c255440201003001c0020704204c4c948032079600c0b00322941103400d21049500d80064220044034144180c0c1091039021401081e1100907200124040701900d14640380c011205003084010789283c051480081d82c0300030802070007000714405031603020700944a07007500304460b149200021403642242d0000d079054400f402207070080110401505030040e0340d070b0004001c2c0d0340c2035030b030000e60311a205007122000500a114240310a003003501070340c6aa0061481c41140404021100001804c0c00c440c1c80c0c0c400c003100c01101c480140120303c00340c481590f00d401404c5034040b58084c07002824000e031120440700300c00340410010800c02d02210014146809a4640d62070703180400074101c10500305000349400340c1c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 666636762 1250 666635512 666635533
    0x82d040302060304061b09080d02060403090b2217070902040509130812070e0f0a080304121e050c120601122009010b03060a060201020c0709020715020426 68
    0x100554085035030454082c1d9980d40c40b843c00301d01420054283c0f0100b1100c4411101c404d130b401105030001e45142c1c104480741d003408458226603454050300e01070007140e04040113000da603500800601e2094004841204c801d480c611201d030b1092481d51085400035002c0c01d0910200400340f14101c02090301201c10b50500e0300303210016604200c0030300b102500e018240380031010440084150b0b007104010f011380001d14a004200500070012120b580c900c02c00e58194022214901a000340099881801c025820030741404290b1504c10b004000c140c0761003059041c901e801c2810f02d0216610244036001400d101e1440c1c505110005030345585050944e0007413030051145804d0036030300a010b0358105e82e0305d001c1104117004180c1c00490340a4440d400100b69000450344880c03100c0214002c00e415144404820345e100d804a08034003d107a9045015048040e003040721039050340180400d280912690756440c800994960100c0c0c0c850361002a1000d100c0c0c20003000c641411086040da41208405440121507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 666638012 1250 666636762 666636847
    0x9021809160e180903090f061810050d020c151012031b0f1101020606010c031407051606020105011a0712080a020f070602090a05040e070303110c0d08 66
    0x2140c034101d00c01c01840d010942d50950b00c002101c6a0048054292085402c011a6050300c81c0d2200700158064450014136170b20b24105901120701c050700814003c06507940503002c000f5003031410079659080200501c0341e00002d91207440203050980b80c8000030b2288112103c2440c0740008018503203518050040c1080004408640c1c10350692030f8907180c030402c10717443c2c4c07503418518140041c0060400507061028a041005d4161030100d410400d0f001c82d0309035554080119003411481c94002d00003000c51200410002c2085c01078522503114900b80d40e51010504441c44450040b54082030051f91544010030034a0f01d041c2c50884440105c07401c6920304481d80d102c86010400041e04082000044070015100d0001641592030029483c203529070345200381d00701500a5000912030074440d52440e1800104c1d0b207007034490071200030b1001c0090a03505155840c180d0f40e545030116584990300600310741640c00c1d84c6205250818501c5a82c480fa1143e68800a020003c0c0000490f941120140700e0341d00038420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 666639262 1250 666638012 666638041
    0x2003150f0c19030e210703080f19050901111215040203040b07120e010e10140115141908040605090d0207180207020a03030e090c1c0207110a09021809 66
    0xb16080101d02c0e200500416441c01c9000300c031a00002000000c906804426080102981e40c0203540ba40d40e1605d03208122200b900c42a62180400c0d40048800b2400c0500c0781c2006900000007800010040094100881c5951100e02600400b000900800c4040d03192120301c6000000203440c11815498a5600c0014894002d0040400d0101c0617491201c94801038000c0c20321025050000e101c14001d041169580e0090390140080caa400c2aa035100d4101d000b4551504840500b48018001c0981010940c0c400c1d240304402140c10000b0459210103000407405400014078569500000b8541307820700008446010740b440420782c00080d0084842540001c000080d9048155503241024050171000000d118940300290000383c0e1490000c18180c0200f130013040703d00d044d5080100c0390b58000c0740101d18411a8403051219000f002128406903013503014080d0544210403e80c00c1c44218000101c0c1524142c0c0230041c030940014040b1007032000b185100041190580f0b40c10301ca420010810107004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 666640512 1250 666639262 666639307
    0x10603080304050a0210020624030309040606050408070611070e04030908010203270f1b0d0606090b03070806090a0f020609030615030c0409081903060f0f08070b0f072003150f0c 78
    0x2525948949d80556041c003c0320126031004104100c61655010040c0284c0c20504c2600814002d001c4001592400b42d000380f0b07501d8201c3c001404400c5d007000a51070f180c11003d0001e604024148001142c851400d10040d4003400c410103030b0030700309408080ca8880103c0034000224141d000789140c59000c4200043d039507001c00b061141904003519000c046a00c01040050280c14279040c81e40016001040ba4440d50700142e041d0180e48078a5101e00c10285c1c1c40030141c0e502c0d00c256101c0c0d41c080004ca2803807030b820280d843c8010810791420321030a000a1601e6001d0383c14185548290344249400d240c2000b4030b0a4041d002d45060105011540300d00300e40d40503811141c488800e000448114a034803990210014140d04031b4004502c80e00e84102148042481c05503008510400070301141c501021415030707903400d0f001002285804415034490440d600c102c3d052100c81c0703019006030341042e03400b846a52504000503050121500d000798074080f050750013410b02d112a1a041004c2c1c2401c0712606070b80402c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 666641762 1250 666640512 666640561
    0x10909051e010b0616050f0a1205090102030d0903030c0e0406050109030f1e080705010509030f1801180b0c1c0212130b0a0306060216081c02010603080304050a02100206 74
    0x801840c5080c071409421000c4807560701400028800c100500350010a2160303e001e0710460326200100f00d5441d03524180c506018100403455151030301054442e80c024681b100040c81035904040d085e59084090314100e5800f01c0c040b0380c45505100c1c0441d440380c0114a80542110b0520000b1719040010741000c042c0e0001810034024644202c040c0820440c0703940d10903140d03034510600d5982a0a02d20090b0f003103010225180c1d42008042a44400000142e44c0340d00d085554240c503100441800000441d1840030b51303414001914180e07000d20104503507210050031815546669990b000104c01d080480e500c0429035280c1c080c48082001070750025000d1100765804002c1556024600920000b0702800d1340840c05010300080d1450038079038190401e1003264030b00e030201da801c0d82c00820f0301c0540c00514092011a41d020600705050120242c1c0148148901400001601501c075203410070194400c80d01514603074010904141141001d2007100c0c4200510302c00307000c1d00c3c188450001c0f44400d0120340000c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 666643012 1250 666641762 666641803
    0xc11160e130807020316060815010914030f010e011e05010f06080612190b06030c0f060d240e220602030726010501030c020c130c02030f0d0b040501090905 68
    0x200b00221080310002034005040340d103031301100d00c100e03d100c10580c0280c2c00090480c5011036020540000c03450440c800c1612181507d909219000c0b6040c1c00000c46954140b00b883e144005042c0288148554046544000704403400010407034410480c0d542e1038015583d1a1000401c00c1c1101d421001040da401c0d450708400c0c540f82d030340014440500d0341e140d40031a8080c0c0f0003600341c1c4041030001640054840d5881c4801550b900d410980c407600c00a0a8581201c4000c81109141c80e28500405001003002400a083c4149185003010211503801c40c40c20819060014881c24140b40c030415403140109004407100940183c8038503010048003030007000355070040f0129102c603000744580b0090b027a9084511505582c210755019000200b84203040c0440d240241c0407190f54030100b600340007450007520110800c0c4101308980000d0420000c2c00045000034012028805125401090b212030a2440440c00e2001b4004100869206900c44c2061628216012000400100704000d180851010341031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 666644262 1250 666643012 666643051
    0x6091d060f180a05010f0f08061b0408010905070806160c150605091510050a050a08040212030415020d032a030603020a0b040305240112150c11160e 65
    0x559036200340711a00c002000d450b08100c1c40800c00d51085040780d002200b15041da5658020444d078002d26401001903036003043e00099100c1041103509040d24101807409490b041c0e031465100d01b141c0302c500f0100e47d6600840d108002c201404c100440d0000c1440010700e040701c01c801c40c00f9010001c030200007807600c586094941c40c880c070300307070b104000809010380210454135011120350101c40c81c000a40c2c1c03080003400c0b009880140314000346c601988040d12281e1a01d822124107480b240401082280c0c0400c0c6030707229001da4481403001d030005000740301e507005c0c1c040480c00340a410040c003040c03070008040c03404000c241c070004c2801d81c1511315201400001001048040100c0c080c2107190406500010319100005003001030500510451740110242e03101100c0038140c40102440c000044050300300c17040010301800c0704901c5105c449912031100348030440a04207058040d52014800d030408203600001c4102081c40a0241502c3c08164003542c100d0075051082d150480000074007010782c0740b1540350001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 666645512 1250 666644262 666644269
    0x17073b090a050303070804061a100e0316170d08070e040903020f1209011d09150a1208070201080708040b0f09070f0312030c080f010909020607021201050106091d060f 73
    0x22a07500e4011003941d640e4503000001410010701510201c0d105460551030750400e400320810440e003410f00400e80007190303004c4582200c641e2080c80540d98540a0f405a5601060307c4401000081030600000c1481c009003c000340d05003c0c1c0000f51606008501e410407008035071082c1c200c1ca1098041700d000900c114181812440d01c421030700d6a520620900301c80504403a125400342c00e07180d40981c0e403440e4400d205001e140e00c0d0804c2c20900c5d03801000303c0c0045181c1c094250503403803001e04007038650140783c0d43c0c4000c441e45281c01e2203016201350ac000500902556070040300c42e41d010205080250840c00c190340c2e4019101401132000911482400124546030424004240201005030400c1e100a03101d0030138001c84122010000042881c00b8000d1009500402d040d611a01c0003c0d00805103a103402003403400b0384603c81e4201e038450b00811264006039200c0703181003c15464500000340c07a40c10640c02600010040d000b6000345918180c00c616185404061190b0100d0240c800307442000404012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 666646762 1250 666645512 666645523
    0xd231c06080604110a1a090411070209011805010b03040503030a2a180509091b040605060f0306121c030b0a0504050702030d0b15030c0304030917073b09 67
    0x2592103010b10010311051201d0a402880720a908aa0f66104207030703114241803c40c0080d44225000c000f080c02001c1181c50150300c03520081000c2c40c400c4d0300d085040d6000410280e8240c1041b2804074680840000c60341c503038421a409815000040d5143d4109511202e640303000c0142000034903615034401443c0d4000901480501e41f01089061101105516024000300405410319008214540c03000130140742c5990700c1d9005910340c0000d400009a10400d41301c2c0c441249036582c0e005501c1e41d00c00211512148018051a00c14114160f140d080440400c580000955629833141d8004d01242d2240c0e41c0508100115018500300001c4a1080a011414810003a0720059105203031a00b0840740d1500480108a0400541030030002201010b0400584c2440504640600b80041c4002001644032600440c1c01602a042100d84142e54404140c03000001c92042642a00002d100300080384e4202d140520a10015840c2c802c51506101680c1b000040c200c60a004140c42e2804625258070030301c00b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 666648012 1250 666646762 666646769
    0x20c070308030108151e0105060a2309030f06071b020a05060a0c0c0605040807090b010309060e0102040602010c1d06070f060f05070e0405040309090b04020d0e0d231c06 74
    0x481549a41c0c1d02c0144c03a440b001032a221080c904038500000d400c8990540c1031103070340204401915000c0e428402403201603084801a1010700518600321302000c01901018000d060030b14a08030f0b9103414403030501d03080c048481c14a203241e9002006101d0310131703040400002080701c031010302cfda003000c13003800002c0c2c1da80740983c400343e00b0400000742c1d4100a940201c1e10128039001d020540480d82e0796140031600d6218070321881c01540c0110006000c02d43c080d8005641c0a40145408520038910391506000c890b028007211349281e40c0050100402c540a0141c4448840c41382442d00b5110710365959221040d90500350a4480d080000b0100100b08200d006600c9040d00000200451542003070700e440108010740708540842c1d03000d4128581440c1a00030b0522540d030654036000501e14000707421014140046e1a643d111740c003403112010a4a4900c0354015403c40040242003c09090300c02402e0f241d00e0b90406602d20803005039891980040504450801c442e00c00f007140c2c002c52800007007000301007a41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 666649262 1250 666648012 666648023
    0x1f0804060c0e191403061603021602210c01050406140d2c0114190504021c0b01050a05030102160803070504170105070e0916141e04030302010f0501030213020c0703 72
    0x1c680c00007058480001c01c0030751310020404884000d1150800daa1898211100903107445242d80100625102e1f4000d015011080c00200b61400f41c942c0c002800f00c2135030710300e0401c1d1070303109600c5018104082009140c1c80030203080c02032410342030240052030b0340d42c40000d000301c100001680521001d803640c001e414110f14040c81414544c545500c0410040149843e841d9075030a0501020307403001848a0b80340501001400c003400101103000810140c20002e0090340d006d042c6940100d1105440c00714004900c0c8600201c41007581000200600100342d0781015020341c4c8184003480100c541103000d04080d5410070f407115165550901c1c110fa880c40b070340e00702c1ca42100c1030a175039103c000f40540186024555603140c0000f61f491f03400600c41c0c141011600c3c1c0329045252291258524010284c030904d00c000c140303100b4546420140e011081d14034214215201001c0081c1c100107050b420311811086c0b4800a00c10b006a503d10f800048001540c4100c2d0000194001800d4213280e50820201000350ba019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 666650512 1250 666649262 666649279
    0x70905150d0e100b0402040b0306210f0d031d0d080a060f1d0f0c1801140a0818153405090a120f030f1215051f0804060c0e 54
    0x51103590340f42c5400000c00b0380e1150510b14030038814a0b180c0291000c3d03402000c54142560b07902402c10404902c00a06181402140c10800714403007410301480b240d00d46c1101c02400203166107480202241c544038070000240900b005401c03c2e04901041d5440c83c56524509108d2070780b00c40075000018005a0701101640485400000311003400c100405080300e820202000326580380b0400d0f405801d0200c403000c1d0004001c2040c200f001070407040c004540310040c94003584c25840006601000e502c415100c0380490682c404009008158a240700704c0c405641028014511341c0c00701c0c00d0703030b204405842c00c14511588088610003030000e81c150402c4028000c0002182c8134204400703000b5501c900b4006009000c00d2001080400074140e8086ca101c0cad0109403800300c0403454404441040e2001303188020403d2a1409a209054174060f40344400451000c0c04841e0349018100106e00f0748803030720100e0200c89004510b0069070010841d949c840d4210802165100682c5000c94203400030b424070030f074071a900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 666651762 1250 666650512 666650531
    0x312030c02240f060105160308130c09060f15081b16060b030601080f0303061e1806100c020d02010c03050409021201181103151c05030901080609070905150d 69
    0x4400005010f1880202c1c1d00185498110044070a8803945a00e032502250546240340000d00c10000540c0c01030186040011848003039035414682c5c07801d81d106161054603a0401d011a5800585603002441008590402e41d44040b03000f8190354401021861103009420701648843c2c0607400701d83c1020061032a485144010380b80100007440b040544501a200c1e0300008940d9900000f20711540d600f0f030f04010760440c1d440c641049a40070840350a044a02d080300d0559805843d801c4500007a00035003203101640c5e01d004014400342d1a10040105c04005204088002589401801560858080c0ba19010030601401c0985951040754440c0364110310000e98402052051070109041e40d94606841d01c8180d0b0807502c000540f248107000114a040401c04101c0035152840e6804c07210740090450310961403c072002011040340b142090300d16800001d810703581d40da03004606991110046851903171768148a1801802e40c80640541c900405403c0e0b03078418203142900c01c0c2d911800c1c4089081c03000e07004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 666653012 1250 666651762 666651823
    0x30d091203150b07060509010b060a02060a0f09020d0b18030417102d06080a0b0a181e0519030c29070c030c0507030c0f0f0312030c02 59
    0x410800c20000a45400000070710090b0b0140d1281c1100c032602c940f9070901e8040e4031910002d00700038143c040150760340c1038140041c2e1624000380042d44000c4e00542581d2070f203584904d081d41ca002c000c2d024464030b401c032a1401a40d81e0a50800d83c0798220102001ca81c3e030711304068841d03400c000c0116800c2c1c4004140040c0c400745a0318010b490a1450f003d40f070f2014054940c1728181c480304034074000c103140d80d01040c050002c1c02e0002006a002955400324217960b40340c00c031a0030410104c03400e0b104000036004005481c0c81034024600d081c00507e03040151100c0b40e4440340f0a1200200302c0105040781000d010050000801140d000b0080b4003200909140c0d4510380540b014401110445082078a80d074402c0012000d5112a0000b01c1c5540c201c14203561000e004545000c3d1903c03080701408590460344000ca1400c101c40c10181d4071510503103500c0c40c2007132000580c60328a688490740b0003650f082e0a100054421442c541405950704000c02e40480100c5e083e030074140c100101420050b0a001208610003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 666654262 1250 666653012 666653033
    0x228020118140c010804020d020904080403120228030f08070509090c030403030510080c01080403050706050a05040606050f1e0a18050a0c0e060304021003060506210705041a0705030d09 81
    0x1d5404040b070380f41440c03900041d1440b450803600a0f610002003070b039441c00b50501914203580a8402e410080c1381c962296206070706e001c040130b00c0d140183d000c040c81e078484503900f44105880c8000f50f16071381c0fa00b10050354024510850150f0003000c1001490108801c11b028001340d130304420b0000e201781c4030351502c901843d01c0c90300111015000a400e2401060400c0d000c0401c60703064500041c00707410700340203a000540701480003410860400000300505c1020031020300c10f090107080c0390207002c41c1c281042c1c20140156000da03001b0512941c0100020011544c0d0510030850200c002c00544032071760000c8000075448005540609104a0b00040a400b68450340d48560310400c4e80744001c01880aa44000300e809000e0070031900d4110030300f0008240540750040b44820703182d00610b800301ea1a51240049080c40c0c00954420301203e941403080611000c2c0d0001050b849005881e005040ca483c210790b420941e078558403144080c0100051400905c10180219500100482000d00004280303141250090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 666655512 1250 666654262 666654293
    0x320f0a060309060f050903040b210108060613021c0e070306050c0d0e010216030305060a090c0f0915050301260102040f050f120303180115030c0e0a0228020118 70
    0x10302e013845400c0c4003400e40c421903000d201003c004604050030b1488850099100785006c6900100c000d2013003000c1c44042980c2c901811400c0040d00083c00e200307061005280c0c0280f104050140148580c28500d0034841903801302c801c1805003c540094070844142c24000550409820507041c14204140408014000d0040323148075282001007003e000341881c02c0b03019281510202d48801030a42c3c2c0400d21076000340d43c0100d070080440c0c4100d030350360980301c0c120340c0307128250004100006d5011242030f13041400300700103000d540c0e0907540c034581781d0500400d45d1005025250201d070042c0c030170303101c4103880410b00b24903c90504001c41d03a840c1c40d501c45e517500c20410b206407442a0189000050103050031225240c6164515000390b0440d102c244001060324680d0740c2d80c1c0318940d07031500389810030216001c1102c010344c000e0150b40038407070801c8801b004159005080e00c0d0141d004015104000002c10169900c40080b14107020b10b410307100c84101d014007013510016400002411281d010f1110360346120f080c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 666656762 1250 666655512 666655523
    0x20a0803072f0a03020607080c070f14010201150b03040507031515050f0307060e03030705030d0209030f1c030507090e150406050f130f02190207030309320f0a060309 73
    0x2c2c0c0ca90800c40380500c1c00e80700009400c0f00554908000600300080a00382c045d01c11030343c4e9420305142c0c900e0303149045056802105d14292049040080251803403c482041e6003c0c170003404029040c10404045e0000d42c801c240622000000090a0040521004019590200340d60001c04007684a01e409808032807640d0f01d940e82020b00028081c6810030040714070004c06030192800a150400c223075400c45086442d581c26010401481700068000d01c020501600030321300050311404840d050515001010000c0a110342c0901c1c200c12420440007440841349842c0e10780451142e840311000c0b208941182d001c240040400d1b8103000510044010036410a0001d80701084810740c2d940410041c1c510041c030454000d0000712214501c10401d03001402440b048410240c5041109e02c1c2c10905034850704140c500680090605000305031740200e020004003e0f400d144090000c00d40c0034000c0c617030986441c1d43c41c15940e002009000e902c501c50300e50218840105220052035582074040d001d0450701d001103c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 666658012 1250 666656762 666656813
    0x3031306020f16030308060108150a060503040c0b120f130215030a0c140d020d0908030f01031205041503050406150803071b0623091906030c11030313020a080307 71
    0x381e25848060f8008032500741d540e4200b03c2d21280c0c015a03e4007000303003034040b03074030b80307003a0300c800d05855546042001b40f40700e5403001e03038a1402d428a5061007030f8070742281d403a021301004456012001510910b0f0045500008a2415102e80c1e800103920081503000075000204043c542128600c0d05001c0c62007800462414441e40c210388008071650350451070030f03c0383c0000a100c5e1190441d520780c0a401400b0240c80006a0a40b654890a116410448200840c08a680d00510070080c1c40c5218100c10025800c00a01341824000000b00110b0b09100000405582d40005002d04c18503030411400508034100300300d0700c0d40d01d41da0016120b07032003002c081e60f06000307400380d0358682c10342c04c8480421100641d45d24201e1909480501c4030107043d80b25080d000c65400c0c0443d00180d80c0e22903440f000659800ca40e0141035203400c002500b550b241e40c0d00002031000c608035042481002008407580000b00456071903401d0013034800240001b860750444074031444003190680400042d544504066404600d0620 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 666659262 1250 666658012 666658033
    0xa020d0b0d0c0b0706061d0402010219030801090b0f090103030203092b06110d06080703060b032406032505120a030c080d0915090209010501030b1c0203031306020f 72
    0x208520007448002c0007074091200400c002409180501000c6103e940c000c21071566440c41c1d5107041c16a030b2081c3c1d0300440000288004c640c0c042040001950024061158480d126203000d0702d61081445018000e6032914a0292032b5076901c0c001ca0002031000342a200c00c1c2d6100c0c10000d64a070861513985002e8410320a100c0c1200ca000003442507030303d290411882a071003480d5242d0380640707100ea11550001c1024046100c10850f24000c25000d0640f00004103191491400c00200703855a41990500a4104007034100e03000c1070301c0002d827054220016034252584c13904804a45403588050710f00c1e00071000307402c5100e001348512484d402120812505c130000d807103c00c040b154a5071402c000007000301c1c81e031340b059200080042000c0e200f9001c10080004032070a0702e884902c10202e034214907140c66a036038070507034003145010b001c02401740000b86801c1003a160b48101003004c0504009001410724a076040c03400031035500700b04503052a0000051011207550701c2401a40d20902d414401c0d2080c014400300c135 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 666660512 1250 666659262 666659269
    0x1202071719020409060b030f0c0306010603020c0d2d0e040608010c020d0e0a0e042906060f1c02040308070303060501140904090312050c04080f07140618090a020d0b 72
    0x110014014007540309212582080010039807080f086844e283c840840c0445540e0a10604008840c00c801820703900d84080c042604085058103c0c00c285807041c030030503142400000b0f2000c54003509040082d0103070000341d0003007400d800c03d40840480d4041c95460020290b4407440300100f140e0b0943c2e00f0f0114035101c6203994207031a13641052400580c004418640560303c10b401d06540c001000d011024030584441089640000440703007030701c5840090307034002520f1514407180c110290760841c5000380d43c10104002101441815036200c02008003290381e060b1111100b5034800da00440d900119507650762840c0c1407230035400140007a0003107880c0820010765940100780509040c0440d074503062800640b030041000510300400107034100095a0701300301140c038007403207968042c1014be42070540715841c0880c13451030b000c0078001c00c0000340c102c0d041c104001100b404101d500c40b20102e030456113a4000c1801100c005280745600c0c0d520078515414862460b400342e000300042d0b0314502d01800024484c0052 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 666661762 1250 666660512 666660523
    0x702030d27020d060e0105040602030610020106060e1909020301030303090b0906010608011526150607020603010b0307050c0d08010f060302090906060c0f010f14010509150f0d12020717 81
    0x41103140d00407411410010720b001d0000c010024801ca000040c2e9003a000405400c5880031a002c81d500d03940002840b0441c0f400455012060303441d0f100038000c0c0c2d400d102c2e0050081020303c51032401030070000d00c0c1008003042c200000000d0069244210b45030b40c1d403402d00801070851044181e0710740026801007581e210012442c1d45c180c0b4180c1c0c560103001d07444c0c408004000000d0203c1170b0100001601e0600300990380d00b51100f080a010300e400000e80c185561240b0079405c942501910840c020041e42c00180c5401c02524111203040c40410344036a507c0a00313903490303c1083c854660138003416041864094000c200a8140c49484180c0c10100351600425001ca202d1903e01c10b52006100c400134400749003040040041e401307508281d688480d20040c6090a407a03100c0381180f4801d443d06000061a40122541401400220360380c280394207080903404990f26101803114040e0290700555078251712041803c400c41c51780002000072400c5840c4000392103582e00d01501c0e03208036a5080c00321103814000f42 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 666663012 1250 666661762 666661811
    0x60512160e0709062d0801030c080304030218060415090f0c03060315090219030c0518040f1b03082209110429030c0406080a1802010819050702030d 65
    0x440d42602c60070040c0c10b9404007017901c0e07445c0741650a42d0900168800901c01101495226254040d295040d032030010040c0007150081c072640d60050008201503a42c00e24144e44458952650f0301c100d455184c023080140c05562881a06c5000000380002c0e0702503281d00200c595043c4000c1007210141700001141914550b100207000001c0e10071154401c0ca180741c0c801c5030001d02c01807004034005140c04178001805540d500035504804042c5c000c100d2810000d0003280890074032000d4128a14195132100b8010344842c101400c0a410118403011a0450081d00c2000d15008081d20703855003812600f0020040c0740d00c114540c1c81c503a50200242d011404d005500c42080d80128003030500e820081211b505c4440c1503110201d80f40690f80704521442d410b001103002d5843c0b03e01c01030b9640e0400f0305c00307060004040e0003e0f0340f151a0400c0b01c0c100c4900d40c02c1e010b0f1520790901c1c00d100346072150414500c1800084002010a91a280500c41162707000401007201070171059050001d11640c1c00401942c0c415500c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 666664262 1250 666663012 666663017
    0xf0f12150a1503140f191506031e0c03020303120411030a050d0e010e0604120317160c020f0a1520060106080c07050102040e061201022803060512160e07 67
    0x842c1403000956080c000846014000103d81821802c2e201c81d611308030846030303003070316805017204448148210208030103000d5865603803d101e082d180d5902d1408824120004e04011035440e50050204031945a0383d81c01107400400b204d450724042200c9055003c01603030119418035440c8401075150078041100708481c0c0c1c21102034149071450b01800d4880c00502d02c03065040100c99261000241c1d600000380014103485030070115650340a140c09042c41041c0404081070340005801c1200000b1424155125000140750101c003030b01c0b2501c0801c0310100c0c00e0b983c55a0122400c400855109e210b10300e00240d0b0751081da260600d002d0884208440407103040e450035002d400020060080a004090540d0082c46114110345850000d440c0c40e401c81c0c02c240c2100d00c181906c9030a02c005403030701c048100c941001d4a03008614246003411005c42c283c0210180200c0104030002040b445802070344590001c000140040203081d00190304107449602c0074600c00701040e481d030808250250100605480303602d40d40c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 666665512 1250 666664262 666664301
    0x8010606031a010833190306140c071707020402120a0501060c02010903020f010c0807030e1e01050d0f0e0d03052e12170a021b060f090f0f12150a 64
    0x1400000314540181131000012803485200300495190034000c2d111420706d15000001c0107007540344c1741043c0c1d107059404500c00810361090006510140080390205540008105121505056114458000c141000e5407180c800f1501c60303800b0394017880c450b100300e220784410441c0da0f8032801b06481100101c42c001e40041c2d12084140014102102c0400c06c1000504110202c1c011607902c02080e40c0c4038100445c00107104a2107400c66040c508416801203000000320f41c10035002c100000c01703134040e80d030b11101e5031501c50342c1d00400251030358001c500240d03105060310500001c0e284090f01a01c001c0d01c1c14100750303090500d20118202689803001e030f80e0011500701e201d40781c60b1080301c0a007000c42100c19600c0c4647d000401a4582c104001813845120503000740001620078072440d00400c01042107035000700c504201c03910345805580c0441e6034006045400d040e007020b180340030568a00220076100c0d0031201680c1d19101c8050005034200104111218031820b170ba036600505000e0796410b004024a12066 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 666666762 1250 666665512 666665551
    0x1030612080f040e0c07030806060702101b08040b12240d110d0b0609060d05061305030403020414010512071206090503070c030b060103150807031101050408010606031a0108 76
    0x140004020b074544100440c0e00342a181c100300c1c0a49401550580030600001600310101034101c0d030066802941200c0c0700e410400940c0100f180d51a201036600b08104088800260308400150079520054000301d429480750340300c500c1483c070381e400810241440114203002904010780e400204003c1c0324490601c0701180c4c2000d06002c0568007402c03040f1040d46400800440580702d001c1c00382090f40c09100504007a0400740c040c0508620702070050390090220300440804104005207070703034020b48080c10751105524941011070541c056900025030260402c012400c00150f40031246041c1c0740b04a820020054804000959030001d40c0326402c10340d00c212941d0f1000c038419500003910319008006407403801105641d10102c505403600102c0e000d84241c818043d15503407600c0b4050114481080311914107042100c0d030b0340c0d50324040c4001400b588024940c0b44180c0d216905031002840820004d200941e1202405006002c114842401c02400c0000005040d841103080a018440070b0ba018040081c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 666668012 1250 666666762 666666773
    0x13030c050312090c011706030c0f0f03010f020d0b030d020a060b0a030f050105090105090a0f0b0c04170102090f0103020f0a0e1f080a14040201090905040302120d0c02060601030612 79
    0x881141552180070500402022658000e541441000407201400101d14081c1c00074100750704000809450100d40c008002032602c00017040c0c4840c0ca01119034039890a0304000089040e0741007035107181c055003040c00ca00700c107140d950054120707103500040034170290ba048018950f5a400608500c0c005a01401200c4082407090707104602d6820040d0485004d55140d850384218481e07115001c0712682e41d60340402400ac1007e01c01e4540004030780c03018040c001c42640320604d030354208031030181801e09050701160f101c0340307148200c900030112030184484400c02d40d034089000390070500319240150700e054040511507100740300b2940c0300c0411005440c20848840c00480d4000d000d503d0a41d004562050321484070800c241c0f1a1403480742c5a59801c0c400e10300b0700121000c2e50358514020702c604400ca01032100503a000b002e84425100c450400043c81d03615800c01701e00e0088003800c124140500000e0001e44140d49400c2402c4c1800b09800f10780071901ca081c011012100359218055400c826a0b002d100080c0b07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 666669262 1250 666668012 666668027
    0x20a09050916030f121b080f0c0607080417041d2a090103061a0403030819050c072906060a030207020301060605130609060806043c141303 61
    0x80c0650403070b0240141d892240001c6805a042a52580d4206108804001e402c1400c4010f4000328a4044150b50010b000718210440c03911005101e081c0205440700210100f2082d00c0d403611100e01196000c0c00d0481c0041c211420940d419240168400002c078807807040c9d40308450494101d08101c4c032401e00903002c40714402038080c1440000c01140a402804080c54411034096810f28517600396413080210b0016046a00d20350064203910450700e210302030b4100710700507107044036014107209850303944a442c180688440305071300c030510920380000d03c008080004050901d0038806d543d03150400740a00395440c3c0003204a2901d481c0b042c06d0200081050a00c80003908090107541009418980d00f40d000038252001a08081e00141c7c001c10b11203800e441000904e0001d00203400d0102440382410002000c081c0010202d0b400786840b00d15030030000e103c1d24203071082041103101c1440811501e00b14503589182406007401c00c0303400c045000800d00001540c4a0055038070750f207801d41c0e03c03949075001d46045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 666670512 1250 666669262 666669271
    0x10c060b120d0302090424050d0804080304060c02042723100e1c0804030806150c1501081b0904030905150705010c050a0e2b0506090d0c020a0905 64
    0x4070640014408000c03003002400c8100324039442c09a122152281804112600012030520300035104402401d0188a44503000c01d4980980d40c0e0002e20342281414403a520a40e44110201e2000240000300603600801c07000800b4400c03a0148995014105c0b40a4200c03c8d0910826840c035440c004500024207801807a125503680c4108070951400b0703041180e00b410b00b0314030001142502c454003144000c000b031100c030350004180140e0141c00801d01000410204004100074240007251020805595940300b4080240c50300300341c01c9550300640a429526118a0400c0c41d40309041400003040c1d806000c45d00b21900b0785920701181c0344500060400c9041000900180c043c800e206078045003584408049540042d9201c00a580e18103041c40d100d0b0858002824000411030203025204405038801246c00600030119200314080e605852060442d0010202140285030101403407810044042140f034880c1c2c826500307071420702d940440d09541420011000070340c00700704988144010b20036940200d402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 666671762 1250 666670512 666670519
    0x16030210020c0a0c090c050a08040204063804140607060204030516030506070e0609271306051509040b04060b100306030506090c060a030f1401030c0612020306010c060b 74
    0x15900380182850803a44103040c00c54690b0441c01241d804d204295816070000c1c03403482010454140e440400602900a0002500410043d000464150359850f000341c4060071001c01042c991030720364142000c6c0c4160b5100745003800000110442c1d0401100b1080d102290203080a4024041c40c2604101c8a5403041c0c2d82141c003260f0a2101101140040042c180c11854108580c0d440d01d095007000c6281c14130040c4030700104178183c0a03d080503113494065500e2203100340da481ca060009001a058160032020b0402d545100356010444185160740140c11000d0040008000c2a154440070480009a0160303642d04612040c0c04a00021050b519180c3d00501809d40082c00076000000594000344800034540000c0d20384406205002c0144142c58000001000501c40c880001020580501440101c1707018159159901c000e44071294100010b4800ea000c2103120030b68580c5403001d00b107001ea000f110000b522040c80c01401081910131030380241816110201400200e59800d0301500e49124100d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 666673012 1250 666671762 666671773
    0x90507080a0e2107020607061404050f0318090601021f0b101106010e09030c33070c060c230a020d020a20132307050403031211190804060605090c160302 67
    0x8c40c0582c42a05ca0035140c2c400117400d581443d09019150409450504c803150300104505203010700011044000710b0006d803090344a40c0e8500b00180e0421090b8400886480c400b9030450031140050f0b800007000d040200c51020391110352840449840228004001c000d5100ac001444510440c00d40b45a001a00208076460700110340002d9003080c4150102d880504070141800c902c0c0740d265031425001404018803c0a1403401610081021400b02006010190380d940403d078414410001144910110403218000303283c5004106496885180441c0050203103107111109544003161110b80103820a40070094480c840940a20b0501c0640f2000d81c080f01041c040341c524403040c004c8400d45160320b99040100160218400007584000304071a04105003044180006a041010a000314900500c002189031002d5481d014a100312a903103d401c1400f20052036540d540700700c800b84121f114403803d2020950b60414040306560a5840c0442c010741400a404182044810061194000c0c8120751 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 666674262 1250 666673012 666673027
    0x901020c0706020a0201120504050606040b01020c0a06180806010501020d11030d090f060509071a090d020306040c03052803081302041a04200a18090507080a0e21070206 74
    0xa1070140e2aa00207000b5801100d101c41c20342da04020711088848820700c09114030325207640c5c0c09859000c0106294030480d5603513409a4142d100300700c0c0c0c61424070050440001c00b5200e00001d01a01c02d070b000301d04018001850082001d56001c15014102c030b41c103800411010805907000c0e00c40c0b20203111b001c0214441800204187e120310301030320503180c0c084d0a0800b11241c207820300b10150761b4001c00a0005500040007003200109420038401803070400e83c0250740b44c0a00340300180896030102c4020358188102c106000600c10b20280c4030007264030a070212040440760190150040b0081c0c0c1075161080078041c604000b0a015040e425884186208982a000300d82e600080880d10543c81c3c0c01c00043c200c0032000218146803103500c1600e0f1150884981503400f0480350b18861103500c06032010071454000e1950305240d2981c5100241854020500c000d00d400b41d4020850203045030302c5030f0014140340f000e10260001040389825003100348a180340f11204010650f0301517201d003c0890700b2480800021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 666675512 1250 666674262 666674287
    0x6010e070302070618050d020a150f090b1f060c050309060705010e060a020d0f05040f0210021c17010b0c151803160c05010513091107120c120201140f090102 69
    0x49620241032900c81744282e40742070039450025140f503407205541c411880500071402c5000f0100e143c0e11402404201d40300c9440d803000252040c0343c4004e0a0f254803006102102c0291213194a00741b145c19545101c0382d0b9211001c80e1318055440c0c020740f540d00100b00040742410044010443d5900030000803800c070010300403203490410203d03400c1003441c3e80418000d03450120790054070314000418900380264141501d42c81200100744070004d00ca12042064000c40318028400008952078004610504074401d0f4005002048010b00685200055400101d2040f081b40c055602104842c0c0c010300c0d403641c200e0110241c0c41c2000e0464801c070f00c2c1c50707282d000b50050100b00601e0840000310380b05807001c0007441c1261754800c0540205050200620903880f07091103007900c400445513008808070301003012204030305082c410010050300841f04101c15075005508450741c035254a00c0b54000707c00c4007810350701c101e0881c0d8184100c3c80d81c40641c00003054444042c14a0540c2217104440018600440300108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 666676762 1250 666675512 666675521
    0x160513050315070807110309190b1b12040323010615050c100509100203070e0402040314060c0306240c011d2803050a031118120f06010e0703020706 65
    0x10844009400c2000f00e841d41c40640c19401100508202c64038865903200940c13a40105c031342c3c1d18090035185d0948001d1258017901c210003001410040355a80300340082c16019145800035141e5184106d6035031011480d1100102da0443c2e81000b4010701d084080110b0030f10100c04011071404964a420700820804102501c1e44440c00494860564409043c1000340c2402d928514401e283c1d4034050402c02c2014011682451140540c0401a0740769143c90064800c280c0703031441503410500c0845d0202c00c1141240c00c428031081d0500413540e5030766405080103143e110032504140c00c40350000d482d84002e28004001584071040d01000344c14040c0c01418503003180e076001c5100510003000600c025480718188041140b070804142490200c0101ca00f41c00390900c1107a100504100c4000f55800c0320501c42e5000e283c40380791180d015561581441d044c42e000070000881948226580a5043c0600d440051038045004039900035180b907030303e01030504040b40d400624000c1415020004c003400188140314 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 666678012 1250 666676762 666676783
    0x5090d060606030e010605090601200319110c0411090f03030c01050703020919050307060e0303090a030507230a030f170307090e0f0f01050402091c050714091605130503 74
    0x300001c4d845070b1481c0c1c0b81c0c207452655021a015505030b00520036166401030ba1400b5000400b020314144098004089185100b09000600002c10f62440950b84541c401c1241c00e541d04040300700c4070710320b460700d003003108036520b28061502e05801080064180d080100384503600c240e00030162805c1000100f6007500351201140d40300e0010b507000901d0005e91505150201a82c3c20703c50050b000d00b4100001300e6a18511401010284140070701c0d07011b4255402c000302d9800c0803010b440308041c1e40c0d0784c1c50000c0d03542d038890250001c540d03142480d44045c10715501c11646850740c010201541075180d0b841c1c84c48140840c94083d5130b00c90303913411101101c00f40980150b0040b641503403414081c5207042c026460a6601614003113505480310148404440000316090658038211340043e51500c4210006407420320000750b04182c0308002d103880c01803110215022044400e0042c02140400481042189502048411038090102a0002003007140720300090604408440781c0121110384078000030385000490b20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 666679262 1250 666678012 666678017
    0x303210f0b1014030a0506210f0106091a1302040e1305060a02070525090f021c090804031713230402041202270c0406090618030305090d060606 63
    0x9a070300c00340c180744444903550120780c501442c2c098107540c0d0071580340c407001e402c504c100b9440ba00407a9480d42d401781803950440d16101c24035190b020a4280300d80b00c101c81c03440d094495290007030001c0c04403c54050080703400304440c10740100c002404200200490003000c6d01d015139900303000106481f8442002c0d54000c035001c2682401804503032030705a140c00c2d07004109681807801030088600042d00001c501501c0c0200080500c041c25000d5441181007429078041400715041c04a1a100d10780154001d020101402e00e242d0719410350100ca610540e038040390300421248042004001081e04007140740310801d91550340034581020070607034681c0d04021780c010f400d44444090ae50003241d40748407030001031170034246c03801d50406180030700201584405079400380c0200ca00c0c090449542402070850b5501e848008800000c80c2440b951014198000b4003560f00800d608140103d0751318020800303c0710314401518942c0101d0304543d802c44541d04010409500075008640700030001e2250301030f5902502c45513 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 666680512 1250 666679262 666679271
    0x50f01051b1608010e160510230c06090703030906050f0f13090513150b0612070f200d030b040b0d060b36060d05010509060f0903090a0303210f 63
    0x83c0030740c0c0c02c4684042034030b0b007190700c0401000c09103884c0c0074101c005c480007103814039407955160030262503401c0340d1422041c8203000c007442d40d40d0641554015203c1e8124043c02c035146950303201d1030385560b48080c2c003029001c60301116003004241c5c41140200305220b030b040915401c0039011380508200b0b401c603070714080304401903400601c60746d0032500c95a030380510521013007000a00f4070384960284c0f951050005072455118500368040d07031254030444141d0544010310b0300d40780c540108000c00c07400e40c176400f9200142d03c1e080720424080742d008030b40c3c0b01300b02d8201c0609550403100d04240c000b0910510283d030440c0e201c01c07004e050f940d6030786409101d00d4029000852046802000c1005a01080e000c1700e210303441d249554101455a000d070112040500d10020001d5260040001c1d40c207030780d0000092184d1300700b004210b40c801c808101c0b0750048810042288040c0c40718540d49869010f107403000b0b90060008039040012034030a4480c80031416034550340765192603414000c4005e44201d034078150340c40e5488 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 666681762 1250 666680512 666680519
    0x309030b0a050f0c03040f11280f06022a0a0b1b010c0201020c0c0d06020c0a12080609150f0a0b0c250e0a0203060f060a02010b19050f01051b16 63
    0x2440280380e13104550301900f07481d610701070790f03045000400b2404c040c2c000380040d146141c4540755442109045941c1c12003804c040c0300d411800b102002c01038042d07401e10321450207000036010300000d00d0301c21a4003101071817a21550b241c120042c10580044826603c06094440064804c1c036940082022001d03070008005110504c205035400d458a0b40144411a0720420003034a104002103510403800e10304460084e611509424480080d000d00e280312a000d008880c0075004014090344445581c00c50354440401c20b83d2120100641e6007001c5400d8005001460034842080c98902c10070140120000c0c5014041e07a120740e07403c00e40b07070000310152102e58480f00c440c80b90320000701080c40342080c84400000907030303090455050401c0409040305100c650040301140c05561800c03130080c0e00340b42c0034084075291451014000d0290640c0340c019401110300c202c1803102d420541d001e02c0b007070f2039001e404c85045802038401180d50354049045110481811148400d20103000e12071400001c00d075208000b1164117 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 666683012 1250 666681762 666681781
    0x809010201060f06051b161211010815060921010c0e03010903020c120f120306190510050c010212040f120302040f0902090607060c050301140406050303160309030b0a05 74
    0x501e608880310000383e8200401000b81d01c1000c131031004491014010040c04d03080c2c000391800325800b1141c03400980a180c0400ca04004148604100b802100c5c1d8126080d070f904e0040d80d004c0020345041c00d40380d080c128001d01d5401c0c14001407001100140216044441e00180181d8030309104030081456512000d046100c558420200300a03103c0450007080360a000e46e801943c2e030f070a45290f01e4004c01c0305440e8502c40b5407040c45198000110303281500c11502c44203411410780c1d03000b260134910801124070010841008900300d1010f44d5409001056020291003040e2940e402181d24501c4a640802c28400e94054540340280a6072051b45800300481d01c91900014881101c640b101c2010f01c103200400a1202c5c3d41140c10483d500c062005a0359100300e804540b441c8505c1070084e005030f06088085016a512400850481c0c40809121001d500080200425218244151907042e4402d004e114545610181040ca180d4864284041c041da6603545500000f182120806c00555507071041022418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 666684262 1250 666683012 666683021
    0x1e030109061e0302010c080d09060203010501030509030703020a081c150503060c0c07035001110d02160f0303020a090e090a0b04080c030d06050f010306060801180b0d0809010201 78
    0x301d50035003071040c50480042c0740380a010611020707040000006690044c41100c0b011104d0000c0302caa018056481c0f40d06108019610030305c58203001078905400100700c060040309031844035500d9805001d404140351140c1c080340d0810700b01a010703505484c040701c225090074460503417862552440e1240c0540303131104060070580b00400c0d502000004003c284a0354101145050a80f64003400e04001c266444048103aa6051000d00810b5450290300c0200d500c0c50a20600007065442d4000702c40204004102c03500b40c402101c21072440150900200303120362070b2500a852450b4201110090100306520781c400c1c0c00750804001d84c0825800501416140e90020300b030750252100203410100c6042483c50746035102008140030300300c0c800e280082000c110040c822146a603003441c044944449040001ca0020f0004c0e126041c410002180b183e03030103500030702450003220100d440d010100d03840d22543c503c0c8006070300d400101695491020388440d80c1c0d25810710341c00c0e0f40030b442060703180c05150001a0844 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 666685512 1250 666684262 666684269
    0xf0b06030402060421060203090f0f010e070501080604240609050907090e06041b0f02010e0c06090d030e031e16050f010f110706051e07031d03031e03010906 69
    0x200020410040540c5401040390112180300d20304920914212100042684420500034140b038000801d1040c802000606108411080c0043d507804480c04000b250803200030550140042d0000030040240c0d40c05103c5155001d9805080402c10058541d08020380310080c41d540b0b070050304805820300403298065100806010150b0390340e140740c146030a002c0d088808078071070b401c1403500110010711a506d4036040650b1003000710070340d0701ca003101c084009007400c0002001c81c0700661800306a10080307500090f442140c500c0281060b40360a0074aea0a01012042d80030f410b5041c0801c8032000840743d1010000d156550844a0380c01041c00807004d1030606240000103074106508507100c082c4031507501c400309030302c03402d0302402e02c42c1c03085906c0c1d003080ea644c00321000e4400316409020000a05a608640140685900c552040c461602010004000740c00b8080020380001d034440a140c020001d076104100d030001e0000c0450303040c0210119819403503241580c0c4000e8003800880100200c4001e0300948016 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 666686762 1250 666685512 666685519
    0x5100626011721040902030402060c100b040e07030c05100c0b010801021801030207020a0533091804080d050a0b09130c0f030b060603040201032004050f100816020705030106090f0b 79
    0x1d4600f0383c00d07850301602440c007440c1403055001022800f1961050308540300710020005072004520004026001002100c1d0300d1070049003046c403007034842c00c0b0208469066030f6029400d5486d9500702001d0100206100415405101c00480c0382000b003100564128001e000010000da40d172500f8404000d500b10800015030f05060040c01a00016680c5d07920940c1550015142c0300d02070941c5032003041d070242003c1e00d0951900c1d545540c60264250110082880c100207036012001070b186444440385040d01150050410141807080310415400c0da088150884010103020a6541903c0001210610261548400741c2d095500d0882001a540c40d10b8005241a80200d6012403a68a4040540300c00400c02071140400000080c1168025031048030303010000c008880d401900702d41010003940c000d02030a440384070110440581443d00815240c624800c0d5a1200219260036491040b80c1b1a80f080307070001d42c0034020380070a05850910490000740f14400d004900c0b024520200001c550480c2c044a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 666688012 1250 666686762 666686803
    0x3183c03182402030906040f0e0906100306090203010f0c050915131a07050601181103040314030907051203180301020a0e010f050d140f060301051006260117 69
    0x400403070788070100002e81101459820003180c41004900394031030364842513031100300400c0c00f06035280108404000d45400801c03000407500c0d0603400c2d0350b46850450380b40034800002d120500004a4a40000400ba0b101600104860365640d201c00c040c1c40e200b4940038005040415800401e1504079903e1403082c2203e10401d2030b00c5c0c441034100c001040d480c002d00c101d0b44e5a5159811940c4014002c5500c0140c00000781c0d585035031188004e41c2000b2540c1c0d4640110b03800c025861025200c0c00e8109c1e405294140c4500301040546260103130660002019900c5c0c1c1c2c01414400512030702c07954411501c1c00c10160180d55a0700c010041e4480c1c250740c0c80350301070190384184000c44800da00b0118481c0f20850034240310001c0c01001a044400384a4105c0b0101810700740038503080e0344048402c55501458622249a01c5035680d50181400c9030402c0b039030003403240c2140e0f40400c5a540605010700228180b07080c94220200309082082c1e06c200c00380c1c041030080c4081c205045060302c0c00d0000301410203000365402e9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 666689262 1250 666688012 666688019
    0xd09080d05250206070c020604090f15080c030309040504050a1a061311030612071815050402120c0904020417060103060c050c03070b06060c150106030c03183c0318 72
    0x20b40d0307901300810110511058820410955a07480207032002003504000c00c2c00b0a02d112241c0e540600035001d4505c100804069001c03400341e9000c2038044090034042d00440c100814a000c000203407401620654041c05001701000101d04a500c0020900c45e0165001031941099070070721900d00c140410012400b86004010815007094008480d0070000c1207508820140305000c0581c00c014a9502c140c4404a51245000300244581c001000600810114207070741c558440c01d02082e07216041c407050b45030710351000280110f6142000751824040260005040a868421140ca40103038441e0340d03c41a442803004004100700780c060400c50113614034190781000498010f950340ca008002005041307082136400940f854503544251404841184100c4d80c0151002d80c401050308d01c01c2c0140c5000a0402e00d0001e03200f4028010505902e8040c0c9181c04c02800945070250000940036544080d82103030128542034036601d1807e54415121190701303000d010123030315001c0d1070710306690000ca00016866a040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 666690512 1250 666689262 666689267
    0x2040306020c2b090302040504060b090103050610090c050304122102031603140c0c0a080f0a020615060f070204060b0c0d030b03060c09190801060f081e030f0d09080d0525 75
    0x9000303c950548010555440358a812b074054519281c4080d000800e0400010600c400090054014a98420480d0010303881c0c003003001c1500c040c0700700007000c1401003000c640047c0c160400c940f01006540380c0360302060b0308c1d445e00c1c03143e0f45915031401510a4001c0140007820200720240c50004c0302a0400700018007440011803801c00d001089880c4440020030300030301c15041803081403503283d0300c503202d203585a0a80702d5072407036900802555001485201300090740310058880852203910010412401d002803040003140550002d24103d030441d03120b00000032060600d07005020300d01c052001403c4101001800182190049500d01d4441c1e0b0000051100c0d4a100004031034004606488001d100c0024510103e551011030340300c080d0a41c0307400e40014001003130b4138a103410f481021081d203480d088010500141d1401c103603541e07000c541041100501c14403030b000007441c01065201001c1401049600d505506800602021202580318002c10208010042d110204940c941d01e6810340350b90b00f440d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 666691762 1250 666690512 666690527
    0x605060a090b0705010f0f1a030a021c060b19030519020d0f1122150f0608071b060902010f05070b180a0c0f080c01050c030307050d02040306020c2b 65
    0x110b007012200090010b040c40000c0d00030b80001000b6807000d010307600c0c1c03100102008102421080c001030f4582d0132034001c6417030041030182030641c00522900f010803000303a40095801c1c051804640c0955540400da54549030750706030071303441c5c1c6a045444900301d1640c1040c5007800d00e41401a04040a581c000c440169290850300c01020382214801130401c8040c5094508098454500b5600072082000d903428680b650345145d070070f5920800140201c030408018000803041c41c1c05407100c81c140b942000d001940c81240082e0b8000d620340f425180c6c2c09407070030581ca054450098141d03961a295940c00095503005056a020622146001480c0c08001d07102c0b5552030b10041c04000300724142c4074503c03441100c108009a030301c81e003040110303159582d0303107015405c060400d04c5901400d000f4400115582d40c0640c05070796201507400003440c44c550340c25104441c2540465803c100c59507003448044042000c0d80b010b03050030401400100f6805540403502e80c1d0440c1c0c1c8144c0780e030340710110244855200c0da11408 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 666693012 1250 666691762 666691769
    0xf1206020706060302030129060a020c270718050603090c09040213150806070c0209010e130804090e0105060a050d0b101d040b0705090a0323060c0702040605060a09 72
    0x20016291012440c000014061590000e541907007404a901201c004000064026415200c840102c440041050103100d000307107003048000d60040780440d4010300341031589140101c4e41507041c05c2c0d50380b0780744070844c00c0c0700003920f02c07900040d030721600c61280d03d02407000b035005000c045074a9411031600c20001944d443e90143c40ca0302070f546c01c1d8041070440d221100d41c3d4040410f41c02040c0514240038039a95441c1205104610035072282001040002b8098000b003110140c0260808420740c0c2843e03501203401c01c01520b60407642421a0511002c2440d80015001070401003a0105a0305610b60309103085d101c0241c00f040c4222682c450404c41c0b42c0d100203100301d40c10703030000000704076507a42070b5070300b410040325445040e280d9a14a0400031400d2020412441544666083d40b0680c550719002c4079a0301615882641011944400340302160142150340640341844014000314084015001d040542c10382c4c030981c1c0c074240071404100314602400f810010745001d0b102a41044141c030b0004180d14011721 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 666694262 1250 666693012 666693023
    0x360806041407050906060d0e0304060215060901030206030c0a050d05101e151101020d090305120c040308040e0a1814070b03041104020307090b031003060f020304020f01030510080f070e010f12 84
    0x903010451030a230340201d922500b1003800d0325100d550303810029407204283c00a04007484400c1d40060264504400702c9130507650080c011600350303522448001d0b010750080600c0d40c1440400e01c20008800d51070700610340b040c80d50181d40100a03180a446a01c10108181061080d44010000748000ca081e450080c0000b041481d161103a1152a4207ca00906c00c41c010300c1c00d81414050008249500301008100d01c0d0211500c01c1d58540d40c28000c800d890241d070000a04000040204100c108050030002d500051002c60001c2e0014140e40561000e60390002d00f203c00c1c812194401c80007000503c8140018155001c1043c5985410303604c0961120145172420f11559020002c204210301c1629424050a884401c00340d580c2003200c1000c1008465100440c1c1003030408203000c2c810555402540e000729030240c041c80640740d014005402424000304042c8005625240010310800c0820085d903030701616101a040300c500b03040c1d241402c0c42050b00b00107450540044100a05909043d1240c0f519402c003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 666695512 1250 666694262 666694267
    0xb0402040b0111070905010e070c030212031e090c09010b070b0a11090d0b060f0d0b0402040b011119021207030f0f021807021b09010636080604140705090606 69
    0x1d40140d800c202c4006180801d8428000c01140d900160f5021506941646502c3d8040d580c134404100c1e6001c030100d2004005802c0340144d6500249640065602b001c02400000c001500206028140113000c5649940541c00750079001d1342410728170300707180c0900300008030706d031602000c4e8680c0006094050008020607590748a400d5400048070141c3c1c00c030020045c001211a15141003410591900f80c85817031151000c2049100d45240c141000e00c3c0e1a41c0c4845603804070b650382e80030840101403101440b0b06120744030102d50890079081c00200000c1502c0e06903180500c81c0f60040c001211120080c10440d0b501444042c800714104140010205510140c1c040c8418214400303d00131440b04410300a1040f03102c000c0c8810160046100555840c41440c0381142da403082c0c041256441c1c00703106400210381d070010b03540f02840313030000c40d8001c40c141c0010510100c2c4445013191410b04555020b04166080350b424003080019000c0e64450586d610002098214181000500c108401800842c400d10b0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 666696762 1250 666695512 666695531
    0x905061804060608190605280c121811060708030412110706211e0b03010207050a06091b050612070e0a1403010f0203010f262b0c0b040204 61
    0x140c3c1207000038025003800c0d0f84001c51450444007031480c40b22400c58915041000040d040d803800e420112040c10340c0c1e000007540c003500c503103040001e22915150070108180d41c0c00c0340541d01c0f55401241d8888000340d0b040c03e80441d08d820044410f42c3d079000341d2880f400e01001807502240c4183e050b01e41003500000c0005044003202010307586d000c2c80e10b060981ea4082c2410008082e600141c1140b80c480e01c2c0c140d200340307194a922640048a80a04990381c01004040049120070750355071200c600341101600061074032516840c0e440c9000c140110481e0150346400806003001840300303c0e0092450307180000c0448508100018016009540300c44440e0f0041d5000541181c3c07007107030107804154014210040c0503885000d44044601100d00c032a020b5820310808021607040c510840e41295062003c20304030300d051540700081008115a0000c1300341038840c40795005481404604a85e116800401141c0c1608480400400d18848806010b1065050190703010420100c08968460750490b03000503c01d04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 666698012 1250 666696762 666696773
    0x2070f17040306060b12090c01270b0d0203270613060f0905010e0c0f01021b12030406030c0f031802010e0a0b120906090c03030d020a170408130905061804 68
    0x1c50b8409000241040070000395072892900402d8042e860381c4100505a4901550a540d85882180c5030300160030f060781003640c000e500c42045000c050405401c0002e2740c0c1c901121800d5088020321140c2d2983c00018080c0241e046a0703200819030403d9018a080329420103900d0311803000400c481030b4040c0c00b4414030100141d590100c5040c4111103010000d5201c42d0800500070000da0400c04418842c0360002c0f00949020304000d00324010580c000c16040a002070031262500380c0d945001e400c8030901c0d83c013040c001c0b02030005d0806046907680024007071a1044005211f101c5990180c02454a82005040544108055104403c0d02800c3c03104450f80700c2c401140340000c050b4805011180f0220ba450500001c1d0200386021720341c0c8000b200c007940c44040a10740c441800074090b40c5c0c5507208000c180190000e0360003400100e9254181001075060348012140110003c480440c0d0022001815152210b520050744028105158040010b442c0c80300110b8440c0a103010320302c8003850314000081c10040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 666699262 1250 666698012 666698017
    0x406020915120a060605180d0609021f0905060319020304020a09240806072001140c071407060516051626030c12160b0f0106030b030102070f17 63
    0x10a044000366907040140410b20040800d40c0c03d8000d041c10b04e000064003500c12400d071b036031140c21074800540450950742008083c000c2840e080b5501600d4180f641c2c05a982c110400b07603205100345005045180704180201000581d8002c1c5106007018018040000d00310340c052902c0721a1110016030320b07150b0b4000074a4100c0d296002d011014103120206d40b440d50b082e200340c001404183e60f201c803100d48904803562a80c1d001c0b6007034030005e211701d00c0c0c0c400c000e2100440070000004110000611401a01d210760074800202d03945c40202400080c400c00f0030107081d000704050404040608501c07400c3c203000030700503c03450300d18401506403000c0342e1080c818180600000350b15042141c40100d0f61740c0d0025407000071a1103550241c8100d4080b41c500112021089801d035640403070117400114089030114010b60031000c0e0030601a8440310ba034100184002c0059805103030f000d082450150303d0710400a00382c0780c000000714001c7e40184a100300090b071941c240340d00a03034841130240485910a1600f81d090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 666700512 1250 666699262 666699289
    0x3020a120c06051812070206090427050705010e03010902010c0206030604020c10051005010504030c03030c17031f14010c060906020919050114121603021e04240804060209 75
    0x49140c0700600c01310701048007602c100a001399059598513845201d84003010701641401035041003042040310050b2802ea8003081105040079000c1960441944038034600d080403c600f01c1d071a6005c49414840c542e0040c000c0c06013804220000d03c40b00350254002001c4103292007000b40a0100400030581991395074050300c00d040809021a020407120141010150400380c8884d440d25849400c0071410b54400e00843c0c00b680c0d00002085a030070315541c0c04540701c0d400b00d0000c0c1d0384401400040c0d5025580d480007903009501d0529102c901046a1121074501d1764950f01c40002030403100303400703081c1d0798210b42502d001c150410340c006408017072410300e600603100d00d01c85140c1c4040c8012003800300400e031100040984600780e0b5468650b85080d6101e080d54032540d001000b50001440c005031042116008220003182d880c54054100540d042245414600e0010b036800c0c1c03000085414400300d00701002d21080c0c040d0340400203110480741c00e00a42503650250018040c07680005288081d40c03100290070052 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 666701762 1250 666700512 666700523
    0x20d0302190302010501030210082208040e0c030609060301181401020d05010303090e10060912020102010f020a050c0105060d031e030905030d0608011d30030412140703020a120c 78
    0x81107101e20b0024001c5c002408200d00c070f4044407030480d2540344a45a16031081c000c01c02c49007a00c0394001507a582c00808840100c1c5c841104100201c2c40400c100926405101c89401c4c180e00e07400c210f01000f07240034004102034041c0e890442c50882c4402c4200c0d00440254110300e0340600d02c030b1140000c034007a120300140d520300c0c81e0504000208155122030741d0300c2290403820040045803500940c40722087c08038850100015040b20301401082c180483d522002881400001050310f00c5865001c281c1c1c1016404002240c030101d14144201000c0c080d15500900449046032110030326034000d0402c18034a031408801d010f42c03c101e42d01c014000e9118820a580120413240c40341002c10340e6202906190081c00115424082952070010765082e840710845012000f60039041c141c0800a40340c400c1c412440000f1115101650700c020603032070011070043d03000700b200c08110100030f000603290300000030800c08201020095280400e5020601100c2c040e07114206440c01850701004407000d0300705100c094030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 666703012 1250 666701762 666701803
    0x15060c03050433081003121815200a030c080f18010f08090705011115010f0f0b0a14070602070b180f0c06030a0c03090812090613050a020d0302 63
    0x1402001c0c0500c40030814001e00035461000f440000440341c20400750b842ea026482d07180c20a00014500c18010450b410041c5803440c4d001070301d04e003009040c1003140c2c04030040700c080c4c1c00c404002c264001104450220031610842075851081c95403542c030741c64408094100202c40001004222200341101c42c00341800041a4450002425841c05481049009130200d900da0041c2e17450140181281448cc500c3e0070054a480340c50032006503440d501e1a03007000140e000305060344450308082c6400c1c42c040c01c0224084507541e42070883d0f042900360103810002d00020f0510101000640c0000d00388642004109003e89840f400d250100281c014040d00800081d14002081941818440c608540003100002c46421740343c20341195032914103400c04580c01c16800c0000510f0500c0315004001202024540003d903540c40d601e40b1302043d0030115076003a00052100078000d6800c0100026a08200d0442100082e4140350759050368860001c24000e0080317041c0c81d1410141070081c01845403c1210029071032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 666704262 1250 666703012 666703049
    0xe06090a0f09020d060509060916050d090b0108010609050606030a0e0c060703050913050601120b031203041211120a0c1a093003070804050c060d05180115060c030504 73
    0x70b000e900501e40c1085011701c1c00d000043d6030700e0100406400b500c000b41c000a142d445600c00c0210a0400c440e40034240b010030001519100000d02c6003018450007142ca08500b5410101303058207588859000c814240c1c00d00c800e005007a592001120b4000d0603000e0009900094285418200112844103030361100d0b001c6041000e00d6080002015441000c4bd43d0340701005200800c001122815100c43d40001e580a0380350741c940140754820103070920010300700d561290b0010300000113079004071402c541502203c8155800d280e00318007224403001021002d410498178640c009201030080020010030481d0920450f8244030308048514000c845e5010b9010040c45d066090715034910445517007180740e482d0888407501030241c01c81c3c0e11171130180c503140c002c3ca15100c1341c1040f50085c5010b1b01c1a00c040c020020303040029541c01005040040401c6404035051030089503007401d03d07003a02481c20303075a414802003144905215131000184d031070b58200000034503a51308084a060081d41c01024500d001201481c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 666705512 1250 666704262 666704279
    0x140c030406110f0304120201050103050304090b030709230f0601050a031a090405010204170c090f0c0c01050a0516180603020a2105010504050106050705030d020d0207060207111f0e06090a0f 83
    0x1544558000c003000301407560502d06c04c900700c2c1c00900c0003030580c3d04180f02c148120300054203c01000032000f0101c0f03d145440d05070070400c0301d200d00310b038400c14000c42e6000600346464910003940000c0142d09a5528606240082c00c0c510455200d0340c10107a6901c0d02c06550811000844052000030301014101d00d404c0ca0400d000f03500a000c0c0e0404440c0c0046d0a29980f0400640c0902c1004040d200a00c141c541c041041c0040d040540405590030041c0a004a0414244107082c440c030064034003c00c0e503060801c02040300a9607515040704001c44078451100c81100086500e0860b0300798540160344201d81c00048501c00c0e6120384070b50005c42c190000301802055908054180d90381200c0c10060303642d1f0b42c002564644115600108980c00500c60303140305042550182c1a080d40400300949441900e079101d0040360701100040321410303580341d50307581c0c00d040c4600b412540d04940400d945800282071070107040801031070582c5208660000d205a0151030f06007064004200101d054419540c4403d2003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 666706762 1250 666705512 666705517
    0x9080a0b0405060a02040b04030204020c0106031205220e041202190501090b090d0f0503100b030c0307080106030203090c120f1e2e20030a1d01140c030406110f 70
    0x42e1481e2180201040c01c1403110310803901160990301880346010302d95402c1c00081e411985901d0031a550382d070000000325040b0403820124680503620249d54610b20b01c6c81050701201d9404600a2000c040340c02d1080e00f006811240e005a0840c51070b10441070001400c070700d03283c052000c0704004500c04081408001d015000a501140310320810201f907924040619900c3e150b0280b0100001d215505020030b90340550002c0d07420070880b23810400403035126403075422240e01c10743d1504220000041000401603124100d40d024001a240540c518281a00c3c0540e4664071300e216907103e17004440b41c048650310104100c64882c6551015207407803079002c078101c90007a01d005100b015036018034a280b9819a25903d240b20341d200002e102e5100c100e4046004100800140c60640101074104802c00c2c0301d9061075002d10301c2609045408288102850610360501201e29040f106503030501c2c03c07000b8095020003101b5448010a0841901d079074503401c128020b09034100810303090420000315001c003080c03140300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 666708012 1250 666706762 666706771
    0x1e04061106150315041e08180405060f040f0212130c17060a0f090c0e0a0c05071a0618040c241e02011d1e030712030c09080a0b 56
    0xc0d41d6141d81c5602c001804a007500080a40c940c014100c55000402c0644506400a000d03030071003c8285000b060032946a40d80302d0040e1100390001c82d41590140c1400b00b210310780b0b2010358007407196051010208216101c0d1142540c890340d11102001c07404030707040d4141c6040c43e07450310b40000241001916074040141025051f0f66800048030003184100c10007040010b84008800104160740d40d104075200200780303200615929540f666071060100314440072503400340140c20003550385810080c03e40d4013101c0001110f0710a00500748902c0c40411506482d1503143e40c02d1580e62107640e650040003d480d010340b44468020282c0700310a03c400c0c01040d0b5038150598041c0904615030741907900229610903481c1e10f40c9400030325003004060100e03840d100d00d842440f120b130001042a40ca1081884145e04208400e001c042e8459418481e040c1301b0018403201017045000034602e0100c41d034a8117032594642511100600d500d50400e915a10720410340100188281f10982e036140a25103002941e1604c10346 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 666709262 1250 666708012 666708047
    0x9060503060f040f0305030a0b060d05010602010b0a03031407030207050a09020a020c010e100c021c150b15041a12040807050f2d0703050102040e0109061d010504021e0406 75
    0x440d00b0700c0d480d0185010702c0d000407401c914040180d4084a05900040c2550180e81d210b07000c580d440d80351203001d00902011440b02103903075030514200a084030b03110300c9c0051107821102010008680c021155528401840151542d05d00c02803d06132310307000c841d5110640006441c140020888100c4d03002d0104140e041d402d1381c1d80c00402000450b40c1d51a030070169588404040c1003144102d006040c00d07050b05102500c541d50740004040d0b41415180262820340300d94207210400c881c0300038035206200300d195007281e41052203140702c001d10303c842c0158041d0b064403000d100c83c94010301189905444821882c180e14800514191402841542141104460a115140e80e205000c00040b03101c11144620403050382c2c0d0000c1e440c071005407510040c480903102c2d00500d003010010071400e0000700040c0c82c105607180001d501d06540001245d80c194030504c114403000c0d100080540e0500501c90450300121005a100e9009036232035030f0b0072030510600c0ba450301da000400048481d0085420144034013802d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 666710512 1250 666709262 666709273
    0x12403120906120c1e030212061206041b05060f040801050a0b10050904020714060601020d0815060304020f19090e16060507140d0e10110c060c1609060503 68
    0x1400c007980c41c1803a90003070701c0101e00c28010300310b041903541e880f61032000110701d003101c4203405001036a40801048000d0b500004d400040742c2030f400c05c0c0b07005580d0f005030080d26140418a510240e80e07858031409000208003480b154501208054200c1030607010b13140080c81c0341e5850701c055143d0f0360154400c2c0f04030003482d401c00c00002c22030b400c0c500c9070800c0004003505004d5003420826040754181d2010b550598441da0910460004c141b01c07502d000f06800d54080201001c0c107110002a180200c8501884100040c0d1010003042100e0105000c10340c040c1a600a91aa1618800211001e120402e401c0d00100f07001071103c800d60144207200126400c0d5141040b151590051603a103c41c0e050b11624409504004100402c9201d2001056214050540d8600201c000f000d414103082d034031704240e40080c40041140f0b020345041e4a80c1c5060b103606040c40c0c0c4074044403640c51074844079003484c420b01c1402c012850010004007400020500c0e03090106640340030f5211302040700142428080e5602034842c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 666711762 1250 666710512 666710543
    0x1b030c09060905130201090b0a120e070801050f04050c0f0a030812160309020a0b031308310302011e021c0216090606050d0213031403030609060405010f1205012403 72
    0x3c059104ca03505030181d40300d04001e82800300300515640040100c07410418880300352200003855100b4071070002d0440700a007402902e0084d11a00350340016000301964400102800300188000401d640c2c1d9840560368441c410769090300181501f04c2c0c039440600107030700c00a80304c2c4541d010803603040e10800001e81c59041019011404a044131f1076402e009400c101c10040600c1541140e4010303650049848465560002031950350804941282002e0700845c074101003d0003640f0885001c00d42d0822900101e08482031070754000034241d0b50b00c140544c04030130b03110641c40303030003442800400c0c0c10000a40c1c011b9202d02c05504025a2603400501c843c0c07092142d42000309441c807040c040d20301201c130305956a0b4140f00070411400000d500c81c3e60981c0741202d0b210307800800640c42c06074121101441201441c0c03a40b03070810500c001000700400161140d0300c2c0c000148003400e40a10050141c40c044065206a00e0300391030000d0041000c61500841c1d9a181598241c0503014041c480302640d04c20401c10b503103003e2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 666713012 1250 666711762 666711781
    0x105160303020c1e2a0604121109191a030319020705120d20010501060f120b01080c09040603020a0b090a0611061b070b0a0509160506071b030c09060905 67
    0x1003843e0385908917000001c80c50b40480e0442c014080c41a2000c05942c9005d940e0000910070307a0160388603c02d104c51721031091303003032091b81fa900419080042e41c00c0a850b140480f509480c1c0d80c6002c8400b18020340d00c0417021502070300b000270034440e108060304580d80c03000340204c021005080394004800603c5a568080f55504040b80d010680c0c420000007405000408003013965101c00c100011220000345540c80e100d1030009004980c02050306884641680e5044c28004042d11041724070709403040c4c10310220b40d440366070046455601c050341141c0141c4800c1c400000401401c0e240e80b02030340c02154070902051300f0b1884401015113070b1044400c480c5142c0d440500b540e003012210b50210494110200150b020f5070a9110302d82d120102464207494100e90743e5070260003036816511542042ea0f260104120304c5020090651604a8100c10b541d4075490003000076441d01ca41803004100b520a51202d0b4490a000321142c0e001c2c5074000c02e04003000340c540205000503c2507105400c00e00342420041600c801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 666714262 1250 666713012 666713053
    0x24050103110406030903020f030f030708090102070f02101412092404020f01140d061511071a04030203030705060f01090507052209020403111e0d110105160303020c 72
    0x60702031032842c00d2610346841038005104e44642901540100450001c1140c0144010718070030342007a407030f2a2a4180309200038035080b030080500406a104004403800f040002d1749007402280d040304c17a04003510040c07000300c6008101c44a50008070038003081003c81c1891855995105941c07010845c0d507425004158428129020105000620400008240903007403180e81018240c0041c10704044180c200e040502aa51100000b55120703075541109000c00452000c20300910110391401c8688500c0f4540c01e141c4070702c041c0c4944c001403403040a40b1180920b055098400850300103051300d403112036604055031180c0c01100d802200034410000415501315a1040340d000303000c0c0d903891605042e810118255800340c15020300405a4040780300041403052030000300080d500c1840d01d901244024820b00594201d5a03020400f981c040b40e000914584842c00401512500585041d070382021701e1005071180c1c85400061071103800803444420505030190002c09611120178201d61114a02004400240c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 666715512 1250 666714262 666714281
    0x8010e150901150e0603040f020307061107050603040507090e0d0809150123100e01020106091823120910140d1d0a1a010b0301050117091024050103 65
    0x501c1d00c401486058100c40440442c0d001c1070070481aa06011400a005c0c0c2e002102c081703586820b000101c800b142020b1041303500928150415400034401c50b00c0d0640c80b410640a100e00a03c0080000303000d00008008510003041001c40c100301303004124042e6600d580c1d100c40d5801c00f0894400c007080f07404030f001030500c44641244460081e207908003814280c200408042150a1444883c0032103039a40d00d10500800100c89510340031282c0f040203001a09451a9902c03d00005107414100080c0c0c031202d810b4650b145501c00a206d1402150a0b0803008160481960303400504c14014003008001440700100482d10303040762148485000c842c401c4880e540c40d40602a40f081040c042d459001c4690b4112418050090091548000e902d10b52540303072586810040d9051101100038099405403100703070501625a051403140703558140000a40021528041c150349074071104001005284144050b12a42004002c1845050070030440201c3e0700100101442544800200010740c07507010740301b40040d9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 666716762 1250 666715512 666715519
    0x905090d0509011b110310020c2503080f131e050405041a2710231609090903170703090c0b090a051914060f030417040b040608010e15 59
    0x11041d1000085802110b04d07604031668800c0c8502c46801d40c0c1c00f445481c2c14560807010050300c40300403d041510b0402d21241301c0068410010401d00610381030750807801665000815196030b0404217a04a01d184100b0040c64080750f1924000302d081d01c0c1d040318040300c40036030144a20740d950f2038030204811200280c80007071410400d1108450010040f20304c4a9110100e2054203800103407124508042503c0640b00d14800d42010b10441001c04052150340e100c103199000c40c400460f666005942100f0014209040d85004001109a4940300b00c0c0100042d003210034050100c8030b6140b602803c01d0000700c1e084030324070205100068440340f03c1c1c450381c48480d03041040c10310710602e0314400c038449920035a140358014040285c040303801d0306d52403059200c0d1f041d40c1006003001441d000b2480310715083c501c0010300c240004c1149000708400034050b00d400a07040304240c03610860481800105200b00c0d4440341c4100c00110700001c40c07540141c8080e04072041c0391460421581e0352000410241d2402902650 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 666718012 1250 666716762 666716777
    0x160312090e0708090f030435060703022802030c07061e0e03010605040c0903110405160e01020703050f07060e0906010c0f050c09041514090318030a020402040905090d050901 76
    0x50103200b4042c0541001d0384d08103840d02104080c050310300b503a2060300b08032403202d92000640003940c00e4040c030313084c2c0d05100700020090f0805400d603a5150800a8826820590082603019050652100704410301c00640c0c503007280c0ca000740902075207a800000300b1411b86d0281c0c18001811038042d40341d40c46000880440750b000320be030bc001c3c141d5440d109400d050350151340c3e410303001c24a915148508004544152031700c1404a246107000c5038001644107225000b107040c08180f0219008002c4d6031100030f01e560420b14200a03030800101c0c0340c4101540060903603c180d1200a202090101e00b075000c5d01d000399200c0c90041441e005004450380c0507254540000c2c00c2d41c0c040b1000c00c80744240c20b40094491030a50341c48002c0302c00014070002065509445c4d0031590643c555196100d4421080c47d1030065030350740f1040c038050a149460703005092401c0310400303d5160124240e5800d0010b8090381e640100110344a0740c46d16010b80c000d01d000c891501d1544650702400d0a294000c5050302c200542c165290784 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 666719262 1250 666718012 666718021
    0x106031b09171e03031f03020109090e0a050d050d150e01050d140a030306150804030e120c0301021603030b0a3002030114100b070203030d05090a05160312090e 70
    0x48040d200450618600d026a00c0f021403c200034200c1024450310020043d51241090b500300c256001070200000c1080e038400c141000103036044a94041103600c03030080041c403081c1b01c400460030310030040d01c020964050455480d0806802c034000c1c000c03001c0490341c1003151419032521400310310309078021110150301180040200d4601240c01d0111035103d11500724011880180e582c0c03070308080d41c0781200443c1d110030060041702380303a400c0440c07038a000f840c020540e8100b503200505140485a481030098403411103c0401034800c018075030f0b6090f0090001c643d41c2c00454400300f001c0b41840c0c0220006070400154101d949005850301040da5540c0801540801804205881781078442902c078640c1400000311a0141e0303401c2c801d0000b030000e00e250610151500100c90213054032540c210000b550f0003401101e000d61800016078000b820341440009560f01c0b01c01030503240072558200145207128401420703000c881c49132844811240304980a0b4030403000030000380c540b51640d00034210780c080003c0004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 666720512 1250 666719262 666719279
    0x60b1305090727060f030b010c120504050312030f0f06011202070201020c060d14061518061b0307060e190609020a0f0b0417030a1407061103010e0106031b09 69
    0x80c0c02c541c15052100d1500c0200c60380b80e40d01d0310f550740c588039820302c0300408114464022055060882c0341c0c0c90104500b0400c0800038180c0051840e0181071030f214060340080340e5000301c1c1250081c00f8020112441c0721605001610250300455072b0380c0c0d18017000c20100721251040c540003409094140c40740840800510b002c400290083e140c203034114400c5800cbc41009803a0f4a0003440100341d008800710740392240300d4034921a088003401d0680507070401b0b001e9000d00c49241c4259080c8881000e46400d8031070200000422a000718405a194445018040b0004a2001008081240c42490240440b55182c0c09194940010012150a0084040103080098080d60060f5100e40c801801c00500d2a2550120621001660800d052030800040d05001000c640341c1d030010784441002c0214940b0b413001000405405204003294031a400c003055050030015280c00005000c1e1002c01c09a40369070b990ba40101c100304080c442e00300803d140c03680c00a8000000d10740050107690607150051300710301d8800075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 666721762 1250 666720512 666720529
    0x30512070507120f030e01020f0607050c0c09102d03060e0a051e0c0a08030a0e0105071a0703110918060f03010204030c050a0806010f0909030c0f060c03060b1305 71
    0x840d800c1c0221840855542281c0340f0001c1034500610281e07085032031918018281a103000c030114190341c815080c4042101d40003400582c01400e07442c1c03c035101c046116003180340014446886501940d50800c002411151f0482d28045481c900c4a4000b8209680b04404002d10307803c3c0800f0400310803003024000318202c0d0300083d140c25012070441c0d40b10101c030340f00c560030312003040c0303074500c0350001590003418803c000c00c4480c2d807211003125102c02c1c1900e801c0b44159a8481e00b4600f105011244443d8681a0702a0043d1103e01e608401803021b000c03c2d407041c20511410885000011030b2825002c0407549414034180c843d0744101074260815100030201d09984440300400c15a0f012002d0214402a51400e0003d400150b2154516902041c20501000030fa952680c11481e92940040d00410075402c0e040550402c44030b19101c000740004880c141210400c40b001d002410410b4650030003400c002c0c80f80d0259103069140d65081000c50f032640103140240c881c040032070b885130b50300c3c020502c85890310054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 666723012 1250 666721762 666721777
    0x503130206070209131101020102040b0702130e030403030c03120b100c02040b12070509070302120103030c0215040312081f180e0f100507050424031d010207031206030512 75
    0x40941440d80d0b41e80014a907180c01c0f0b80142d255104000c1c00b4003003001440c401248014240025403c0600f024020000e5000d580f8000c0d2007403800310103a4070010500e500868902e00d02800740d0f941c46803030380bc1c0a880203c603a40b040700000c280031140302ca00c002e03e2280c5e10741158010b280f04100f105100d0300f00c461019060041e80c0c01a9241061806541c07600d50031013880d1034070800760010528103005c01c540780200911f0a424107004002c18a1050300309180103041d40c2d81810700c400c4d108400e00200d040650301e1030440611540c0080c01206000002942c3c915107040780e903429841381e40d1084400300c8407000d48900c446244c03c181b0244038241100082d000780c514200400a070300d00c40e82d0307030151030f02c060035036032503034907040296030291044580c01003540c04000340c20007501c0c240c070304040c181d004030a0403202c9510342102c95540390701900ca07401c0000202c0b400c0d4890030b0740b0446211094006e62000300101d010540101c00a07040f0700d694041c0d1401c498000c8082d01080e12201200e050a52020783e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 666724262 1250 666723012 666723019
    0x6220b071817190f0b07050c011103090f0d0906030b01050d06030b040b150a06140d14091009080306010c150c020a030801271d0a050f011b05031302 65
    0x904125038140700d940800914a240304241854120040749003000140100e0400399014501c190001c5000d81c10401451503022030a038003a0f07618180c08039124010381544041550800c0d0020107420100b40286d0f006000c45004d648080c082c50030f0055071a00d9058440010500e014402c000c064020341c403521500c841814002c0c52711422420301011160140c00844050302c20000380001e1120042c4100d50113805000311180001e041000035100f100301d841500c00300100700245110b90311100059890000017104240304c00c0f41c0c859500c0c0d4107403800325018102841079a040007840f64641c096056050f8103c6800752454450400444501b151100192503040c00c0140e81c2c07509180a103d0100808000e03800743c2030000042c600200201810f0380031201050341c1144910341d0b4002380d81e560301100c140c0d04002499480c07500c034010304030844240303410712802881c03003940c14082d01003038031000028180c1c0200078170382944142125000c0e00302e954400144040c000541028614404401c50381d0005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 666725512 1250 666724262 666724277
    0x30f0c050618061e070b090f1b041a04050423010b130902031509061006090819020109050a26030a02060f06010c060c0509190b0a08130807031106220b07 67
    0x1007100e40c1d03080c0d0105c003049484280ca001000300f541d000307104001444554070003034801142104401070008240c0c01c1d43c00d1103581d60f108980f0015a0f00d1400756030320328015005004514103810900900c5c09000041d801242030f440381100c41c02c01c10301c5040100301000302402c3c2941c944021000007412520001c0380c0603c01c62001548411700344882920801c0800c0040c00c4078034046440d0450250180e000d1018400c084000f445582000300c5c40900c2e05598820358408440b541c00101c3e003135413403540240c0d080a0380c03000200344d440516540a004400c0f400311001c1c0f4002d07400c111681e920600741c840700181c0012000c00c0070610611100b0703400260501d0242c1c64450103894440403240d040c018400858800980400c480c2042d480da003010703c41c0c0e20304085480786440c00d08070152081444603170410090000013010304404086585841e500094031780d494000300e140c0030f0440c1c40c0d030203030804d00351013031600040e15440b1580035003100c000200b80340b103d00c0200740d0703c04e0428440600158280070f080e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 666726618 1106 666725512 666725557
    0x405270c0105040e13060c090f14030705010807030207120309141c05070f0f0809131503030c0f050f1e01050c0906090a0f030f0c05061806 61
    0x10b24100d0f9130980e64150102c0001c0c410020041c406880c001d480c601c0190300003a02002d541a0503900c84170f080d280c0c0c08050350726100c2c80c605645036001040610895220348000d54000505060150600c413031652000280d580c141c51440c0003a076a01c07046800c2c890f11603640c11180d03e80902914200c01c0c003510b440c2c82035519141d400c09000d0005042030030800142c5090000d280c0040c3c0103404140e092030241c20395400105030750304c84c214a06201310f12980ba4031400001480348003a15001614664081d40d071980b0b0440c054074620800c0030144080f820900452819030703400c1c0c000c2c0c454042d14441862141003401400f00305c582c50541006110754007034049810902040390f68a860300d00d4440024000701054210b5031900103641000410003c03034000540b40240310782d0b62448420b850300140030080c0100020920203210040c2d4010f02e5040c11402008110314022404800d181c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 666546762 666726618 := by
  have h0 := BRFrame.cov_init 666546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 666546762 ≤ n) (h2 : n < 666726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
