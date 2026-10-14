-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2040
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:54.807745+00:00
-- url     : https://prove2.me/submissions/59065376-f319-4b3e-8aed-689628a525f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 366726618 ≤ n < 366906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 366727868 1250 366726618 366726623
    0x30905090a0b120c0d0b1b030109090201090b04050102060a0e10020a110d11030d020a090504050c09100206060a030f14031605070b13090b220903021005010b0405011b02030604 77
    0x80354401007941d441d01140810081600c100103144100c000d80202d049003407401c2c40907211402c0400002c1003c405000d1f00120081100a4959250307160b03a00300000b070a11080590004200110100c1d00550440488040c1c41058000306030a90b2101d101c0000307010074090807a10b900407034840070b81c24078140c0040d01000300c03540c9444680310501c02d045494080c810000400b00401b00f0194440000c000c011614401203800003d42d4072442120103031103500c21035200980041ca4801017000c5481c0c5000507003028001151001180c000281003280d0b541c0e0150380c03250f0302100c1594100b000074404803c1071a0140f00d140c60f12466a50401d07a581150402541d0542c6d01c1c0842031003004105003444190060300170340c20480d090001c46d60f40018045150b000d40c680b0155100390300f0029948889159800d90b000c0c070916040003030178600c0000500714010040300544100c500c40c0c0c0003001c0307600a4a041c0e454100146c0d0a2030314007401111001d00111a19035508103008801002da1000e0182520890 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 366729118 1250 366727868 366727871
    0x190e09160f030b0606040308030c0313020a0609080105090c101803080d05060a060201110703081e0a150501080912071704030b15090702070509190e0c010f0219030507030905090a 78
    0x245182846650f481c0300600c214405c01c010441440020b84d03a1090726040000b100310301c0d45070b42d545900c106828800c102d000c0c0d48020020030009455600800e0380d4160343c5c8600c020b000c503032240d01c0032035503a00b110201d007580491060b1a210300b29100d4100804030001c1c0101c0800030542d2034458a50550100b40411042500c4208004003820a042e401005014901c0204054402403080b0340440c00345c064002e00700030700b4001094000e1407140b148019640c205020300381d542008a0f00500070010700c02100c8140112a10000d15580145d103028801c00050000e444401990b0100454030380c000401107990388040c4000c80e48030001403024001840c0310700d42100490038001d8841800d061100b244034890501d07202000850748d030100d899411210161200301c415250444080c855035900142014510302d0400f030b1501000780025926040d400a899030303000c049032a1000c903126144080d85005100040041c54002031044005021460180c5010610283c4810003c1c41d008819990304911a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 366730368 1250 366729118 366729149
    0xf030207030206011418090c0a0e09030304150b03012a0e090c071a040501060602060f0c0d050c0409020d1a03070b0a050a120606030212010e01260109081314190e0916 73
    0x207003409d820a102401c03511500c4844c5140050040355030b40710040000f01f00500880001c20005403581101105802c018001d020300c14844090314151003580d542e10312150b039182c0d101d00c8814014840c09180c9400504000e503965180400c0b4040c03039000385c8089032114100da0b0064070b0560700303001e2240654810703000441c0c824030740413009281840241c403403005101c000c011b00992841c0d040803244200e40b0b07900c0100d61070f90340d1886007050380911742c05040d60a00001d0740c0d00c00002294841d5103804030900042ca101c40600e0305041d51941d4a014901d80b031901080785074220380c005c0000e4088800c45141191201c80c162074008259051a4441c2001c2500445d0642ca000c40e040d00d481e01400b443d8204150541c5047e4034007035203170003407a210480c000b403416542080c480290006013070240c000140580d5031085400c28001d030307600c07442110300781c0c008082002c0c1d5a140032071294420310582c0e65400646810440503002c1e403000a4601e958a200b101120394404509541d0b2400600394440a0450f1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 366731618 1250 366730368 366730393
    0x70e06030c0414070305010b040506041205100c11120a14280309060e0a02061606060e0c070b0112050c040506031906021b0705090112030521070f03020703020601141809 74
    0x2514810b800062300c00f413042c403050100d9140c50065504560304441c1d1240301074000d0600d20305240340001c10f43e20341801c003540c5000150304110b00100c800216001c03070742048001140c1d034480340540e0b5520400100e11001000e29075907000d01406003d410002c07100c0203049150040b06401105601110120303840745240003d12001d8401d07440344c400c0d10009460000d0f0140d0019101784600d403202442c00810348505410301c20345034442400303001d20204161aa05282080b01041e800c260000c6440020540c004900140c2c1c80e0580e032041a404401441d214009100f000041d05008042a81600c1101003440c00d000c000342c446c005a9006040c0142d0b900041414400b44404100303101007941d001c840c042095482e6490300c1c0d811115030400c607005103092403030300316010303c9100014014080911103840b001000c0f100b407240500d50030303241e40d02d2041c0808426400d0380240d81010b030250b002100108034000c0d40d81b0000700e05034070040050701001d02d10045800544016101f41c483c40c0d1000f50040e01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 366732868 1250 366731618 366731621
    0x90504060515010903170903031b0c1c020d030c020d03090501081602073005070e01050d0503030a0f18050f0705011707030207050a0209040303150f0602070e06030c04140703 76
    0x2002161680c4410726240b080d00041d0048003540300003414501d0210301c0107140e295003025251151001829240e8881e40701ca80200003c42812800200d070064013002c1c030b424a00100309026515200b011030400d0705c43c0c0e8081000c0e600d40000103400384100200c941c80140d03034096134605110303c240c070307004402410100010a03640004000ea1000510704864226068000510078100c85041c144e1214100c1e200031551454122490071294031a00c4032104000c22001107001e400703075000480b008405a03603a10401005a5500720007600503002000800c0610b00103801042d44014031000101e51482c8a03022500312121030041903c05030800880040d4841c0140407200041000b442c082d0b6225550607400301e25210041d084000345030b4000707980030800c00180006184a034005280700800e281505024000c2c10107047c86003c101e441c14800700f4200001d40c0010260341c0389034001d020890614202148541010300710b0341d40751281c004581a00e6482d40100c81e101520040d4052142c101654081c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 366734118 1250 366732868 366732871
    0x1906051c0204050421080a0507050708071104110c03124819020d032f0c01110702030f030309120d020c07060905011106010e0f041b0905040605 63
    0x920030400e48604811540e92152560030803601118001020340b540e1030a100d2003082d0000c45500510191210ba08a42e04a182d04d0311030108808203018036a0303001c80440d0340d88030b500b400500c819010b200800121b41c14009924894a001d400042d824248002c024065005005509200e42c000104102c0c80b2100a88154100a10003503092100da40c2010041c01c495460510820241c0b00002140040031a106085d03031b0552840861580c1d44452442d1800b0400f031002003c000d4800d10203041c5090713200748149101410081c141c00b4800e81481c07031040c0d8658040c0310b007186082c800c2c0400444680284141000134140030b03002c0e40c0d039003120b10515052580c0881c551a0300e41040c010424036101c04602e0060b0310071410f60265441301a012441d00034010080400d00d80e205804021503400d270000b20710402d031a4240c841101540282032121b0355100d00340216081000c0c404007107071164050000306500300b480741a0030741c4003140c54045141b141800c0c0c2d000d00f0b00c240d00c5100748800d0120900c12117 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 366735368 1250 366734118 366734129
    0x103060204051311041406071208060414130305180a08210c10051e041b0f031a090312040c0f0512030a0c0809280b0a021b030102121906 60
    0x140404882c07904c1a000074000c5114494100d05020180740712940c84504580070380c0d910400c2861486200f00c8003c00450044903602e010b0303880c042d101284190b03a40714181c42180b0ba041c1000d0071230415602268240c03c9503440c500c002500c244550b49542e201e044000150031080020802051400e6610a2191900108980340b81c010000b043c000100400c2d40f001d1622104000b01d00f40e00c50800320901032a40700034070325250031203a003840108503007041d0104441c04c0c2d0043c2c028400e40c031104424050b4110b80b20007400800070341c1070072202a407081e1030554002d082d4004c0e00c0c2009041ca5130380c0e18000089608a4204060003020300098103911a4030018010035a002c41080001031841d60307891280d000d000e014001100f1190b010070807000121a603c4d440904018209076580e029140240045450409140300c840404181c08070010b0655110241d103a00400d000448200314640c031b80046542180c155408000700301c00c5c030140d140c1803402000c2000c0c80d600b0041844500d101210070030f4105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 366736618 1250 366735368 366735371
    0x906060b0d23060d0b06370e060607020409050f01020c100c02070b12040c051003020406020c0303120c0304060207170403061803020622060c031e05090703062301030602040513 77
    0x43c400203407120b41c1c1d40d6001c241d20040c41c0440d0f440b141d000509883d580700c55080b0111062201003164170f002078041407501d04903281c07003031050780b98100d99172800c20440c0c00a0300b0800a01146001d071406400003000c17a8001c90980f51220100580c0600b640d0003515051800c0d4040e008101010000c0d1107810214171051010340956820070518052605c0f41d07000481c008103000000c5000e0100080452000380002090324040450801d0050003a41092080d04054040c000c400d507541d01f008011240000f2180d401c40010340d0390b04a400d00303190006041034808030390910030840010240c200014a05a800044580b290b143d880c0c000c0540b01800a84030041d00c1703040815002036000149180c0208581440003082a9200d00705501400c0100001d0031150409080704d0380a60594000040b070301d806011894445d104800c1102510001e45100138980d001c0d2004002043d00c50784030705646800c80034160b10284400d02c000c4040711b020380080d2800c40d0700103420002031904416014140310b03101030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 366737868 1250 366736618 366736621
    0x10020705030706050d150f061211070308040302030d020d050f01050d050c0105030601020c03010f1401171506120d020f06090d020304031202070b040605030411010516060906060b0d23 80
    0x11a44482c0548199000d2020110703603880003032541d400940803180820154090070750b0725501201038030700c0c62042d940400c00d0400703c1d003170604050181000b045400f500365850004580e9003111200d030f00500035030441c04103009141034410103000810a44a071800c0c0850b6600b040c503404040c080d410f0748014800c080072075090001520128a00074869804d00744079071039a9904005030f0030319100302c003280d41c15440c0c04c4109018160700d034032030011030383d071260004032070313a00d400480321091140903c10010781d0041240c0c0c00340d6414600d246611801c00740100c0c032070940c008000e81c5006a1107195102580280c0380c40703506004204125a400108040140401190789801035180d218a010103001c0b1000c04120500c00ba008001280c024040c000d00181d6580e941d44000300107800a8038201d802c0c0768420004902584600d05540b07101251144070003140c140c540d20503004200c0490101d44481c1c0310640011481110f030043d04602c64502000308101c8603c020600605242e000341e045104800760 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 366739118 1250 366737868 366737879
    0x90812011d19110c0a050303190603020102030d0216060903080601111c180f0b1b0303060a052103030109020c191101080a0e030a050703080601020d23040e04050606100207 75
    0xc00300031000b0099240050421030f03080ca000c180d849061445005445100204000c002c0000b0085101d582d9250401102694841d004001c1e9001da01c400382c0140c0c001c1c4040010a1040e0f401804e18088030821211541e0056540805950651005501040451040081d03c1d60000c4000700840d0307070740d8080c00e5200841c0514040341920a03070540e08004240400c0304011120407000405001400410302115940d500b110a00d944010b5a82200b00510f07400440c0c0403000100f035900031000206a201c0c80703400e1806100d42419003010004a0703260044a03403151010500007140a030103450000b698441610400c6c6142883c7c01410500c04044041c6175008103050340ea09260401003480c0503c4030792101c0f800f00c40640300b00703044501c140c0000a00c1c0c0c49083c1d00400140130b254400c4d1a8284d242d43c910340160388400359260b140e00840c032240041d240d0043c206215001c0200300d00d18040c1069242d2800b400b5100301106d04031080e90100090200d54508059104100c00032880280340f0f40b400e10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 366740368 1250 366739118 366739141
    0xf0d0309261804020d050f04050d050c100c0c02040e100e06040c03020402220b070c08010c02070b090117010b0d05090703080f071707031e050f041404090812011d 71
    0x103002c011000e00d024070400e90b4858045076004000c1c0e0780c042c410ba040188110b40103140a8a0440f454420111140100350260090b1144c0c440b004c00a00301580303030b4030b85600280900110701020000581c04c00d03001652984100d486602c944001403184219900282040b207041d000c003448198000000c1000042c81c910380c250942e030b4141d40150b200c50b00758440c0c080c000c0c034212812882254401010a240782c3da880030301030160040160089460799403060360b00700c440c503240d01401a007001030240144844880103025008040c035140d02104c88940c036140c002c110070f0f0089090800c0000ea688089a00c500400e50070401c5000501001803940d607448445114066903280c84c1907001c00c541c0e00344010016071722422010440310035030741c403024a0010706030704800c6080c0e0000b81400091074180b501c22816140000012840207142ca8101101c50042d0810380810680c070541721010b580c0014610303005810000d11025880344a94182415440c040b06141d850f0078031001d0281c10170600383c425 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 366741618 1250 366740368 366740377
    0x90605030a080702013c091202191809050d0302030907060e1302030406050a150503151008010603030504090608030a08010306020703021e07030203070b030601080c0307020f0d030926 80
    0x146450f507400441c4010303219135001c80c42e0301d5080b20f80c80300036030b807031003c011030301c180d05101c0c400310302060206240e0960305044140900754400760161109801428a02e21000080c4982c01c0858111551124002402e003401c5403004030954617503190104012003003290140c9041d01c1d040641c118036105080341c3e40e400369032184c4401c0102202d440c540e640c43e40031100340d029514440540d641c1c5402d08241029000c20740780d401c40c00d80760081d1940c07a592040d580106440b0002e026221030708680f014031104c1100507240c4582c031030742c1c0c02c000141d1440c244142c0008503c40d40301d19884510f00348120080351a5580040e040d90410002440c02c1c1d0743c0600c0042c1501d900c10b60050710340a050504910749a0040d110a0101e03d0b643c00b001028100001c148080742d10071811240a20703200c040c400e038203000c1620042c1c00314001501042064901101071984141288112500328108200091405041410704d02c04250781c0d0b01100d0074804038108849000400c841c9482c401410140d8114142c441c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 366742868 1250 366741618 366741623
    0x60206060d261216170403080711030c160503060a050f04020d06150603020408010f020918060102120a03021206010221130f0e0a0b011403061c02030d0e0901090605030a 74
    0x5000d810b420210080c0025100740d0030b0740d0f4221103160f1404180c2c00d41c03005001410300c00820041e5030445001d4110180e898816640343d0349283c1345072100c14040e42c41c00f014502104a07070105104001e2001c0e0108603c0b466055084c500310314040c0341100b0316051030743c064510704040e8100820440c00f85003840703c5641103070341603403d008081a07506201c40142002406580400d04000340080c0095068029100359080b81c0e00801c1800408a4040101d1007000c00702508000715184110349004111541540300e10103006030b4030a80440030f045074065105201036008281d0125100307482c0e83e40c1094484d4046020b00082501e510700c00800d01e514038200c0c0c86003504100015000c01c010f0740c10b28201004140300c504902c4074076102c2016500004d804c4808038800c078540750740200c20b50700c2200d189400c0e840409425285032228000e2100c03400440c04080440310304186808016282000b42c0c1890f0300c3c460340c2c0e601d921005041000000007040e445201d4a50400c02d090080b81c0d03010880401195 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 366744118 1250 366742868 366742913
    0xa0b1828060e01020d050604060605090f040902061201030b0906010609030201080f070e0d08120603030406050304060c020c100c02040c020633150304061103041104091106040f060206060d 82
    0x815481e045024010b400b1101a180d400410018421711040d08003a01980080b03034148000e68452008030b03070034000c1100300ea41c07008060343c42594905050703001da01102c0c000391100d854140504546806810280c0c0f08940d007440ca0410021040d4080c04040d016180070710303220508a2a58000a200001c041c018214514004004c249250b000e0480040e4809003d0034628419a590400200c81e40002d80038400d45100030b0005240b074a03000c021103050f0b03440b0b40c0f102c07170550b180c58955800520840a1314000e600c68a07044810070707075076012912580501540c40e841c18440e2841031005944000c2c059100b075500520074401d0085052058540c0401942d05030542c481c1c1ca0342054607007030204080690407402e44510071034040c2d0000015486940542c01c10320682801005050040c4000c40d8050400f84541c0b90502035440c0a8000c2800f003800359030b0004000c0560000100f072548998030040a031404203070704114840e01401005c0d0301400886110384000c1d241c2c0c540c0c41d84260360750040c40408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 366745368 1250 366744118 366744193
    0x314040608160306030506101d0c0a050a18090f0f0605130e0a0c060c03080906060f0906040b1207091a0a1412010f02040f05220f0e0a0b18 61
    0x601c0f035400800115004011035899042103480185000c00c24001d640b990130850344614600420a6aa94019094550f00318601403040e882107440390488146d10081001802c001107110a4880280000e0300300000001035505128030750f1000c44800c0d07003c1042d11414074508000070b9450542e642c00c0450703082004503011060104241c20100034010050005414040103c0c20700d51003d48480d05910036194000503440301d004d4199203080031181c055000600100f40c02035400c1c5414240e80141000e030010807120fa520001034070500c030070010200303254001401001070f051140200e941b0f041550741000044190b050210380000d0827030007900c6009a503000c5042035526010403420704506110000c0200b4041540803d0195110740309000c00583d550b00080f030580f510351001d99110440805c65044100008074400107402038107800c070b80c000e81e6581f059203558001e0002c049098071640d032a80440c50116a003980389001806e07030406035032092607040c810401c202c0101003413040704454a10354 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 366746618 1250 366745368 366745411
    0x1020115050114040b0304060e0c011d060d11030a0c09050103180204051e040308010e010b0901051b011b080f130803041103010902040f0905071a0f090f1801030314040608 75
    0x7a072081740d0100c08840c200004100034090705501500250100c002610840c1b98942c0c0111108051440d0b10402c280f1110007040c8140340c02002406605c2075142d0201d03c12040c042424103940040326410b408e19250b401200500c0d82c0b11901078050304003402c0c2000420319805000380b0940642c00024090759441000c00c0b10744403c0030b07000b00c81036840c0035103403160310301894000d003a120284207406084888200110313030303041070806960030010180d46d01d82c00c08500c400c40e176000e14128188041c40355650142c0720400f000d50151402c031714400e070710f807480d490a14801100304107500900c540d14001884c03c14000042040d8100da401a80082440360100c005200003801400b490300001e40c03051030301c1f4401c003002c5141c4d0043c0407054000c40603607840765542d03070150100c01c001e6502010090400c0140c1e011140c001c8024010034000502801512141e4074040f4078a6120500104510001c3c0b40041040581c840340c1c034591240c0c031110107410f0910b0b05a0240c181200900030041e614101001c200c403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 366747868 1250 366746618 366746657
    0xe120d0c110f03060709030506011a070308130203122101080c011422060e03061005151e13090c0903150e011d24071407120503070e010201150501 64
    0x4070701401000e49113603040c040c101400c00c61052104a80a00500f80001550a20654503020366515a0340082c0303040700740d0f90300329044000182161940b80c003510070000903031000c011001f0a15600c00c0525540d003840c112200c5604181c080c8100540340c108010310058602140c3c0d0300c01c240e001e00305203050908040309a0101d000d42224220060449001d01c00112400e001e0308040f0342083e01c8801140001409160322864119000038111089200400640c01d00000307688950503001400c50809803c1c5104000d04030300b50380c1c2040d00113400304440c806040020500030044c07213002410410320364040d1018101e111140b09c0a000c40c03482d403904a40e00b00e015045403940002010007004881411b9004401e62280e0fa80d170440a40715441003885000d0030030085210002d140e906603402c80d65540803c44840d1000301844829110920180b0002400d58a508450f000ca50315903980740e140890004189800012445046a040c00c3c01000b01ca586500607005a4500386070081d00c4100f02c040e42c0fa0f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 366749118 1250 366747868 366747889
    0x50709090c0c031d090612010603020904050a05120309120a0504170d122705010b10090612021801122301030204110909130606090c0e120d0c11 63
    0x21080c1440c070521040d030390001407200c0041c031035280c61100b0314002c4e5004e440030070415281908040080003050340f51400c00070b00c0702c011074840e0000c42d0054a07980405d43c000000e8174111403941c0404060420400184040d002c1c1070b0350050403500f1440d1180c6015a21003020340d046043c1b2200040202c10b05100c0e5040350050400310000d20700403203162080d00c0c0d840050032aa80d0015110024000034000e190160104814010610590b80e081045040342850380080c4c044510b503589e10954207070f0740c80e04034900310540c406842e0340d03d40b18034184000d000790420f8004900941d1041010170109a8500740c0c41e81002020710b0508014a101241480242140c40f1019913003105c0700380650782e45802d01c4056068030b20039a0b09200901d41c09180c410320740500c489080e8803050000005070040b840f80d05240010b40991000b2460304e03541d420032000c030f48600500c2d00006050552540290038a03010747c00008018038000c00102c200480014103030041003900a1002980601e41c44031780c5d0300d600500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 366750368 1250 366749118 366749129
    0x1306050f0a111608032d0a1103091203030703050c09010f230c03090118080a0f0305070c061d09160e01050714030918010e060906040906050c1b010915050709 69
    0x90783c02d44d413603045050b130380e130805200d4901143d0017042c1d0300140122030401c003000c072000c1c00419040500c0c0e110192030380313003e5141d0095140320501103403100b5500c480400421842c0c40000e560b60381820340004040c0c84000b0f00103034034418108201704641e42e00c101400848181890300042c10700c08000d65800e412105404a80c0c4800040f44d00d90305d500d808002000c1b40350302626626011010443c403420700c0e216910902c0a2600046580d0300441c010051443d8914420714190349400030503907810202007643d41142c0c0000300a21045402041052507450002e6400c581090451404044200c3d40306401680c0100300301002d1600780c5940d02403400e6409455104038117980300640311902c655242c108050340d51003030841d410840c08420448054905072a40e9104060721a960030041c080f07400c0c80500400c0e00582d0707078603070000802c03264440c0d180a4150000031070f54411003110761560b00c03002550a48010f924082848001640e08400d03040030f01d04001d00403407a5070b600c0c0401d54081c0407a40c0071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 366751618 1250 366750368 366750403
    0xc0507051204050109080f03040b0a02070f060e09010509060f040c030b04020313171c0b0112090c050103150f05090c090a12060501091a01120b03010c051306050f0a11 73
    0x900c41c81c035200c0c0c000742080d10001e0365188152a41c42c0041641e03100042d040404582003040107000744030035070340100b944001038011140060f40c2c8801e40003c298069100341c00180320341400050030301c0c00d02c00e058014031080f1540700440c11f040000400028404100c28071440d0b468984400c3e0074001c1c0c2040e644440c00070411512440c1030706600841080415080b41e00302c1080142c039400d102c0d01c2054030f019000700032041a198007415243c41c0205940310a041c1440300d020788050800d0040c4c0070344801c0e03e22941c90000c5c003030300c1d240014064038607142500c4801c000019003413100d045040c0300ca030200c0d0022610002a901c0340035000c03125103e40c1341403039000b101c0d800000ca610600110300ea110644201c0e000c100d40d030b1f0388221500460b22207800040406480400080464bc8120082000341441581c0040e1040d5960002400c596003820294046540445d184003840b000070002c60041c40c941c1130441c50b111031030900825a10903c0607940c284031000c5c00860001c0c00030840d01030605040301a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 366752868 1250 366751618 366751633
    0x5030c012a0818010c0503030a05130b04051e010204060e091302060c150c04030209282f030403020303011815091406010306030201020712080d020a030b090705030f01090c050705 78
    0x104845079a10628003076483c0c03140d0101c4040035520a17450501d5403a0001c0165055456450958000e050054143c0c40f50110461a02000c2100c03040050f005602c01c03002009100074102c411405641d0484841d078036644103000c10001c95801c507000040d400320458080b4800c2d9100110b68902c00c0c103442c00039401c42408030b0300c889800000a0b05450200c08011003164a80c0d40d021074220510071804002e400240d480f0116070014001d806503411041c0c0005605011440b1110490842d108040e100301214540e818004003402010740c00142508540345145c90b620301520301940e82d03c410f2241c101c100e5040f40e2a4203564001d640401920450311900e40c0d42d142d55808200054a1503d003003250309040032003c40d101d50700030320a80088a50680160120501d441c1c444d14041403202c8065070760701d40400404a2280961000700094100741e1000285e24022006010302c4400c0246203009021003002400034402004001c18112040300e80081840c0a410004440030302888034000c1071481010f4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 366754118 1250 366752868 366752873
    0x60a091e0f1a0d020c06270a2907030c0e01080f1518010801091509021302031012140708060906060d060f05040b150f01050d0509150108070603110405030c012a 70
    0x414500a510000c2074244621042403564044107e4441000d05035001c0c08014001400c100a2280070303120b00c0264a03041080307503000c07400c108000c0307942100181d5507000101004d41c010941003c499000e1070465131030710300507103041b096410103414200c10381e0b5620f0040c1c0ea11340c1c40090724801103c480b00141c6113542d4900301d143c041c081c15401152640f82040c884001c3c15102e1040c50355103a002843c400815101d680380400039030006d484030405902d40c0d400851902005501d454050340b040d06013403042201c164015050030895040728510b40c200000344410860001401034100c1c2c0100c440980804103031030064000c0407402e02e50448241040e0800c403d001e0400c3c0d04e1880382c0703101ca2650140c0c00c2030304104000e40022402c15404a641071001402c0300b40c1c0c942c026030344000e41030121600c03e00280c1748001440026808965250f0003104180100355050203110202d017003102826041c0f90600000070307220340341402c079981040a00040d040e100d0303001d42081c80301a014080b83d07074614030490 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 366755368 1250 366754118 366754123
    0x30c0d060203070909180b06010306120c050306090c2101060e27010c02120702030c040908070510050709050d0302010b0618030609150402060705010b060a091e0f1a0d020c 75
    0x11a40f54012a00c981070020b00f819841c0150a100c0100c1c1040001c44013059540c1c0c0a01c40c0c0107000207042541d2108085215244100ca4840c880d0240104000135841d01c01010f160a40c0242210140e40008501001c9620b0700300c505c00c2041c07140d043c0452081e004622180c01070503107a0241c1d4448409100f80a00d400c841118000c0c00401412100c91000310709000d035003603407a0a05140016070140d641e07092100759510151907018401400e03260883c1030b141c0000c0036100400001c1c1c5803508009440c40c10440c082200007800202c00c003050005181240015013684e00c81d10525004103070301c03156401014400e510038800c0800003002e032900e449940e41210911028600d0030b6000c0d00c2030401040c000a00020b0808102c400d5032450240b9645d5642030103a070780c1150384110782c99900c03070f01c0019040c0d5441d000303064002d2a959503120030714540019052000d4014400c491b2802c14004144058454880950191820104541100c2e03054400c00020b40c401d070000c00202c1d500c046820741c00007802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 366756618 1250 366755368 366755371
    0xc030b180c030117120f03190510120f0b070207061706090a090804090207030e09070f0c1b0b0f130b0313110d02120a050f0c06070f02030c0d060203 65
    0x5a60812028929a8500140c804156440d08504600340010084600d10000e88130180c01044243e440000d2a202d503500103400180d00741100000c0882081290007a81c0040308141020341001c1c0301c20f0410004225451a09018408034564403851402c04c2c080e600d451481031603808003404038240b502c214000d4641206001d50b000058114000d030004041e008603c5006800c001c0c2900b5154442c000440300511960f5807c441d201c006000000308141144098031180b030080d01c03800c7c1070015000130400e509100a02030010b111148046c000e03480d0303101d42e5208005501052810440c403000c0c3c0d16103203088050f4800d400d840000180010010501c2010b0300212503080d80403202152a900d1076000da0204861081040b08040b0f034410100d0345d540411000a600640300d101d4001c8075401107175402c613103654100303040d0707101e1030800040042c00c020300781c0030901000c01b130141e444d080000940c05118262010744a5000d00801109541d41840141c04c0000c005144041410440c940078000c0d410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 366757868 1250 366756618 366756641
    0x1b0c02040504061b0801090506030304050f0d2409030e010c030c0f0516030609020301153606081b0f0a0915120f050f070b0418060512010f1112010501140d0c03 70
    0x81c00301027505030900100b0b039400d544009005d00b0141001c18203100c02e801e0f6100080e50000110700b01103103950424070481740321035144071000c01c418803a4200941301d1584246610b041115029400c40400d80c400e10201213164012440c9100d10b00c0c0c1c1c02c0542c0703803601d0360170105000e03082100c00104129a81e402014824800d07002442901d01132003000000031114400c484202041c0c4044d0b600e102610484c00322200c00e040c0d0210500e00d13048120008a90360703030f045203020b5030005007540c8010140d05012200007200315405c0d20340c205100041440c031107051141140c12134540d007000700300d4407034004c00c0f0025181942c104504e140796420280580301c4400c10945042c01680740b00c0d100401c3c0402c444d01079172000c3c21410725151603c0c030f90101000a07a49003906c0c0c95961000400c01d030b614081041b05203580b590001c0b82d10411114824100c0e201602020310a200c100805150120308a080c02c0c111002401d002c3c5042d840754440c406184141e604484109113803290100142c1d42545c002c112102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 366759118 1250 366757868 366757871
    0x203060a0213080c010206161704081b121c090b070314010602030f070305031f06080915060a05011b0b0103080a080601020d171509010b0901031b0c02040504061b080109 74
    0x3903950f03070503e44505482041c01c1c0180c001c080081d00e502c00c07a0898001c0c010041c5444c0e8100101002c0c005a1001c00b62000c032022103002840c01d030024542214039110304d9170800500200c000c0180b00c01070f00c0c40740c0307000f0320a84000402c04c0b42a56002c0e1b0701c002d1803030350000c04024403031424150080007010701e101d03080c1100b40d0b10000440c00a100100b5260703d01d01d085c0c101803801d1402c2e18191115000186100240041d80c00b151309000750b03403890000244100d40b182c00041c107200b00103504040c3c1c0301840a91948da910208025075588088140450741c003030820444141d4005401c001040302c8803009800500780400000c200400780703000300821205559130100c580c4600c001203845034058501038000a036100d082640d0204030385181d6400540c45e46070000500c4801e8007050703403401b00341c3c4801400000031940021388c0d41c15004108038112030031001c00b000303004201c01034a030030f041c40cac00a4006c2e9074690006041201d0390f48410703007402540300300044102c00050002c2c01c00409006050030b45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 366760368 1250 366759118 366759157
    0xe0a0305010f0b1809070e0604020403141e12030c0a09080304170111163c02030d0206040803070809101a0102010b12100b1513030b09030a050301140a030203060a02 72
    0x50010004c00b42c091031009020b0035a01e8600200380d6488000038000031f510941c2004000b0010343c4c03020b40419800041c0004e840740a540703102060f402422010102c000d504012516043c14100d54100c0368840314100d045603c42824240460301195580c001c48014800002c002c914aa0101c002000c811091402848030f1084100003000703074050869400351400b1054520130000f56030b1000583e80149000d0031480d2652001e0309200f05081c0358018180c941c1039009442d043d41410320985000c0c0c006800184114203040e5a110000c2c4002800311003005003000c08540c0e004018000b031400188d03000010f0080c03444001823540d400700324407203050142d841d1000401190030101d0350114000d1040d00075100c0060f206409001078112020026030050710341c98403110302c2541e40050150a6105034041a505d42075140c809100c0c0704c00360546a40f0b9005100e02c030303e1164842d0403241075440f6071a9640c3e19a001e0f0010030b40c0d12144e41c20096050042d00c080288a82c1294064111402d0201410f402e5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 366761618 1250 366760368 366760399
    0x311042d06020c0906040f0b060d0902030c0402280207080a0605011502212104050601030312110702041a150a03061202030a031808011506120510060e0a0305010f0b 72
    0x2218410740502d50018808400a501840c261f80441d00d0f0000010020814101c070f1400125a544003a0014401d665103000316001c2d070404010301c41c22001c0030740d000c610f41001c241c10400311a00b02007804031059024020617103442e10078000b91009103170000032100307040c21602c4d10328094102401842502d4980c0066503610902c00200040d1004149c090201c51016001c060001540194a16600a2004c00d04040c050768448055442240258041c4c000d45d4118580142100710302d4015103501c504001d040084080c4c0481280c00540e41103500184260b60359114204a00001180680c0700160014482107003210b50010030080070599810454a900d0301c0002c2806500024080d4266118a00803000a8000d520100326280140c0000169585e24203959013511030004400d008500c107444108032180d0803104a081001c620030042c442460140c50801b0411401e00c1420304100012200f81050b441d04c00e00f40003e90b0b0820700030300a1044007600320020f44030030b00003240520207865101c401c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 366762868 1250 366761618 366761623
    0x30f04060c03090c06050f04080601080307030e01020706091e05030a0b070219080304080904020403080408070906050103380a060903150516080403140307180b0c0d0311042d0602 78
    0x20f400e60300c80d000c03400c51814031741e0443d5075400c2042c06a5540c0e00030803010481100400c041c0e4003d240342401590f9601403441d00422a006481a0b00d0556019440c180100d541000000090790380d0511580c55614250b04205400346050380590b03054001c03003c2078414010103031041071280040e6000c607480380440b140080481c990840b0058014030b001c0c00498000340140c070081c01c00c82c40c014070241c100750f140d48070500941c1c0294000d00f915404440c081151186900441004100901381001030030119181c00e5402140c00c00c0e0020800d800208000704050045c50742401c1c0b40e009800c00c021319854030030180845000c0d010995800d610300c81a0003401d01940215440381d80751200121402c400c0003030a5070484806030045041c42120b03100070981a408801540c4581c50b1541e9100d40700212410380d40160b40d170760308403545240c0d0400c2842900c1d2000610f40c0c4c0e00600528000405590703190500040c0d0160707410000204459030204c5210305c030b8484804004000507022503030400ea40e0303881a43d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 366764118 1250 366762868 366762881
    0x100602031b07030212060f010608041109040203160f1a03062b05010c0e09153604120f08040512070f05010c02060916030203060a110708030f04060c03 66
    0x503401007010401c0300d010410440c0d118541d0000701d80c1d2443c0ca9034001000c000e43c0100c0e920056109004110301c45c4003001846d030040025040ca000d180c28070781c1b03071102144025041079000304102d2004c1021501c0801492400c410400b51240403d6100d00100c3c01038030041c42020000342c450740c1440a0100f0030011240105401066164291040203502d244844004081502a04680304080210b0000c0c061a03031a03005a80c1d454003a52881ea04100c90760300003500c014208041e5103541c0903280c0307030f1644e282c03800030280381c8040141c8503088040c8000f01c0c0d00c1000c0c40c0440c0d0b03260203000c100003c0d410070742c0c501b4003203442e2441c04408a104c111202072048034098220340c4a0301090b110702080c4e500828100380508410350341d428440d19000c3c2541e50801c1e03040010391029041250380c0c0400d2142080700382c54914510015443e64001079a030700701c050226110203035201c007589090305594044a03403569100041c2a1a4a00042e04040c1404100c40684145043c0614102d41038030074802d06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 366765368 1250 366764118 366764129
    0x9061e051e0601050c01020c010f0522031b020301360f0b1510090e06010f05040b030c0417010915050105180a200306030709020a0f0f03060b0f0702030610 68
    0x340e100075018010014400040c1410f41400001c1020404c411028001041c11080920022892500c44000070048900c004c244508846494504000c0f20782d480318450300030380d05450000c60340d48144000d4820a144180000d61540c0782507200f040f03101c1035046070442d1303880245a2140d216000c401c1c00e820501100700c0189100743c1d00c1c0b1600d00141c1110782068000f100c04d00c590300389114440101c1d85d414100c00107a800f003090000c0820440c1841401664000e8082c40c105015504220003d003090186000e0458440000b01c0020040d08210003918003c041107070000c003901d45a01421402080340701c009903002100c5400c0500013040b503028443c1203d83c05010716410b101000115900c02901805402480352034035400b501a0449400c00d0022511002c140e41d42d03410840c04261a0000c01d80c40303503036030600500c80d40c90666040030807030000640d80e04041c4021000c24408500400060304100c1817680081403035041444c0702000703028020301c02e80849030551036040f200c840304042da1244 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 366766618 1250 366765368 366765391
    0x4060605030705010c0b0406110309010207120e130b0609090c040e16050901030b0d050d0509040b120a0215070c150239040212010e1e060d121209061e05 67
    0x140c5d001900c04403900da4094028080003a20394501c014000f016402a16901440d80d00403507034400b4040224072404207d0040d0811440c11141e0001048028441c0644000c445a0319000320303480341c90b42421501400402004070ba038611b8294088000c94005002d40f08540c0c002c10002694100c02502114103210680c0714182020698001100940140032020b07130007000c2c440c542000030b4001c01240807046e031075894050700d4451140602045540340024288039000c628042524030306c010911040c080d40644004150a0007403a80744090702c60420000c1c403524050800264105e01d0344488111b010841e4260740841581320380c0d540c100a007010011903000405c0343c07019150050000f0344138044601400250500942d8803001d02c440009901045030814036404200484501004007811034900d4201d144103030810102080e2002980c990040503d40203c00c03050009024000008aa0402407424801c05102c3d02e020405802e031498928582d000e401480a00407030310740034840c131a1101000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 366767868 1250 366766618 366766637
    0x1509050d060b040e0a06051909120c03020f0d03050f0a020a09050f0301060807030b1b03070e0d020a0806090d110316020f06130f1401030c0f0807110a03080406060503070501 76
    0x151800107004031102c1c43d9005550380e2200d40f44001c00d00c800d501a5004440001d903610b0803020b10840c4d07034002003002220904e05200600091680100e0104443d6540340140d5071000302d1806900d0080d8028030785403a80314a046004109515030010b62069002c0100365a281e142c47c55a001030340a101c1d0514040340c01070b102400071f820220001c0403200f038020004034405036540f02e802d05112a540040d21090507103c2005403d042e840e00b16802210a070384d8081c6549402c0d500240550000070840f445500814030980c29542c4400000000d8245c0c4000d4600f03604003101c07059903a640403021a0049004580072640042021050302c40404c4c540c000045046465800c11900c4012054400d0303220806102034a01c400c207000340302d0090301c141d12205200d9814000e01e04100540740490a04160500881031100c65214079440d0b110703800c5085c0640c40c0c1c0ca030500c041e03896800880701d801a41c8980c0b9007190515500400060140b030140b00104152074480061540701c8030203002d500c1c0803952041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 366769118 1250 366767868 366767873
    0x80606180102070b0703080114100c0f080405090c0304060c020303011401050d0e0f0a03020c0f0105040302010e0d02031209090a05090604082107050c0607080f0a151206061509050d 79
    0x305903032060051058600850b22440c001d2050f1300050b0040d400140c80c2c070018010003a0507001008041000c80c0c0f40d40e030320750000000a180c82c5409000130260644500c9940400200c0707410384006c2c1c80010482c02c0203140420036807209801c01c68003591080c0c1055042d03c40742d400441260306954901d020349040701c001c2001035400317502454001140030750b2521000401201800034011421400c0050035010240f420003e14183c044a6030900ca030070840005030341d9a8111342160209ca41c2800c0034a0030103844000a160100e00c10340184d094020911070648a44280b0010502c01a040705c1d14a440d4132550444006c4682c2190f03101401d500c803102050118607484041c088104000c4402070f4401600c806c442604c40c0160745510100d5008503000c421a082408680d50160071803030300e05810714008019000540020340200605070b07a80d00c111031001600c080e02c0d0054000d044050b800c0c10380b03e140c002c0041819124950000c040c120390a46101d02c15042c0008a0714020b101c404c4951454 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 366770368 1250 366769118 366769147
    0xf011403060d050c0405040f0b010603020c100507030b03060c03070908190332070c081504150905060c0c1e0a02040b220e010f0216110109030c08070302040606080606 73
    0x581c420f989500c62168030f034009940d5806003074441c500c21b01409440c002c0f5403820503641c10040e0010001c9c180180710150705101c00041003815000740940200b519101d400c4190300030700043e40c1d00b940502071142001800407034180154040c4441d507031091805582d840c0c003503890b00111a65100c0c9084802919404a48141011082c400d26500c40c0e85405104001d140d140b40503004403aa41000045298000d102194100d54001d2658901030101d09401035015031011400800041c621050030720003080110040d8481001590b00c44119401803c11306510710381a00040e007042c0503071003240304c1d5a0000003181528540c1c464103800903d4031104c540d00f00406400c01e07805040e040812800d2100811303400302c40315250605650350005030240d00e80c200e9400e581d40c4400d5a1041c2e8010081d040c0001c6a80c8000a035140c0c10020b100071600c182d43c0101d50b0342115034009098402e00000109129030007050301c1d01100c0c82282c00300501c42e540c01c000e4600c00350480f2034a0b0302c03140500404540900c0c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 366771618 1250 366770368 366770389
    0x613030f021c0308010503061024031b1e0c030206010303120b0d110307090e070b0d0204050d0c08071e0e070c02040c030b010311092206080106060302090f01140306 72
    0xb05040c0200d40303403020b59416440d040e101600016041401045a42001d000c03940d044a440200001d07885d0405c80e81d0941c8003c17246174404110b91050229281c3c5100c0c3c0d010407a034410103692465082e000b40401400010300f110482c040a8044003031449850140d4408400294542c0182900d41e1942c0c906032440e800d043c0004540a0f25540136a5055841e070954072816071041c0c010034103051745102490b18110854102c80500d900e0a01510620540065960201c1d481a0102551140e101c6d10510103800b99511064228524040b01c07001c005016442e02d050300d042204030b03504550f407840741c09880d0426804090388041d0180040c4047c0144403401e5501a1140c2001004d40866a001c10b00311841c134403110300025501c114080d4190390500407038030300c0300ea0b5525290400c0481000202c4181c40344031405020500100d003140d500c801900140010300803080200902d6640d020080c001e5440108028460320406040404960060300c5c0c0152003d005940c860071a0307607000c00d20645481c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 366772868 1250 366771618 366771623
    0x2040f0e070504031e0308280b030f0d08060117010501140904180305180a150e1503070503010e0a05101502030d0f020406080609070c03140c010c0801050f0613030f 72
    0x1800c22001c0081403403507150501116200315105c0c0d01090608004054610281c00d505d200c11844c0400c5800810600f10b0300c83c804203480000405408030b100081c507010007100c1c031203a64040d0201540e543c0b50000070032403081000f80c940d20204645040d414000f003009004190214541b441641d0440c1d1020b0043c1c4540f4170058800a001c2d40040d07100c1d617018070340e140c0850002c0d00005804040c0e082c0c0c0c003114102941c1c10384141140c00e0911201160303050032414000e04006035517030103030b420b555422201c803c11070709400076661380c0c100164010000c3c1d009000e001c07121007040021515410152180301d06c1404108500aa05410400380001c482c1d090515007046110a11041105020a214444c0740540070700c0e005135554640b90b400360000c0c1c0f0051946106840303030317002c00140c541c20204110300741c2d0381450030302080344882d0341a5031240506803400d041986403c1c08014419040700382203050f10012605004080801c20401195200340e010701003540310000c5040000034848440c1c00522403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 366774118 1250 366772868 366772877
    0x7030903111206102105061f050d0302030d0b0906060702011d130204050f090103020d1401020f21010e0c041403070504110d0501060311040b1e0d0b090a02040f0e07 72
    0x201d1010702c49140800c2541c01d4130300c03588041d104201c6902c0d06038502c600215900264905190f058a40c80c3d03c03180020a9113101c01580c0918035109551900650041c06009280350740510070390038001d58039008070100064061808204058a02e420814036201e414004c09840c64203402e5801182c0c4060300c00d04140911614180451030350391003d5400c60980941c0100607240d40c54002040382196404c815a40100918001800540c1302d80c2040110280c00452001d50300c080800701600910503454242c9130a80b001ca0a0b40031480b07007200200f00c0c0d40d895007a070406640c03030b030b03c0941c00400282c40803100103030f041004214048000f88a0a000c44000303080e941070b15a03560205080c2d88007240d518080000005540c691001f080c8246130140c800b500d410005441003014100c042c1c819070281c0d2003001408529010080940c0441f4a025080c100d43c4603243c001c4040118050705039281924480c41304040065001155442550100c801061507038000034502000c60040c000083c000d02c0400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 366775368 1250 366774118 366774139
    0xc020a05041d011b0c170913090210020c09060418050709050121110d080717130603050f060f030703050d05270f22090f02030607050703090311 63
    0x90703841d4030403a02580310301c000c0042200200144582101e107440034120260144051080403540e1296001401035400403915000c0318064031101a1400380014030b40d4080705114208050300303a01d411441542d403098552440000301040260b84900340700c50101d13080000c60000545a141c50340080080c04900c04003c0c10307800a81e104c1c68201442034208116a94590004214248592508404000200e0100d1901e4922666040034504042c20150b208800402c000300038000440100c8100540c41022207070a14900149212240c10910b45200c0c00c03010320f14005091802405010300c80c13000c03003500450340d507200b80801800407580401c0c61b402d845068000b00000c0c0d81040050076220031500c83c03585408846c0c0ca0f80e07680c00c2d00580b510380040401004880d243d00c4004020b88400c50803108089400b090014503101c01288075641d030b5145080c45d0744031081c44280000c8022541c001e42c2500c400b640c1d41302e400e9942e40324106005000400e400420000309052a29002045000408180030f1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 366776618 1250 366775368 366775379
    0x1903020d060807030f0302250905040c081902030c01050f03011806150509040c050c0327100302040815061c050313060f020c0a150309020d050102070807060b03061005010c020a 77
    0x500e1070a40080341c04a000c45d4086007416010400d804c0151013050542c50b0b03200b40004000d0564919203e0507000741d880f0408502003180101c440805802c1d01e104650515403c0c1d013a1a0b8090f0640005a002e40a908028031403548114102c54405001805551550740791046c0f000203040b07000c0591081036641c80700898849140b80070002c410116a03030301a1144250410401103440031250780c814800c0810a0038000c840201c240c0d81e043c0c103160f41c01e03590300c000b09050b1400030094101c0703694030880ca070480701d05850300340c1c0c05030050714010403c854001ca1084000700f8074041c02d030760803648081c0c203420428010340b0070b0103a604010b06c2002a2810140148a00320701682d10b41c21031004101100501100e095041007008003100c0100e42c002d030100d14040c500e1501c0403448848800309a100c1c44804155241d101e9005811139010000f15540c01ea03d0130f10040ba5040340c0c1c1c04075030450609101100c0e524000400c035014a000380c902900151a200040d80c035112822070407a00300d0f50280e0000340c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 366777868 1250 366776618 366776623
    0x807030203090d120b09010b0d0608011e021b031911070317031e010b030106021504030f0e030f0a0506010f0609062a0b0a05071202070c050108101502070303090b1903020d0608 77
    0x741502c0423810740300d09201c1d4001056502070b400c641039aa150203049000034000c51209501d0340381081005030755407030800b107005000201080a00e903500c80040d900c1800300e0603491104113042e075a610f400c81c403080c03100b800781c03211311900c005080800813020307823882d110400b001103170021019020360100f8034030003407600d0168400342d20080c2140320100c0100103050b014040201e803130b170403c011078005241c6a034020385480c411400000801c11013441009040e2410004101000140b108590380c1c04c0f0b040c07411035541c00003405221018041c10320001916409007295506981441d10303005d43e1900d800402c104330059010304144420b141c0c500b02d0002c1044030070380030300030414640702081d0340c0f90142c030203028140702d40a81061184100071500104150619000c2602c10900c0c1a001c25114580350184500c2650060398088910004010f01e1903000204101101e2080d15041c0d1003035580d13820072595004180340c002500701c04402d800c04a610171346c020140641d02c00000502162075048192 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 366779118 1250 366777868 366777871
    0x90c0d0f0603031205041a06030f0109060225051005060a1d040b0c070803010b031b0a020106030b01061106072019020406140d030f0507061b0807030203090d120b09 72
    0x503101a903400090042c0b42e0300ca0500960f503c6610f40c20b2101c3d0900340d4070040e10a005261000722010300d070020540d141d4013880480c4a0517016002413100c46100d0500d40029442812142100c144103617050400010034600302400a8000d0050300f030304a0550141406020300030070b101c1d44480d9503040030881103969145481e100541c20001c1d21a8036080c5000300d030481c40034105540340e42050068000103900e502c00c881c191002601c00e9074503915400d1000c45440c0003881101c0c6912004074200d00700540c154041402c81c0c0c0540204080c0d0b036a00c1c40141c4003101140c0c80b6420a801000006079098001c4a013449070300401c4208400083d00360032501d0a2001202c001c0241404580e2100f080d46030038000e00010300550040185480e00c018002400c0024420000f000d100c0340e020340300b0f1018011030560b1091a0004010300242001d407400d42021844e000780d0b2408500410042041c96210788252441030144900911840e03580041c2621681c140902a45280d9269040754809884480441c1d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 366780368 1250 366779118 366779141
    0x406090809150c0f0712060b0a24030b190b070c0e090f060c0a09030b100305030c0106080c03030a0807140c030301030305030603010507092d090f0b1f080a0902040e1c030608060c09090c0d 82
    0x12b00c0f60b101c0407001400c2e24100003000d03206001c141e4480c5580d05420400202311020402410f940d01d129290203890a040d592200d6217460f0000100803e03c2008511904000c52200907a80c6554810b0040c4020f070060302149030004e10b04d10020310000d40902c2c20160012440f09014600f96920b9840c00d1950744104540060760351608800c00070080c082198081d14142100514180600c05000411801c00203122400300510f9880d441071903040303a001c5030b10020150051705d54940c3c603400e001c0c04950040d910140a503207003800017030703445201e40e4603403080e280888039101c440592403420801418040403550605054424005468401d40c46650340c07107603680d1404202076030360344200044500c0945a42e941701070340c02107910041394040d203982d03031000001400248070056400420028030003152009480c0c441c40444820801041c40c11a440400381e582c2409001d490344001a29030340700707540c481c3c25a2424040c2000c036280980302d41e50b000310504100c50822480c891401c0903201c454014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 366781618 1250 366780368 366780419
    0x21c0209030d02070b0726040b0307080a05100b0322050115060908030a050310090c021b040902010516020d0f0c030b07080f0406090809150c0f0712060b0a 68
    0xc0480314103051003850312442c03081c00500022850b00700040c0d034501c20814018502c0c60401c401c2c00c51110b064100640002c101c103040c0c2d0b1203e8854401e00007079801514a0004200050700003541c241031800780912a010400b411110b152400c40c465896410240220a0040709650404400340742103c0f2958064029000820703000004c007076032081c8404079006942003208420051203003000020881c1c0328044245403080d034035a155100100402e020307403c110611410454005041540012903402080d440390200440035401c50030001121940c100090100300c06001c0c00040070500702c410804580080d05110a00d00540e503001c0103680c80090031a032400d41104140188130f08005034951206c0700e4145000c0a0030004400e04d0110703001440100b000b608d40f10a4002c0012110075a50100d00203001c0350592000d0403c0c0d0072041d0001a402c140510540c00b00b00c02a82c40052020704039404000903803903801e100d454401c0942100c0c4009030300b000c6048400a80d41c2c01254480e201d14500709071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 366782868 1250 366781618 366781627
    0x231b011b06090b010b09091303020c0a06030c03050901150b03060d05070b030f100e0408071a0c0405030c0d0b010314120f030609100602030405060705190c0f09050f04020f0103021c02 80
    0x410b6111018182c102d84030505c018001c01b149034940c0c64100b500180c40d07084a200c0b45a061800b05d02e0034507210700c010f0308400c43c01c0c0000347ea20b030150020200314040352010b1160f40d6411180318200c40080501ca03660880159080110b001c400004581040014104000400d81c07030321010703e05202588404501d00001040100340c91400814581000800355201c00d01032400f529a2024140504064080310700082e01104101080c11071040034a84080d01c0d50361882d000039100741d41c1e0001d214a902034040e55460030040d182c8116860900d5507c075949050720390075031300c035854100c1b4041e11145192084a011107018451003014180c103a2014520f1070380d0780b606506010720848042d110002108040c481800059008030942c2c054402c1070343c00c02d44980e45420a01d01e41906110560800c0070200e0104050002c1c20b8445010744281000009c44c0580d2403a0280c1194021038803250b8403032820021600504c0e00010382e00c080281407401506007900001d0141100748200c044100301540003c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 366784118 1250 366782868 366782873
    0x50c0102042403050606030105040507110a030e0111030c070e0c0408010f0204032102060705030705090d050d1e02030901030c050c0102130801110c0a060c11030301060c231b011b0609 80
    0x180a801840e4181c0340503c02d608105c0e001c2911390006004492140d0344490000350381c60300c00c00521040040501c2141c40a020030b06010300304600d00d00301c90780000c0480082c0d20f8685000422940d03103900060040c0502c503e4504547c4014502600e02c8205100800c0002040074090080d03500156041600595942c5186080b4100d200e2995040c240c050030321400000454000c204180d203c1c11500704150760303644403c0125014030030051203036849450041c4110070300600003410380c0340011130340302d402c4219080d2540901d00381c180090100140c0c0300b0483d16503c0c0d442900f04413211401d07418040d08110540c12401d003a038001e200b40050011124104005002c000d00414000a0b00c8020441c50300300500b0803581ca8003aa208058041510340e080b00012901c0b512a100240c101321043c2c81e201d503150070004014001020050341c0b103180d001e0001c1d030f03071124035040740742c4c0d0009942c01808803924003c400d9100854144102e41401f80d2858040c0030b014032004041c818078811a0001881081403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 366785368 1250 366784118 366784169
    0xa08070b0a0f1a100504080f010b030607021914100f0912090815060a0302090720070509070f0207090c0207180507051b010603150218010c080d0c050c010204 69
    0x261044540b071030800e0124101c45104981203142c0c118162005110310088000c02d4a607449030794049601c82c0300340b0100031300e5894190310500c0c030311404a0558620381c648507400c9030348641c85d0b003110f2682c0c800400104001000e18482902010648042d00d8059416680020860391540c903014407254840c11500308002e40707071810507020801030404030718160074080ca007a9103c098400008007140b0150110703030b42da07444d6400d000c000d50340200605401c0c03800810040903007040b402c0e003500e120012240802c0d0260041140010f40d00d000d8044c0c0719a0740c40d403600701c036182d003404804015402140004500e00e0003502a50a480c03500b40c008100d0301e0301d00078200c0d1010810240b100315051508052120480d84041102caa0748070074810300000e00129000d2900504031913000070300755030035641000780c80580c0d500502821940600350085d03140c4498010742d10103210031002088502c1c02c00c40701405881c0c0798030400c00305210740780103418508005101422617209030043c5c404c0000d050750002410000703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 366786618 1250 366785368 366785381
    0x31c020f0a1211070f05010f020c040203070c210c030503060409051c1202040b030106030b0316030c090b0603040302151317040f0f1202040b0103091b3609050a08070b0a 74
    0x4d00640d0710304030a8201301c2060340107060400080c103200c5241c4601c208111110340f800180708550700d0604042c0a841880700c0c107070403103a10380740c40c100e80c0a40b50401c0d80a2003450072500c900082e01000d07901265203900c0141225481030b0350b0b81030b60010403420040d00054021030603400e01c414016000140c800c0780d00da440418101d0041000f03114004992085d80d0464424ac24003040602d2442d0000e030804089001500c3c2525a441000061040300c8c50124212064040d0070000015024248801440120b82c003a0160380482402c8400e1400010300582c4112001c1003201c200a103659120020402c0040c191220580490b0130700803440d00d44512401449481010b05003107180c00d150032103034126200080e1103a60784800250580c1d020303401c00710320181c2c41060280c070580351040c03980101d0114000c060440d1030110452003c1e4080120305c00e00c0700742c542c6092512603180084000034028500c01220140100309100001a03008405014414450607000f100c5103008622141140d50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 366787868 1250 366786618 366786647
    0x40f050f0d1d0a050f0a0b27151204020a080a050a060501080a0b07030e150403051b0303070903080304020604081608010507171f240815031c020f0a12 66
    0x350303402e800e82d40d60781d928502085074030a44100b4904124000050060202a8020aa074120000329040405004902d8840d07501c0768074030110f58141000c0c1482980000302103d0490a007041000d480d1458202c0200c5a0051004122030119519580c041c0d042001c004021101503010b00c6941c001c010060180f24050003406009010701146500e402400c00f90103440c1000341a62040c0c81c24480b10248408005d5616032030503602c003820306180082c40c65007c46541c0131017403504250f40d00710301c0005c0110790040d1802da0b0360220040c1981c8a01d0b196500250040381e1000040200083e20903003841040014140b03d41c02c142072070714002d060341c2511401460b2a08100c1480d1100f070341141c40030f031156040400f040f60140400702c5a203000c581c0004a8102151103e40c08190350000c40c880a148c4940c1c0c1c0385a550030001d43c0301c0013000c10190000340001a419000820100184041911040480043c40c812a00566062a801400c01013200002d8a01030180314200e1009500442c00002500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 366789118 1250 366787868 366787907
    0x3090c0806040c0312030212151003200a0c020a06050c070f031707021909050a06061d22020c030403060b010c21020a1b05010801050612060405040f050f0d 68
    0x1600340d4034640f001556010081c80c0043e43c854420030705100758141da00244040700080100d060581500c010003117a00da4613446100e14408240082d4424042c0c54a820351103060440c828000c3d206043c2c4a4000d180b0642c00c010102c052500944d4640c40320100404050311215174031050000d219003030036500d0308464140c007080401000085c84c1041c98810101080c0c3e070994a46a940c40003508506c0c010f210b07500120808580454100c9244d0310450043c8046001006419030320f040076030710300c055141c0704804180040c20102040c10140040c90f05e03850280040c03100140b207a014241240c2110402d016140d101003010700401002d84200e040900c801d0078036480070485a6251800207640c0383d210781203043d8650100302e1050080006890203070740040001d4420f0b206441030101d4080c0c42c400c19000411420000440e030030f0290448940c803490003140321490b9507040520003e080d02800031160f0800311034807140811010b00000034007100c1103000e090350b6800508005c06200350303c54502c4050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 366790368 1250 366789118 366789121
    0x106110d09030206090609030f0c040c020721060e070f03150908030613020c0f010e0601120c06030c12330b07020108090a020418030f020109120813080a03090c0806 72
    0x1a00007845500322079045503540d07071300d501c070307802042480c040c42d42d041da01842160404080301802140001c0c0d03400090ba810010100d5105040741e40d82c05600c01c55142e442180404418101c0c2c407003d180e8000c0c06408042941c2540000c013615147e41e0b42d00c00382c2d0380c4829003014000c00034807218140354800814000e000c0c0852680724107180d07110140c8040d1090044c1d020260005ca034540559141800c41d0050700c90880400180c103018080c03091010b07810380a40c400115809000580941c1030316003003080d200c0c0040c140301054004000349444a0240070b0005c910b0582e01d500342c0120f2480518031030b113400b07020710020880f607102c03100b80c003a1202640602d81e0a00080580e01c082e01c0f003103902440c0c01a00c9455004015062000354040030350007c2c10000500b24040c80c10301c041c500c0324420781d00c0024883c40090107e007210b11200008001507404104c1c0c444052103401c40315002301c41240c1c0000170542c19a030b070076174a9100c90718078000b198aa608030300512140416120081c030310200908001e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 366791618 1250 366790368 366790393
    0x60f090605121302030a0602030a021b011a01260a0608010c0e06091e12010915090507120201021f0b0102010608070503071509030506090c150a080402010503180312010611 75
    0x4040080411503d83c1455600708259601009900703075080e00900704644d85d0405403480000303940565822210b416101e508419010014071950207194046403080c08503d070180c0045443c4a907030140c0111030202040ba4510f1107550f000b03181c0c01107040840000702289403052840c251001c6c07041400a000c92030728080910b40303505003155410071f8100c2c1c0300d40144600c1c00c1c600e103080b4030404209801c020401128440c030a0154081d205180c06600b103020072500242040d4150707032030140001d20540005004104014966901541c100d1050040d29811050700500c9141e12070150f0704004020380328042c004440d6028854030016102110140c0112410302c40404c0d80c45030584100040c4001c0e1000f0908500d209503141d40147d9806015620281450301040350750307500c4410250312900c00c062040a4445545046a46441d25500d44103010750b940d0b00151078a80000308a1681030200d11482c2401520500040c000808520560020703541001c80040c000a08180303600c045a0016907039041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 366792868 1250 366791618 366791647
    0xd08060f0f040c030f05010902070308012c070302070f2006040b04030b0604181506090603211103040e0f060409030512040303020d0204090209310e010603020307060f090605 76
    0x1641034064401142c0e40c00e2501c000ca00505d086041c01c4501881c2c0340010654080580080c000b05000f5036074881d442e600d034052101104819002190100880083c0342c074103019247d0309551011903420f0041c200000340d00c3d415448c800d410021a007400030700144801c9d92920b03242540359900d05441103418a420300d00e040c21680320354080900036021407400035100f0b554540208060b24000c040100001c090740c030740b141c02515a621a200d109061620115141390203115103400c481c3c0202c0801c0b100c0700b08105803c0d07010006d0300602d04201000448520108041004100401d142070030316580c1d10b040e1404503a503400191015104a0034461150041395110003940c0e20155640700c10000c50719240350580003403244c022500316041c004100002c852075154050300700c0700400c0d2030760301640205c16840c44011040011004500c0d1a540100440240a0b0b10454010780c2e0000001046516174001a10f49070700c5521400004203442140420075601481c00c0000740a203003441410840c9042c080c24 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 366794118 1250 366792868 366792889
    0x210031b051606090219030b2a091201111801021e0a0209091c030501080118080d0207020406031e022d01110a0605010f2108040e091204080d08060f 65
    0x500f03c43d29100c03810305640c2c4080140148600c0c0d08190600c0c10b5903494014200b000403a158031a20701000500440510306508012000d40c040803a41c5c98003801c84104100001096001c0529660340c4000c13031a4500c110005010100c2035800c00c0c4508400300c8002450138140005581c0148181d15083d205071000151144115604031222107a65940b10840342c81c115100344e0002191140c0a40b140900ea010341c070003411f840010b4000d000a01d035141a8100240f0f600300020101c501c100810300300c0c04529030151404500c01000403c60640e00d444d4481502e9440c40020204921016600d0442c41c14503501e10b01c049141c1d44003240604080f0f000c01000c80320120240c1849080c560803401d4880a00102c2e58035580301c0000c10440d41c480307015040d141894010071190402401400e07421500b90202ca8001da640105000c0c43e0505154803114840c4001c0c2600013248101c0c1c810b00102c12880c8050805050000020890008850790040c03080e42c0190400d8040c40700105200c02c0d83c0c50300120070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 366795368 1250 366794118 366794123
    0x30206030a092a0e01050105092b02190f0e0f0703020d2a090503120306040b01090302030a030c11150a031d0703030203071b050307120f0210031b0516 66
    0x1042c0b003090410150542c107000300030340304116030901490700c014001142c0e41591350f00540c800540c1c0c0c03034400559480c03048902c55503012851048010341c0e1562402100802034061011012481c215400301c3c40d020303a0020044d06945040d6000d01c880700311240f41100400041094100e541440c540000840c2d10145ca18000c06400080f802c2146405411040303642058080000032151340240d2900500c488038004000580c2106001609241c0051501d414a504070a41499a140c2e0010000244102c0003034505200ea480030000140e0342c00d1155510040c002e450741d5031a100146014941a800f003171481d489001214029064140e00e1000d84094041c1400e0001d01e4601ea4415908001c1904400104a1150310800306c20540c0c01300103003140c1449403628034480146501071180d940800d0042d681c040c0c2c01b6420030015454001548035109001d585481480407040e0045004072104419400100e80c9400e15a840703400850722600d0441c540b40f6040d07050a1480f0101440c40743c05e404003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 366796618 1250 366795368 366795371
    0x305250e04020a0b0301080a050708010b0a06110f0604030522030b01030213061e050f090402090c131e050112060f0b090a05040f050907060206010506031612050705040519030206030a 80
    0x6000c644030500c1200213400200e11454681d0f80d01c0014075901c11103082c040380e0320702401d000000d40d00014000d02080c0d401c010b04140b407090400340c04a880786100780700c0c440c140c4180b40902214000501190703000c2c2e80640da813650390b400d903030705020901c50111a0201c4aa583c2035000c0001c01d0400b0000d5041d2a8112180401511441101c401510507078000702d020107120001d0004c1c00c0e1680d41030500b2030741d080d2200c03001102d0035400c02603030f5041240c01a420004805c00102c2c2081e001f0014004005080c104559103525141280c1241807000c0484071040041e203000d0040f583c0011015004800c80e1b1b6040c404141440e1034075a03508910301c58032494100200b5050358a41d1030312140c2019200c0984204042644a080710010341010b5544005031302841d80c001c20440c1c40412024181c40b0080e100c207155403911810301c1540c00420107003604010241d41c100c0b06c0000c250140078058200307560350648403401d00c41008030503580400ea031008440358580820042e01d92100380d036440b0040260 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 366797868 1250 366796618 366796621
    0xe070305090a1202010506130b0f0d02030a0507090501060809010e150a060e0406060e101208031909050609011a210f0709050103050c0105030106170402190e010305250e 74
    0x44a40b0b40000b1880c01046601681462030607140c3c150b000c10300c515011101c080111005030708084c1160201460280c000340000c281c0d12550508110300b0b0302c1148003508813a061400d940b070b480d0800c2c94580290071616295401000312070790010805400011300d0000300000d00c0910084c0c0c1d991607071002021b5030051154001040742c4090791000b401407164907401d24040c50b080ca4940000d01d05801152411480d03040492403181344c0100758800d4171141a441000009242c41e410410b80008001085d6000e800f14070f03010300a1140030ba200b030903200c1d6004050340e051031111b00c0d089d51203410060341d0703442c034154503850750b60345a6014002802039400c03000d50400c007031650f5074100108d40f0403103501403095800000303040d64150f05c220f040700e02400580b44140001070044074203110a01c11500020440500c1c090064005041c0e0380d00f052006000c582d0380d00314450480d0881c0300340ea02811400c0b418074010402c2c001d041c8100340b003034840c0f011465140c558a12001e0b010044500411008010000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 366799118 1250 366797868 366797881
    0x4050910110d020a0504091a09010603091b0312140a0e090405011416120207080403020f1219050c150406140c012a0306051e0102120a0507030f090e070305 68
    0x48a51220502c2c1040d5560202100007910507805881345900722868822884000c0802e103e5844000300c1c02407111100381d00c1c092041780a405960416a4030880c41d8803001340c071240703a900d0080258460110240ca100501c800a0020407910583c0d00700c60300c0801036501d0301d642c0840e81c601e03001011500c108a5484034104903004001400c0507040a03410368040c05204101002d40f010003007420390311035011401c410001410f030b006054004002520500c8148018509551001d10200000d445204071602040c90355260200c0710f00315101d0700505c00303101e03800d1040038001440ca0610036254000d46c6200c51401d0003036031199105250030414890114500c00c0a2881111900342e0348200902483d02c2d8684031104a000c00d00b01c80501041800c009540c060290103400f0488000420340c0300200c56608603000c14448240d209411405454007a60a21442d08050044113805944580d01c4001c145405848100385c8040380050007103040042141c070fa20304100c0da80c0a4050b03d404a62030b161030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 366800368 1250 366799118 366799151
    0x513050903092e030509100c080114041b0e0109080f250317040501080a180314040e0109090b1b18011707030c091401020a14070f0b0703090504050910 66
    0x9140e000e0845444418410f1901d030b1640005018400c0c0f0701c1507482200da48a80141101c0004107480e0120f02c00c04010460b549202d0310040200c20080c3c004619000503040342c0c0f10001104030504045104011000d510f03503448038003a400352020300000e0040c0d031610707006a941e440301d003890180d4900b1642c0e03080c80c40070800c502c084001c42e8091070502004904224040198000d4010030b80060b00318800a0340041e02c9000f104040c0603041d907400c80640003910300700c4d4400c1ba00880c003120480100000150706032820880f0303000304481c2c800010450070a00c0d10014000010702008a0110019948a01c1000780707021149202c44032250b08004160500042c0e800804410020140481c3e01040090300c43d01500000c200755030560300c941c1102e80310840508e0b04e6945402650040c0c0c0900401c3c0e0005c0c2e07035030310b101e489500c03075400301c480a503074411440c2900225a088100340340c00c00308440d000c164108802c10050401100c080c0868a000303280c899031980d05803c60300d050303034989103884c1903180003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 366801618 1250 366800368 366800419
    0x80d0509060f0a0c05030a09030203010b0901060f0e04061701050a0c030e190609020409060504020420090402030c042103031107030815010c02130903080606090109060518100306051305090309 84
    0x5c01500d45407101d001c4003800b0601c0d184404d80c0a5424028800c2d9107107810030805044e80e40e50b0701c81b81710000d500001114003600400c58250426075450703000c07902d0b46511659100c0d2004c00d00002c0303010b1424444850070b031141000e0340810716040039030910078a14041040802c101c9003d14020000d491030070550090000004040d4005103024181c0f4180641030f04000d114a00984050200388c2d094800c00000440700400f03d01144070074041c000c218a459002140c00080003080700307007070075200c2c02103110b1514040004070440388101d10000070507406006e01c00202590070500d0b420aa40340d10080c080300401051900051580c04d5521341e1a030141e00101e40309034000c0e10b5120071f49811030140d0000e041d800d40903004640000001070340351406800b1074052100694036189040d00c2c0c20429949500190308103d002e50304681e0521064a40345024070346124156070100e9150b00e0035090040701c0c10a01d043c00d40e998201310030801507070b10000841c1e0441506403400c1c2c1c0f40d034110341c90781003e0202 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 366802868 1250 366801618 366801623
    0x302010609111206030f07090c11060c0c150f010614070c032003030708120618041a070c0203071a071a010905160906080709050910080d0509060f0a0c 66
    0x82d0450b9524608074801c041c001d04408400100d405440d49010942d81722200e010101c11944070040c2840f0000c00703a0040b0003100814282582420426000e05007403131400c80d40c01110f040c010440d444900020000325100400c40e03640381d0503d00346248000306a28050041d1024400c0040815a00340003a00c11560981d400170500001551680307403220a6140c00c80a44198000503100070215140100455012650000846140c00c8040246400941c3c0040c03006920400f98244101e10203102181d0381c1c49140b1404400820f941401255100940e0141501003040032050010006880001d626002d41ea04c0c03812044114100b203880c151107120f80980202100c0080c010211350b2400c00b85150705865810005010359070b200002c140c046180c42107201c0004046940400840f402200c6654108040d07241050b0f9035500c2c3c0c800b00d021a80251089080445030010802151506001d020349c84030f15813505038071300005079000440600501d0f64001c442c0782e0000d48145024000d14181a810f503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 366804118 1250 366802868 366802871
    0x13020a0c05030c0d410f1303052e0b061c02030601020d0f08060111010605040218120307020a0e060612090604020a05100f0e0301020912030304050105010519060302090d0b09071a070302070605070302010609 90
    0x52680c00c02030010202072008130f6041c4526120911182b01d10032501c03110310204094424402001c50000d00030f40900c4501c0c07034202d0020000045000c018505030407545460b070380301580d281482c0c0300091604408586c20002c1242041c110950f042c6e020340780e40d402020034600468100000701c401401080c2c04d41c005580644006500484048000000380c9850021900c405007400d09040040d180c1c402c0e43d10007948a03065050900824070319004460f0085400b030720303e1341025001c4a0280c0d41c6d040507500341c0e01c20360150b0100700840ca4072000300400392000b5540038402d604002400390000c103040c000e160600c20188080c0c40f07683c8095068518a0a004121001124107459460303100e50003139400740c0e0b265003008000300306400c0c400c181000c0c410340304226040382403502c0003c4000350402d00e03e8640c081501c580a070f0208281d580301d1030148502502901c2c00310310b0628910b00304921404400381282e0705200c000c0c0401d0700850040704441081c00c01d0b540e140d615140882c0145095040303500050b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 366805368 1250 366804118 366804127
    0xa05040c11060c2a030d020301090b09070f0f1227050d02030a090b18041b170411040b01140408070f05030c13020a0c05030c0d410f 58
    0x6a0061801c10041d03400030a8500580b03607010018180e2041c0e40c42c0d8481a0300d90419240e28100001c550905214070b10b0a0b42e050620f1031151805907802a030001145036100c1c201103542d4609042c10a400c94040d0620b8041c1d60b204040140c010521003c4120901c02a00b2500299200740d8003c18001c002180c1ca0250008903582d01a1031144078240903140780c400c800d04c1c01245400007045501c1c03040300c1c1c0c86c0c002106103000001d80c03d59000c20000300c40e4240c03101c0904000c0c0c030f070380c0180c8800b00081e41c04803600c101401c0d0001c02c40100702e43c41d51203900c810001c1c00041440200004280102501d002c20311088890058071400761024201050380d800240c00922540e010030804107407864821000c404a41c1e8000f0555184013502c0c1c20b944c004200303030601d105044540c1c001c0c45042000c0c10951118412074403243e04640102d1307140c0d2400d070030000c04c010f50694819054044955503035000c00389204000600001803200a03c4048864070401d0340c140d0864021058070250b00026014030f555 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 366806618 1250 366805368 366805391
    0x30606061b1222030b040818090a0c080c1201030b0a021b0d030b060901050318010f09030c12110d0804030212040305150f011a070f120206150301091e020a0504 70
    0x10740c41212510203241a503d0104808200502a007040f00c1e00310400140d00d80300c82c1c444190b240d1040105026200c03560405141d5502c0300302d2968400c891880000925a100031000b070020751b00203042402080381084019140101541d100e41901d401a840d46101d6650421500023403041c8a00d03402070600000c034255013400300182c6406e242445507001e022002c0150107200d01ca0003003121907804941c0a10000310710001c464025840c0c14291000440e0a80507407080d0403c0f149180029400540c950b6540400d01504045811200f0030381d151240500b05441240c0340c944812100400c200243e1101040501d4404c10548114000c0d04da00169075035601d1520940e90b0070501d907a01a94101c05000903003081c400c03c0fa00d41200c00c0003140c0d00001503030b036811500d503a000d0581124100f100c00f0807a00421280704c0d1580582c2c0042d0001c1c4401d0070f025502c60000005814440e101e40c0c144101000001c070340b2044c143e002c1d0110003031500710040380c0c13002170030005030b076000b2541280c90604500a07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 366807868 1250 366806618 366806653
    0x12080702062205040207020f060705070315020c0729070309030c1401030b030a08160c0902030103080a08151813140102030105010f031a060a020703140318010509030606061b 76
    0x2c1c4800c0000c00442100c1ea11401e0106a0064120296120002104081450030800d0003003640c140301c1c40541c1c0302103480756984003421503a1005149020350106241c89440b03c00c0000001501920b072141c0841da41030070b1040c1c40f201c41c02c421840020004075000c0201802070054101030344d0301000c001c41042c1ca13034504040c03030f10508407400e0000b41000d49410f4107007008900c9c0d220b0503410044c1a841c1414206800d40712012030041195510620303c070000e9004028805140650710443c11642d6038081900c000f410178001070440c03808103400c1c680800c5030b6030700e80f64640002e455240c81d04034039640d0f415020300009811440030303000016140fa44070410703c0c19030095043e00c6098948450b100c4801d00c00710101c40f0074085440000c84240021034442c03503c0c1c4040c5c2805c40842c412108680d440f81d0760303c040d2070102c44503d03003254801300309442111a6105c103400300000178a4410b041c0108080002d0b07480c040034140c1c074010400000c10281e85210340c078492083c1d8040c64100c03519078041c0c0d41c0d80340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 366809118 1250 366807868 366807907
    0x3040b1c1107061404030e04051e040f050c1906080a0b031903020123130204020c03040f05033315220f0501150e01170c2a071208070206 60
    0xd0b0a203241c511030b003404d60050282c00f4095500340d500c140030082094203000040102a08081c68094824811022460004050381c440c03842250b8900720014076117450742c50941d880c89090700c150700132500c2c0305980c23020b98668411100c8600c0c150006440d0549650000c1039103580e00ca80600620a200a48510307030b84c2000e5030644280d0080042c40c0c00d500074110015401d070400d80d0354001100104541144101d4a0614103000501c010301e400e10000c2c4640c65644260b01c01060fa03018444c08012615040c80962200f0070b0342c44103807c07181c00c01c14040700365200400308480390401d00f0011403685c180700940c801124102901e007180d14280b0f40c00c6004850904450441c495052409a0340c084045000e403c0c1201e40d000c0b48400c28824104090300e9504002d41464100080003106414000482e0400e50044400b032103290394074808030243c214040d16102100050b44558014106406d60018070b040c1100d42ca40f581845140c0540b8040e80144140c0d80003a5012202081da5408001554442c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 366810368 1250 366809118 366809123
    0x13051506070b090d050301050d02090a0f02210a0203040305160f0506011e0b1305062512180503120a050c0102030705030612060108030a0509060d062309040503040b1c1107 75
    0x80f01a4138800c01c040b0b90030300c424040d29420020b115014401030611003c4203420040d180c0c0d0115149006103003480880c4c001034808050040300c010030038085d4008058040d0060b083c02e4040d4550f15058030043c005105803940401140003849004040c410407a03d0b04070b1160b0b0040960ba60b559590b680380c0646025100d000c040e10425a0000594841031000c9505c5031001c400c50103586440c240811440d80c1000200c0030341002000c80c9004c0926850414440c0ca5100f003404c1105100c080c80001c201076052010800f400f070980100f48003990b00000c425000300d007040c0340305039a4901d8040c01c40d29802000500b00d0550b0020061103c884c6d00a0013451190000340c030342400000303180d031640c1e81e50042840383c5040c030b4104120154036544540c000305096000901440d103081e0440e4800002c80e00315902c10b4101813469858040d06d50700c003e81c140c04855040304d5041250905481d072580704e04c00c61041d51040c1000265125054011800010300c4405030102042048a00704041100f50300c40c1004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 366811618 1250 366810368 366810373
    0xc0c250803030103020307090216082b0207020906040b01140403230d05160c03140601050415030215030405160f0602210910020f0a140f01050613051506070b09 70
    0x20030090000010341e0304985d00107000308a80c80ca01035901001303601540142d2950303040b555500c0045503003003008018034414005042c0984402007400041110708106c5a50031a00402140b00940c3d40c00042d04d81207901201c0014a100d4008010782d00c102829280c1fa00915020400100b400f540d10508030041c04a40005c41c01051560180780d00d03451500c0c0c9050120b20309020020400c544509039401d8248074216141c0e400e9281d88580d01d4001c0f10b0503640301c00d030f40518014003d0341424060004142c0e01c4402e0840103600f181c0c0000da003003010b071000161080c00400014103220081241019250b024030840c0c00440c0c03038410032800c0d15098020407015100760950189805071700060140500081c400050420144a0401135a030810617090030071403046104100c60700030180046c4103104e10030000a181514800880c0d070070540c00300d0407940103034541000c2107166200d2510741d510400300c9145c00166a43c0f2010074504d5941080204c90300901c01184000410060060050150201004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 366812868 1250 366811618 366811693
    0x60303300a0c0804120e0405010801050702010c0207060f0e0609042a020313150c1203020d0b09060a06050c12030708040b06040c140a09080d050a1101060f0302090c0c 73
    0x404002d54000c030038142c0c005000c0d02e0008010440301035844a090f07550f0324007100601c01c0c0c6030008040c0caa081e0030103c00c0765074803020300070354a80900c90900c6001c0b46001505074549441d81c040c4c070b155426408002809211400240581d03035540407644d204800410411140c1425844004c2e000fa0611101203048400d44503240d40c540000184c0e000020b10745102c40c0b5080c100350601d0402003134400014140702554008000040a01e004510130b004156401622008814001e0007030350440681030703004030384a20900000d600c070090300308182c0d0400d04201d9522010400f03800d2801118510070203400300e0120030721090945c80b000c054016401207030301c180c1507102c1400b04000c440c0380740e0003240815240615030091401940c06801c000455050030307a0b907103070b44d002c2c0d15081c00a01c9001e03a000440005110060342e8103c00003d943c008524003c0007541d0030204810808030090001078415040d001c00104d01100f202c04481806100b20140c40e4184201500c0060000000d1101c2e00412008603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 366814118 1250 366812868 366812881
    0x9080c060a050606030411060d060306051005060c0303060103050408160b071713031206170604020a0f0602061b04030822050301140c2208030408100501180506030330 73
    0x42c0070b004000040c0418610b0f181c56407040e508003c8182c2c00c0d50440301c14005040103a54501c5454015405000c0102d10b03454004201c0616007015042148901c3d41400040748903030700002602d034046000e08000500b611941440f03845402865010502a040645427008010220f83c1c1d13207000702c404d510f840051000407a0802d2408000b191000071918100202c400840e109424001150400c1c03040010a69100c450841c6903401e21821284180d02500a2000710706114808100901b000003403000740e070382403035002900d5800140c01c01400342c03503140c00c2c00d0041600b10100c4008562014181d0b503500322070129801d00c00030010728040708103159a0001054101130151024291980c05d840800e0f07619031180c031450390440c0c807082c2c1c42441c03d400f07403079400c01410700543c0144c52028000d40e00c5900e0310308204d180417005810040071a0811004100c120308114002c004183e0403500403d107965014046403842c0100c3c1c0ca01200c0310840740040b60a940c403801901d4047c212184584a40d07603801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 366815368 1250 366814118 366814121
    0x30c0507090c120c021911100e1806090106050304060f020a1808071203030509030c070e040c050d08090108041b170c0a030201050403080d060519080c030a03020d03150909080c060a 79
    0x4d03102409030f0440700404c0a020b000503008022944181e08200e6404141000301e404240214250b402294444001000c0d0f0725000210200c00007031115240d005142080c081030781204117108041c184080031006c20b0411507039800400c0c50045407107045444059414005041c80410020410261405580401c8200000c41d80000780e800c06c14108000382e031241c0d02280148402015016980018802d0300c500880c140040b200410380d580c64201e19040500b0014160344081d40b10b94400c28007440c1c90000503072000c082d030b00d41c06402d08049000703550f2030a02885400c94401260348003040c01001099040078600315144d00c0c030095003114080803d140502c41049510b0001902003581403004000155a51380202443d0070380d1136010500c1561100851004260111006c004030300002c810b100080040240415a1074200d00503e9180d50545029440b50540300d0302c0810141c651540689004110340d428005020400c01001800241d0408040541000c0300300c0c640c42c090500856644580f0307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 366816618 1250 366815368 366815381
    0x40c031101020f0d050c0703050a050d110105090d0509030a0204050c0a02010f0623011b0b06090603010b0f041508030c1633091e080105010b13030609030c0507090c12 73
    0xf40003440b05408003001a100c0e500f01c1c00650301c0c40d10903030001100048090001c9030302c1c1441740004000c80d80242c0c030041e10851455207100d071503a00d80310810809040c00580600000c0344c50500d541d07114a40344c003080c186021028040e42041c00c140502138020903200081400d00095030003040b2600d903031040f035402e4030358a01c640d171070010344080f50191401c8011814519160141052200a901ca95144260002640c81502e804400100b08191418030032491030340a94124002c00820100e00c000882c00c2000c11205d50207990b031181140010007650200d0409412400c0440e51a01407070700ac02c945d1880788481c1e01800313410240002a8042d0241d4440307100c45851000b0740915030f43d1015106419216590300010404032180000d401880b941c603481c515070260350f400c19a6800d005e940d82c2994010380c05088801001c2210322249800d000c3c5040659030721440c04a041052414210f4080454641c0541740c0d0051542c000b0300003034030754054400c0f008181c03101055802c0403c48074084403113 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 366817868 1250 366816618 366816643
    0x109030207150201090b07050a1805030a060e12040e0406060e06100807050405060304111206100b0d0912050d0e03130312111b04150308040620010203040c03110102 72
    0x79400a00604540300160200070005100004004025031a88416102c0950314030340455400030326801c03900d0307224510514280825202c44440c514000c0865540d60101e44041c20490342d0702c0550965640c140409a403010b510b0800035202d40d210301503441040700c16601103820a142040c0000e101c11105403036481908010101c843c0382004100a8600381c0004040c00c0422104100105103540c030b0300301542c040c0d40a4415164a407071140d00b80000c104e106030350102c496000e83d040007021407003034001c2c07820740d4200d0048a845003c0000a0405405890030040580d40300d140803404041d80700c0050000c40c2d4205500740216400d210246849103d80c44080401e950701e400d0900c0458403112103403011052a03d0150002c00c450a9940d08100318072503044100514810007081914042c0160350428859900d12102d003131450b81c98008c58403c1f403090800b03010f07640c4951400b805000c000e42d001c40780640000d556a180c00c2c5021581c010075408121070ba040310324050f042d6540700080040c80c801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 366819118 1250 366817868 366817873
    0xa0503030415060503060103210201150b0a0e03030f070b1003020f010c0515011e0b040f38031b031302040b1201060801020c0607020d0903031b0206070308150301090302 74
    0x110395444002041c0c41d100b0300003011684800c00090aa18100940c2d0f001f14001d00c0e1115050f6401ca03904034500b6000c20140d0116030400c92100540688011218125500303050340c0350740e5050700036013560050000320103a50f16000c0407400d000b5100341100209021482407060910903550030141d05880700082c080a50052040c000e610800d5009150754800305001d071080f40c407014251450816100c1c4242c101405402c1e2421190b60700903244000038001d0b040b03112505042a09010950345018414881d120b02886a1600c0201d00181c0d605002c941320b001c00010080c0c550b4090344030301c890344140c4250440500406804900e81c108a007030340c0c090f0245803040d50600510b84c0801000d070455030115035000c01405015000d41109100702802045010005603d800d2040105030810000400f60f009541110700d012900561180d2488141e07940340c104281154810412399042e00000300d0001c1d0414000503110080c5034000890034490700038050094425400c4206160a0306d1030240300a0140c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 366820368 1250 366819118 366819121
    0x81b06030f01050910050409030215060f0d0f03110604052404150c090801020a200a03081801180f2a03110d02091006090e101e050a06090f080a050303 66
    0x130f18000c8a800e8122140c1d03c544190700751190001011038a00780d0086000d80d01c400030b0300907500c91000a990f0b10400440700143c402d44a10046100758130042c0c0000c2c520011080c0309020035000b182c00000c03080e2200c003100c0c00c600c0c0a01c0c02c55541e250798103402c030400001a8451402e00d04595020b8461640480c2e03504200403103000c0c100251036580311f480f091007507100c0b0110303d038882440900305d0480660b0301e40710741c0c0a18648601d840d0300201181344460b00844840c82c08a80c000711100d4011140c3c05001c00f2060307100107040e005050650020a0700284410b85100b4803802607000410301d400380381e03114000b8510a10141050b5200004103c2540300200b0820104281804641d2103901c05030000b5500f100aa0010702800d5003201da007415000108c07400d00c84030358015512009054116425041400c0800a05a5566482c811003044c0c500c5c900e9450f4500e400c900c99400102005003034480e80d1030302c2c0c40002e85040103900032804986c101c2100050010400200400aa5000400f46245 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 366821618 1250 366820368 366820379
    0x2603010b0a122007020906040c020322030b04030504030b06011e0f020c040f0203041509031d010203070c08010e010c030902060f0313241b09140415081b06030f01 71
    0x100c0b40003040e08008103586401c040d04040310200e040c1c5600380882e4025946012902c104014041e02402d03242c0964600104860003076000811510b08424080b24080c03014401513428804584030f40000300050f545105020070540c0020180c004e692048031440401d68944004441d001d09690301c40c081c101d040095105c0c15402030500181001d000e01c15294400502c0f4003040a42e851807548481700703a400420401448040009800e0b204809101171264100c1d80e10014504621450701d21104107000843d000f1580c000c02c111781c001a0b002080011855449454900030100070040d601554202418080c00b544680300e054030403070b0300509150501903605a202c070b4a0b0801441d14804c1e064800a040226607080300800c0000d403500c103034070424105030346100e0a942002a000004080c2c0020480c1001d1f00b208100096503004101c5802c0c440e181000240034101d040c0807500f03d501084004101804041a0740004184603c1c07210400c22010040c03241d9403104507a089906081a40113000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 366822868 1250 366821618 366821627
    0x8070c03030e15040510050c120105040b04060312110d09051509010201020405060409090515090606010804050c0d061a180121020a08030d05010906060f050f0c0a2603010b0a 76
    0x10412510b00842d80c0ca00c04075551284180b01c04e40301a50b56900c503410103289401540a40e035400a0412503a40c2000300b000703a626011034043c0200d0b0311580d110b00c0207680b40d80300d1340d006a005603004001c203116401c103c400a0a0030308050074403000e50040c0880b41c5805401401e00c00d08881010300000103403a11411501c0ca540c2107110250704654007004005919503981c0007501c0640907000000489070304900c2c0c403a1401c02e03800d90424500790018100300b015100030075020392145080c01d01d4202a591464400e0910340701c0c4180984c011034101300c940c18000c0c2a8060b1884a21841604a201103041c04000c10b1405100c8881e50b00001d000040c040b101c2e60340300101e141c01700c0390407501c50300002d940090a111076a070442c0701c06610100d2400c0c5540000c0c02124018864900d08100b414100000148030919818003482400310003d11021103181072000c940394507445000fa2090606036290020b506a40181c0710800d10790a1000307807505041c9001101d0480f0816100e031460f001960200780d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 366824118 1250 366822868 366822881
    0x2107080d140702071503050105010918061e1d0f270a062903030301060f11010e0f1e19061e0b0a061b020402160804080a0303050708070c0303 62
    0x800d4151102850401049403001d0389000d003185801900b4001e041207610900c07503070644072103001c050070800100032991b00414400207441085400c0140c0300c0440215801910701903101002c2c1c54002d01d24540d140811128070000e8a0140740c00c036072480c002c50a5070000c414240c0314500c450300b1320030116000f07084c2e030300808144d00011707a211246c190007540303180c0c1401c00e284401c0e11115160172811070280581c119035000d016070480c1c1ea8000c038041c1c2010960728001405540c061151082084500303501400c81005030780d092000a02c2440980001162104040d051100ca507104444540c00340444801c003a440360b0050000504070340280c0303090030402140b1800d003610f03202d030303100444920103a040c1102014180c0300000401c0527840352040c03007440c21045d07001e4010842003068680700f001410b00004400c540440b000368a62040c4074140300c84000e050001490f9203070003c0c000030500d5010984051090080c2c400300a143e441010940d000c10b021610480060350555246001a000341d01c01c0303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 366825368 1250 366824118 366824137
    0x1504081b07090504080d0b060a0f050903031303150b0a03052d0607020c010e0d030503060f0102160303080109060b0304231e210405030727020703030905210708 70
    0x1501529900c0900000f26101075506a5038640c00164040d15040b81d4000c1c050a450141c50807840d019000b50300401c441031020150701000b41c005100304856404005542000c40510304011000f6038920703200c0f407100e24014440c07111070300306060310099140c143d20400c00c503900040901205120100d004c1c0100300141c00740560300c207151b03950540a0004000c071301d00c42e02240d002803269111403400900200e003800c16251246440562000000b548101aa5000b180c10748520031001031070300c010b0b030600300c0708400e40716541803800c40041815440700d4210b040f81e2505808101c89a00c0f0700e98480b130342c0310032070340540800034020000c64080d001e038000403080103490080e00d004040c1070f4841485a6840ba4200d08994082c4c0d811b440d240000f180150030447c07441001a240c903160102081c0c4810301d81c4207800c002070004141c404a20030030345141641d6a403c800840d43c0700014035014000301406c3c2001e842c14070500007080c10b0f8443c0f0042d4142c2d052180c90286080c00415964105a0b07400080744 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 366826618 1250 366825368 366825373
    0xc080a120309020d1403120603011503030c021206041a011208071b05041a010e09090d141c02180d1112010e071403060f040c0b07061d0705031504081b 66
    0x18071010a1200c03d083e8070720a0050041c1d9552400e00e288a40401f43c0500010b12a0345080002d00340411591008000c60b5414106043c00c20314600008034200b400d10840202c6020b09002c20040201444541801d095500d51441e46640c840320101c994011488000382002c40400a034030204032150211600380720b662403001c6004d510380000c5000d42d180c010002d0700c00e22007003225000540c0c1140c40341c41407a8041d18051058500f203440c8a6840419503084018805003000d040f511000090456241040c00445c0729816404038003a01d0082d44140280f1708800b64143c5002920718054400e03c0d0460380040d03070001e0364841741080100e621f8155921414a40daa01d4504104a01c1070040e84020f042c0e00c03140201200ba81001e040c00d004000b0310a00c2e100f0400010032000035503410900003a540e21421868641d0a07515018004018043c81e1a401700701d0703694280c02c1050005103050030f40300d0690a0321300e00741e034000310130720354550a4400805002c000c0c01540004140c0a07400740070030365843c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 366827868 1250 366826618 366826639
    0x40b040803180708030c07060507020a121b06180602061e1005040603050d1407030507061e140a0f110d090c030804060504031e02090a09060b060d090c080a12030902 72
    0x80035807801c0d000d40c1c40300e20303e50008a01800c6c000014050b140007013403e030404920b04111540041c041910902461003190080d4900c0d03418000e950a80b0303000c600301030503e90b02d00c588554000c1d051901c0b40b4040f80c0c81040311540418068070115505000315030040042c405c500040d07030310b80130a000081111789007520b4070308002429540e038081c00000358001c10180886035000440141030300910315000e195420104100790000b98042d046407185078003c8030004902182c001b01114204a682d0041009410300304802c6c00c20741118032f00c03801100c510380100180c0150000010580d80c1844442165010500641a412100307802024110748a1800800016107030381d034000c4580c00c00d800410018102140c14400c00548081e8040080f0032106c6008159000743e000402d9400004c0101e22001e84600b422010041c0341d40209060030002003601d0b0321061101e49140040002c803a09071000c40c00c0c1c0b10005514040443e205a509410003a0030030308280000742900504603070881240c00001d07441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 366829118 1250 366827868 366827911
    0x4030e0a03110f101706010e0d03020f010c0305010f0b0c030f0a0807020d1d19080f01020a12050105090601081009110c15060625050114011d040b040803 67
    0x500d000185120307091a4909291000501c843c8001e104000741c05000c00c0b960000f91260404020403026010302d608030425a1002e00403500305414064030394101c41c215031003908040c2c0101d0f003031802d81c04d00002000b4aa00803c41103061707078420321819508140300007050181142d01030080c4070f4001c02c0d81c00c4900c0c000c200da448199907407045840000141c3c49906101c58250b0501460316526400d1510941030b0324001450403140c6c4120a0f11440348204a801000c50440d0009030401450510160381d000c294024149020394440d151280000301110410421b1125920910b8140c03100a02013981c42c2d5181c4005452a20303024041c000410b101031800a6180014000c00403502d0130850a19200d007040d600c40c9103800d04500141008059400400100d5142c040c10743d51602e10001c0384150b8001c004110044c0500700c2e0602914030b5080c901c0c10340101007a14100c0c0d049402c0440e40030101403118084940d410000d440007800035104501081c003046100028503003008180e0192894052640c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 366830368 1250 366829118 366829129
    0x1060c1416030506070503010305030d050402040f09060c030b03070f090c0507320c0306040318030b0f01050a05010504180203070e03061032060a0e09010e01050f1c020904030e 77
    0x15031000301540c01040a108000c0301340310303442d0400300c0c5061082c1154110395a50b510fa0040b0070403281c1c46592030f00043c065541e20340054040c0408400100521882e90034444c028140060b40745000c20308048003241d4a0800003043c2e4100d4550281350608a0b0500b9484400b84c440d48089000300b1500348072900100d5a06143c821800e0328503510300702d01090f040350750100c207a04150501d8194120060040383c41e14082035407a849171341450016444e842d0390040c040004281d401c040e1680c5c40c40e404000c06506a2904241601d10403603100c0d0030580e40d103004680c58440c60103000340401b10250000c0c91980d0079006160001070908050f80760300b440318080307850140c04031076826000305607480402801c90080078001e0402e22241c8441c0c41003e00d6034640c2981900d58140074080c220014048641c02c0c46140300b41c42c0610700a007001000e5030342e003503000b451302000c0c06058400d0164217900c80032480d0104080304d50400411082070719900302c0d001c20102040050003038043c0000703803685040d10b40d0384 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 366831618 1250 366830368 366830383
    0xc0910050108042a14030d091d07180602100b030106060207090f0f021204030909150501051b030403050706030f0b01170702070503061303030e0a0c0b0a09030c0e0703051b0301060c14 80
    0x2880817001e11400201480c0030b9032000c248090000d841020704c2010b030b40c1e1000d4020300010800741e20994031807020840e8444669542c800580c40014004a501940800c2842e0201403415090103c0c3d0b2259080600300c403c2449490b0140c1c7c05803104019219a5802940300320102e44000941d41d02c40d083c42d0810790707000e4603104240c8048001080201508034204201600c40300f07004102514091031020f0f003a02c210300809052140200f40030f1045058044981d054402030429a40c0361a500d20345260390720302074083e02e40464106468034840d14818410003621480580d519804034401984610103110701812440440c080d5248c00324280e1400c01080d07001b10b00c480240700c0111598100102200c00903080400613030400d14400300421340500941c82644c03d4122201e50b29000f00300180d03812420b581c00100710360352001000035140004080b25110f070700d20f51020b010643d02c45c17200c400c03061100000385006940600040c40110712030804807840510800325000303100c5240780c0c10707450501c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 366832868 1250 366831618 366831629
    0x20f010504110117040b060409020420040e1b071707020d0804081006230d0f0302060a11071a0613051005030d020a03021902010519020c0910050108042a 67
    0x42c02d81c4a121940d0101c030509122030700d4401612241002eaaa031320f01c0842c0988550701c00e40d1105c0e4044250f40c0c1c2c1e607000f2400c0075584031045154a0780355403407a445401070f10030b40d9001c001440018240301d0202c24110070f8070408105140c40c00c0c0c0326a4941c2200f01000020101c074482c1407160100688688801c165114000c40c1829212894501d000345400769030000780c9020f9040960411a2620b8080780c9150443d842180d071400c201e0040110b203204a207554081d100c2a22040c6d2007003816004520307180195000082449101d1484c4243d2400b81b01d040c000a06c000c0310a124810101224220541c0241e0002d1024282c03000e0400380006540302941c00105032030b610042040949801c00c003548040825001601c91102c01d610007940750410688091100c0e00300d0701c041011603100d82c044420b1140341c00b264400103050103000941e03408110407841e000380b00c0100412400d04080010308121541651b56800d640c5d0b4598078040b510709182c1074240d22074014075204003a011a466a50007814 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 366834118 1250 366832868 366832883
    0xd14060a090606090b0901170c1509040f06031a0c040b0c01060e0105030705090103060509010b09070807080f27191a060901150f17130b161e020f010504 67
    0x70014140402100d031607904c0030030490720b494aa114103071030b00c000c02030444840c11080c000d05103140c0c1c00350f8103001c1344080326944191401110304000003820080c1004800c142c0d010051780c22030715503140032508280401b0700210b52020b03c01002482d0080c45680c4104560399850500e641c450b030010300e94100d00441d1149944481050200340074214241d8010304044005020300d92030040443c01095040c000980460780750710000d5001c000c05d4100494142011340410307014606a000205030110a036444d9001500c55000f08508200d004403250091090b11182c2b14044442311040b0100c0701c1d8028507010354060030b110a950300715191140030304903025140c2c00c0c0b100c03100c10500c1d071081c150080c50140314011110042c41109510b00d8002c41e036510702e081004031030035851302c15102c0f0301144400b1401070b1444010071150521080e40b20012910486104120f5120485450342c4c074409031a01100240e6400020324145460744064510381030b00f80107a07480a00401180ca0030344408407001d03640c00707 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 366835368 1250 366834118 366834131
    0x2011205010602100f021306050a11070e0915090c0d0f02030f010516080702030f0d02090918012909250f081501121d101a030304030c03020d14060a 65
    0x3078041c5c01210a0002410801c5103000301c031880c80184a500c5000300c904010b004135031040c40c1c501901c8002c23104134071402107074241655010710340700402d800c487c20102130088828241103020000c900320300501428010f4080c03c11401d050164102e44c420080e214040d0144110000da282480a802e0036861207001003543d14003401e82c03200c10704c01f181d618000c02c1810300c104100543e02105544407041402e08981d52500c41d000c1880c0603004000920781e00080300802c0c0a10030340090a413401c0e24903c40006d206001c1d4903080340000340651310501102d205075141c0d4a0031442d089440b0303507025003100c5080d03a07070a8105902d07100c034586507a40c00b00440c400215680609030480d40007644422500c0712014002c3d515000200f020b02c1803000014403e48485e00164029464100d078070020280d54101c42d242d0321042111000b41c030948501e0185042d013004040070900b0b000c011501a2600150009000b900d96403d001607c080c41d10150b845003070444080e502100c0a00c41d00d030050245600c0800c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 366836618 1250 366835368 366835393
    0x7090f0207031707021207080c030d0c020f0106120602070303110d090201081312110319080105040b0436060204030506090c0307060e120a0f080a0905040504150902011205010602 78
    0x2d01401402c40100080c1c0e0340411604e180c1c0000e441001c00700700180c5c2c03070700c0300c01300d141c1126140115094108680404182d007610002d55511002802c00154215596100704d00041c42c00c80302139002c0d1600c250305119604001c90840d80040007520302c01e103400280714204aa00d844240c02501c0d0040d0301c180c40341c104000b5503030701c6415a5004425040e6901604401d642c40d039031410414101041405541440200b01c5501032040d103000078034280750095000c101440092404e442409424802d603d8186240b8035420700e44030346900340c0e107500c2d4103103980040c0311814201403d0202030240310012030440c4400240381400036100452282d00240001d0030504a414100402404568025800f1410400032160f1009031b00190390000c1e101151080701c00260541001d241c44009800003080288440070090b6182c002c1c048038207683d4491b000551101c003080261071042e02c010706507102d4100c240025590319840049020b2050510040300c1030030065540c15a602680880050380203000020030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 366837868 1250 366836618 366836627
    0x14010e15161412071b030c0b040306060905090703020d060908120f06090f06040b0d0602070515010b0c03030103080a0e100305011701050915060a0801020d050117010e15060307090f020703 82
    0x31002c84100070307210040f01d9078030b01c034494020b106000d04220458419102034011203030710381c80655042201401c2c015121343ca01000796005100c210ba41c0703843d20700006542c2c0039a208071070003880759030040d0282d0740c959020007405825000d000e0780c865540340b980308009058a001061401249240c04c8060b14250205400d041001009180940c1080c81040711003514615400ea00c138008030380001c0c0c5a0070a03008580440130003100100f045100103411818003100003044001c40400701007000190381c0741c1a520f5064021049100100e41c0140014400900d07400e02404200d45a490a8811040b05100113100100ca601208000c06d55907001480344100f10b00b403900f0b2051104000780b00714186040c5480c0e440382e1010411581901e4507010039090382e982021100100107080003592035960750313907469006203000e1040015200035400302c140001418050066428010b0f0702900840005030b1603542180b0005002c036078540154800031683d5505845007030051144520010384544003880c0142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 366839118 1250 366837868 366837893
    0xc06161707080f0a020f0f12130309030320010906050a0507090b04050d1a041406131a07180e1b0304080a1b23100614010e1516 56
    0x184052869080040341d50b0000030711508403404000785601955060303440380c000d010b900b070070b0b9820050004241000a1060020f002039044100084285403101108100058030320040140859160328080010030b000d082c4201c400d5014000545918450ec45501d0844031318003c2110f041e0ba4810612039000f082c3d10038282d01c192541080b403038250408241d4a03040c0114071a07035100700300c4404428100a000300c18443e0f080800c041814036030629103468a140000f11100e12468482c0600003408034001940d001d1865801180480f504021003041d0404110010f02d80024080b05141028500c58607002010040003c1c003812056401c140072102140039200d01542e00018042c000c0c440031850003022038890350068100781041c06400044d000a01c009104040d00c85001100c4074102c00078081c0c842c0364901c0c100d0701943d0403086400d00325800c551303c600403030450f601c40098600c1d036075004000304540a003000b4441e0186038079040d464101944002d00c61001402c0803180103040040b200303c400c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 366840368 1250 366839118 366839147
    0x303030203044805040207050607020d050307090302240a050d15060503060613051305060306100303021207140d030902030d0e030d050f0d09030203130f08030403020111030c0616 78
    0x1e00c0e40503500c10721840e0f403088116049800960001920400042e11180e0f000701000340c410741d120901820042c2c2c0320700c0c0403038003a400340c0526203a6141092041003120311071103c0e61183d4a0f464119020300102107074004424012492481114888030f02101c00380c541c02c4100e9032219030341c103114600d880071789540c1c07841c410820442c214284103032a08002a030368070100075078000c0c3e110141c110001494081e01c1e070156420000c1c040c1d150381d80ca0050b4101511400003a011511151990401d680030306034180300c0500181c20071016160503003403c00041000ca800369a141413040e50b91581141018001104200405d5072101890704504081c00900811140e9051103040d01ca00b540100c0d40724440303110041c0c02c2020001e2101c0da4802468240c4224400f10f120070012000b4510300230f907807036114181012840c3c212400006070881d042c0400b00a480500c8055400d1a265500542d04150070b9054001c9500040c0a0055500f50811080d445101050100381884401e1107001c3c05888452008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 366841618 1250 366840368 366840413
    0x7050306060603160504210b060f100f03090c1706060118211b03061a030307060e0102070b04030909230411011107121e03080f04030201090b01030303020304 69
    0x41100342d80d180c5040d03991040c1d151a80d4241840c050301d04440301e1003036800100c0e001c041c031b071070030442c10308402480001144035002d0540c40742c540d4000c000c0394841004072070751701ca2012604200810f100d20301d600d140200ca801e0200c0d1111269485403004007107900001074100e4011048988640104507054001c0030a00b00100341c85d0707041d41d9611003004140145890140a40c83e10440304075103908000b80141c200715411520300ea0706414088080440c441911a0713400d00c076004c1c50740740740c520b000e01c0d1071072004000714a4880c00d82d035400041c003aa1806210255406c2c0550b0001c154511241c0d8400d5119a446c08812400c0c118035004840200e6048020b10302642c2540c1501000640302c6030300940c01c4400e0703110740d00741000122482421203a00f60198041c2540c00901d07603490b070b03c6c030888162051f41e4034420441c1c0c45c00340e445026480381d4090001341990012405501101c400b803078006001e0300c00440c0b8040319860f2021403040c283d00880000f070b800820070051045210200c3c20302a0b90210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 366842868 1250 366841618 366841621
    0x60509011a0303031b040b0c030306030d0e0612060f0904030203120c070215030a060906060203250b04020618150702090f0105092d01060504230a090c05070f0c0807050306 75
    0xc83d50ba808014100410040800110302500c078610040c1d40091500743d20300c0e0b135541e42d0001ea141d26078009030b03880c80c0030b84035000794200050b0150162075404000649881d040908404180500a0303000c0c01164200c11032104000c6a61102d4042c00d210714026001140d40311000c03544d8003280080200b004140d40c400f4488803005075034245150050001d40e000450701ca44494a40000504660b400f80700b042c4e24085c8001540b540100180c080040d00c2090002c1000b145400003540d58841c2e00d00801410081c00080c0051034020302421704075514642d004c1022005002084081c00040381241012401080c00401c5140408030154010300d44144103030654940380c00b15014000c00f40007040446440103000304000d011090403101100e5131900c9215030f59407450045c1040d0b00c2400782b042c03c0c582c200d00001e070383d0b16200548810031001922400116103084c1100005113056031100c010008200110340c0410460000110031500600003540032502d8480110301d40034480d40000c1c0130fa0060700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 366844118 1250 366842868 366842921
    0x1506030d03110f0901110a0c140108010815071b03081012050c090c160f0314030115050711060a030b0913051c20010608060f040f0314040f0306050901 66
    0x242a507900f08007070499030ba2110004401a196200310b42807101d50b0303200301d803001001d020034a003100d01100c400e041d000c60413000e050300455540009000c0e40f42d0640c4440c16054054458444065001c0d4032032500c540000300390341c2c00f4080b00e000c0c640b007500002d80e16002c0c4003181001000c0603000300420b00e000450085156262a21007000d1421140b19021040c0050201c1c15482d00300c508401403154181c1c145525441e2000910001e20740550010f60310303070406110180440100c0f41692a29542c1e04800c2d030700584100e48130b500101040f07070391070380303038a60442c00741c4a40000d00070a0402d43c501080c000640c0c010b0041c111002802880460f45807502d60b0301140d0041844000500914242c200c800c400003425a800329240c40800242c4102002000645030306621107800d58809030160388080e100d081c40d501d40b1074800d560203000041004a4800000d00941041c10001c0c01c43c02d01e541040e1703075451400c10f4134050b540b069a0f42501c0d4020001c6807030b428424000780907200d03440440c0303d07910384 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 366845368 1250 366844118 366844151
    0xa051e01120b0a061d0d170a05070c081e06061e0406050306070f0828150806100306150b16030c0210050c1b01052a1506030d03 56
    0x448105040c4030020803524840d14468001d24400c0c40040e08025845a650320010600046822802c0010400600e11401032929054118802e034011810045100304107004103030702d5214007091014480304214440c00034003030181d202c0042c1070007005004c002c901c080c2004030305281c0b400170440300d4101c0d004014442d43d40c040a150001c2e0964941310406500c0800701c0d004044503000903605100320b01c2000620380e4020703400044464240d450b0111625401084031200e031503010240c02040c54403490701e8140c80d0302d42c002403480d0084900340042c20b41d515031260030300e04260b0f00280e52840d01602442404240d010b602c460050109403060564a030081803646070148800280821003d00042014144240d80a182c40d5400a00ea0078060740d2042d0058416440108108402e016911450f02d46442068040c1c04032007040e160145400c4064139054602c60203440c3d9030382c1c40b064200390075a0740d01c41003041c80385d00640504040541d0130801c0402d864a00c0742d204010425007072070903000815030354 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 366846618 1250 366845368 366845419
    0x307022d10021b0604050a0902131406070204180f0507082406010531090b01050c0a0221030d0c2a03050304061107150e161a040b0c010204050a05 64
    0x1810440ca003d140346100144080c821680f020354403e00443c00441c180000754018005800c007002c0307014196594211440050240c00c441c01d03402402401004094100b5810101c000100b000d4000786001c8a42c0e40c040185a481c402030341d480d17000030020b01c82501c04100c2c0c1d0030030100b0700c5403030540c19420041007400b4040080c80c550400001040002c10520111080b000000f02c6801c0740e903003a045541201203140c0140308036004982000d1f40d1103102c3d4007071000c0701c140800d22000750413455216000d1000201b41c0f03a200104100000340d030500d0186c0180007810740584141c0e00030602c6124840000c150422030400d410410301c0758100c081c440d00c05180031241c8542d05040640e12070b0f03a1030514000a0040c10b10340602c4080c0080c0c040c04008021449a0795040c058008101e07418805000319514a1940e00c0b02a50300d070304410030f20661701419440000100302e03007905450107407a0707076400c103158100203ca410940c4d0049401c1c0110b15040e001c09000e030001380d92040c00040c4007112004407400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 366847868 1250 366846618 366846643
    0xf03141305070b0c061006110c01140c010f05090601080d0c0611090a0b0a0201050c090f041d0109030908010501080606060d0f15120302100513020603090307022d1002 73
    0x540c00800c0800505108007801000c07288805038072158004c20703840e02c8036411112290000c4a030440440c85034000e400d130302c05002854000f040c104100000641d0b958941502c0a40c0c1a0410304c03016101c02c0c003d01a100300d49080f03000215032030900e040786520300b80042c1c001095a4018090142e0300a912038200c0c82890f400c00808584c4c481c14840f0105c5600c200c10f04940c104034645004114044840024490314005074020400b5640f031580c25100b500401d200b6907440740252018400d10700c1d00350031004051009c140c0440842c2060300d0304600312010694102c020601485007006010800e12403103005120320030103020603141c0400021303c1441061401018603603104641c88100010380e1090611103d0b44521152013512140d40b285030403000b041c1180144541e200c0780c0107001c032500400f4081c03505040b80d1000e42ea103c0c2e00f00700c030ba900018030010403448140b00c1d550151303642d111542c40003903482e51051202040703103451103144501141c98501030841c0c0c45808044680c0054041c0080c0d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 366849118 1250 366847868 366847891
    0x3060904030519091d15060a0314100e07051207030c020109020a0305011a0a080709020702030a060f020703030b180a1a0d0b01090606090e070c082203030f0314 70
    0x160340d0318069075580940c441c4240305800ba448070b07203840d41c2c1001a1000b6a640f103890301d00c0c5040040c00c841a9000100c07081481100c0c10050401c20b400c2c05000303040072040909001c038000400c440c0008a012080b0b075010b2001e0540314082083d4160250f003160454078920b8011301d031606500e656000c0b002c0103450036081654810305041b4141c801c1d440110020350080c2900c5035640c0e60f00b0003e000c1d11004801660308008840e41b0500d600e030103c100300c12280742502a0818614011404c070080d000030344140d03058000c0c0b00101c0c000801d13511407481005526480180c903030b14a030330b0003011240c0c5415068041da0000103c00d140d07000d41c18200c4c2e4403411082020481c078804200c21510b541810002c641c000704403811103410864814080b5040e680e52a0042202542e41e090480d40c140081c0b242403450780051021070764003842010028549802403401c41c0ca400300158224075000c1c0014a0800c1e142e0100750240101544006400558142446e0a1115418000601d03a46050240c000022170 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 366850368 1250 366849118 366849121
    0x9040b0105070804051c0b1329060904060605060403060f06060504120210140a0309023607021207080309060604060803040513090203010e0616170601050a0306180c23030609 76
    0xd00100c111700040c6548051404014204461454224000200112000b4a007050f80000c40c00b4008401049c1107071074488108540c60b00d6090084010010b03000340c170340c640c0342c1002068544a010081005610800b400124074581c000e251045541c990008400c2003000c020800800021409410565804031051030420b0400b0900b6203084c031b9403000f1950421030201c2c6869442d90180e00c15241140240c0f10720100c8001c1030060081e90400d1000100003000b2811119411000ca1006640c403002600450301028a0395101c901c007030704050f07021916041d0010400081007000d104040c1c00803c00d460921150b4200100a0340300e0050b4010a809041522042c184045480d04840042038014008000d40c808007554241c8800c0126a10101c0040e201000000c2610521a1290b102ca000b40d203485075031248401191a07500c040c03071507801c042d1140e0b000304001c144990340404511107088000f0307460090160103010345d080c1e8613103124074804030a540c0d42c032000a041180d502800484940026 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 366851618 1250 366850368 366850399
    0x402040b0a0807120b0105240a020c0a0e1806070e01121103100e0c0903030412020612070807110f061b0d020c0109060b030a021809100e0309040b010507080405 70
    0x58600c60b034002e102c240f18280d40007800500003411000d040b4020800c14455a0f241c10501c04035286501041c0e101103220616030744196100005892224040d106075100c41007107500241d8900440d0300408070001c1c98109000021075440300c012103e908860103400707145403010300540410103c07041141408200a600c1138560095848015090740040380c0135140d0518040300002d81c02d580c002d14132030003c0c04011a2106025400383c0340d40040040095140504200131140190103a03a801c030f80203181840840007880600c1c0e81103216007540d039200f40e1140341841c4005c2092410640b9a2910307048003501040f000740c0482e00a5200f41482031070908a064003480c1c584030322520500300e0f1882d20105104e00f0001c030641004a0890207602c041c080401c000d010036071903c0326040d0007540040d030001074800c5560400c12080e48000c0780c00603100603107221b9103e5000c0d2400600303024030317035007000070408446d00e02071180403801c580c00c0c606103003010300b41c0d42c131002284158080d4900c1512441c004515 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 366852868 1250 366851618 366851629
    0x2010605130b010806031218011110150b12010911040302031c17150d02012c0a06030e03030109091b1503050a0b0307050d020d021002061602150402040b 67
    0x24000544201510303040c41c03a000004141081885002400c0140410704514000031603400a031005203005141003902000310080014070301441c1d050088080400c3d013403002c103204072031140ea04260041034000709020329003060121030700302c081140340a02445515040ca8606181035a441ca000040c9616541054002c64083d44c0d0000394107100d5035406a06c0c1540d003a01800480c8003e85498101903400201100030a4040740c0008107035900600c04200b52501c442480121801810500d80043e080401048416060302500200da0426081451141050035001c0028816407400b04480080108581d0300c134441032051107200c64849414405100000701030801da4030041d84042c48003540c900c925032864504c00c2203140401d00d443c0c000b442074151402030115141c00200908541e42c00c0004000112444400503600039038051034040041e00c544240545404242e00241140e141494089420004040840d001c641021445030a005c1c601c00100d0b800c141e04503030111744100301201150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 366854118 1250 366852868 366852881
    0x1203040b0a1b1407030302060615121504060b0423010804020d08090604151101150510090b0a02031c0b01081306020d1e1410141302030f100e06030a02010f0201 70
    0x5111003100b1082c9a14644005007134821a4030980944016540b42c60802004a082e4114241030040400800d01030b10f0081c09015840a1003a000c6044800f010001c5001c484458100b07030b141040005050110384000025001035030010442c0004410240740002c162010180000f4000e00d085400e00040040910030b86080c0440034080e5502c4079a1713a84948100144414000046100c40303035246c003000c506009903200190417000c07500629183c1010b05ca0403c55410256041080c1c0c1d031400303c3d042416000a0011004030b41c01103450344446900c011142c0c01d8400309440c90703494107200040d030741d0300040c1c15a444614500c92a44484c6207040000107442031810f1042c001d07281900c1c24890540b52a840388140403004002c00c2112303850001458402d5056032083e1540c01c6112041004841f180b90145030742002401d00070070384821818090981c0c00c295664181203130004100000406000f07180d40003012000c0d0000428100200441c4d110925400064100f14424101c1c0060764001d401072b4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 366855368 1250 366854118 366854123
    0x110307020d1b18060e13052a04020706020702040501060819020a1b0c03140f0303130c0b04151b1a0603030c0a05100c0206071209031b0b061203040b0a1b 67
    0x21030a0f0043e02810100400150103148406074040c000301d0101900400f1041030254000d0050028541e000c44e140503452018100c0e6144080400344900107480d14000f4000300307031040e480540c4800715441000305030751058000c48100701508040051172074440c945580c42405203040140e46181800702154482c2003045088180005030a900c01040102004501100d015070001c043d6410481c01054484040f09002035142c2d0003400824006110000002c070018420041c0e10060791381c44085a03240d400c03c1e407294249040c0302c7e07450700d642508403003484440d8402c4076005806840c156a82c00360a02840b03078041e03a400a17a0002039030f9071800c00c2114180d0480c80708507105c012840c03411950b02d14000e030b10866041d092a0611403114000141c0d41e0085030030f92507990351050a480920001c004001003902007040001ca105408444141e942c407105004940814241c50007400380a4000989501c1d40348992081004101c1c883e151800e076100503820346040c000e503060800c2036958810805002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 366856618 1250 366855368 366855389
    0x20a0c0f0c0e190c0513030209270d0f140f0304020112020d06030515090d0c05100c0e01030c231602040f020a1b030c170c10020a110307020d1b 63
    0x81c080400c0884003541c0c1030f200c903280c080c040192180c03412107a50084407542e82021080c1d00003480117180c00480c0b65405200b101e0f030a001009580020403205d6040c4001101d150450400c5103540e59024107008403a60650404410391000c44204c01518403d03c40784c1901400003002090031a80700704081201c203051280c05545920701c1142002c002c04907444119103c1c03003864603c0d103180817440d03401407298074660050072603682d42d44020f6580300c2c51f014045903075000d1621003c0d0304280c544912000c8414560340c04201c0e5507508005030484185444480601032402d921f0317207883c0c01e00b00c5c0900c110039903034210035221441c00034a0500c2002034240294445d0900010308004007960340a4240031103169103030b024402c000b41048080e1400e4100180000d400c0381030600c0420380784001e54043e0500c05102c68900794801040604280040803a2403a29400241c0076140503070144a804810b45010099441e1084583c001142c0285060004010b015400d044040d120141c801c400c001f0614500c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 366857868 1250 366856618 366856621
    0xb150a0902030a1a06090d050f03070f0b01170705041d070b03040b0f0403020d03090f0f1a16091814010609030c120f030e04110703030e060a020a0c0f0c0e 68
    0xa90403c85040d10310358584a010840c40f940515003c1001d1005041d161603c146c58003485510312492505560301c0c42241c2c025060f01100b040101102c50040c0c1d21200050031a2900f04880001a40000303200b005180c101c1c82008400b1a0140131202c00300ca0000302070310f400c0082003000c61200900c01042c0540360000400300d100200070340c4030b00d201350801841e03551040e9140000c58829174015005030312004c4503105042c0298044100240200069000300459580305c40840120240c11a6282103606030f25030401d0307013020002d82180003100322108000b00c0000007800c3d9000d034803454030100044120b0300c0500c003c40c4e10049440e185c0724490402903841d504007070241c000742d01c0125101d4140210020f56280d4404c01011481d5120f00007201141103a1011284026140300066101e540c038506100c0710601c001c01040300612a480104001c818803e007141005002403c285441340100405500b031b6a00004420b00383e03902a000554085603803d1440c40c06038207821109040a0440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 366859118 1250 366857868 366857879
    0xc012007081605040c1e030b060c0a03021002030915040213180c050102070608010e0a060e090a02090114010e0d05010b0402030a0b031903090b0c10090c0f0605030402010c0b150a 78
    0x400050b00905020705010583e0303540700344000ca031011109080000e003165030061400c0c038407010031420116680303008100001d43d50b00068603a44403c9070049150b1001106800b0541c06220b2401e0039110385008508510700780c6181501c0c0c050144480756101700103000601190b4034003042c0c100c2031080380740c01c00c05516102d4220040c401071781c1d000e55501c015110001034941c800940007064034034a541d65050743c0d1038035080e803042c0310001d000000125200c2c070340801c464801407480c40c8038820701002801c4031403d1f80140042c5c5501a040309000001c40e040600c520703600204240349209056072855850540b5040050041510b01182c0d0b900c24000400d002c0c001115030894513182d03000701c0945803164075030140c200440680080042c04511041e504004840c007440240403540d0b1542c0603500e00f514000003c00403103441c0340f001c0700d00707899009040c0301d220300f02c44159014000d45d040061a508198001808629403880020101000400010f40b20340d024801d00c511801c000d06115201c68548 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 366860368 1250 366859118 366859123
    0x40e070f03020a0e0c0a05070f0b040309050423070c020307081504020103140f1b0708070803010f0f06210605091320010c08030606040e090303010e0105040b030c01200708 75
    0x5120a900c20040c01c440407440c1c88131050518018a0042200d9241048400307040e503060f00003020540740e900030f06100d45c0c0030907482e1018900c20392183d40d40f0311042d41801c04120481d2040e01c21040604903c01c00405400c20012a951700f046c0a410003480540441c030009180c00c2c195013006002c0d004032400b228070070014201c040e020b07038800d13201840901e40300c9006070300303201e0102c1e406a81410002e000c520f19020b500f000040710048800c1a52030074110342c0750325a295018100441f5058070010041243c1106400003002610b03500051103a018981b24005051000d0b08590400150500090201814403540284000d043c09410b4810502d1b08070724010780100701c1041582c806154900c2030032108400d051042003020140c50791203501c03c5640300d1000740c0c1c000611050300208201300c0854440c0040c12081e00c60301c40800117513076a6042407006143d80328184d210302e019906201a402095030042855108800d00f80b8104551441c040c0d0b02a012141d101e0340d03070046029034040418203140c003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 366861618 1250 366860368 366860399
    0x415050a030305030a3209030c0d08090c03010618320601021509030f131a0c0c0a0b07060b0a150c02010e0a05010203040e0a090c090c260a0902040e07 66
    0x3c10108020501181202080c040414807041098890b000007104030082040c2c07801e038001c0200408c590800c84011799461070925124405004103029008001020b40104420381c140c0760103800a000c11440c1ca518020f88000302c0c00e021060075121001c9983c951b461074a501142d80d0000407405046210f104080c18178803060307600b1030050192904c0041908002000c890041c00840c0080d481e01e0007a1800c0e000b20303040414240c1c0b03590340141c40040d48000d181c0c00a1201002c0050199a405491140901d0715009005150144010441c00c00c009522241910405038101c103010071005118800102035240680244461703091703d0818010160740545c403404024404e8880d00c001c403491000300007003e043c9100d0280103900800003805000c84603d00349401c54841032020030030400c40e40d919000c3e40010303040552416561291140000c1d4001141100c012548400410082d0301d03550b40d1030341007001031086c444251984110780454803503500204149400605440342d0607240c0e00303814100c240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 366862868 1250 366861618 366861631
    0xa0507080901050103020907030b010e0a0b0301061e050a0c080903060f0a0e01060e04030f200a03091401140903151501111501051e031b040f0b0f0415050a03030503 72
    0x2100d0002140c4070014851541a00e800414440c1c150f036400343e04501801c0340081c95410030800501d10361341d5481c0d04100308058070b44030a0560b01c81d81440300003400d00c5c07a440d02010400344184111412983c0003000c1b12a4203845180c40e540000040c00d02d0382261080c0c101c0d0580604c180000c000012003012012402103241c2c44c400e0041d864440c201c1407d80d0b525000b10311040c0624030120313002901401110400c0145406c080380308101d03407000000d91601d600b0020006130011036a1004050f803102c800005051504440e554015a0400007002160081d0464901d244002038260056904005c80c81404140380c180704403901d48929002c8030244850388070b602081601140300401c40300072800004485220750f50007140c3e0702c0c100806c2000c0008680f0400001c1d090b4a5000c4a505d00b80b0142003800714541c000e03007940131080240011200d20581c0a540d80e1705c0c2c0507483d80a55101d42c41c0401e805801c031000300b41810943d60103520300180c0e034401684442c20210001c101604030010310321422 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 366864118 1250 366862868 366862877
    0x80a091509050d0f1409120607020f010b010c030e0d11030106030503090907020102032404110f030708012909151308010f0908030c22081f020a02150a090b0a0507 71
    0xa10f0301094495400076144800403451034112004180c140b41d004d001c02c0c01008020020f0001c0b003070702e8682003490658100005801c180807118000038240607003030449400b0f1802500702c03100c40d00d000707200c0821840070034410b41300b0200080c14402c129400758007800700100200b246991b2441d000b5a43ea00c20100f0501880f80c600000e201e01d030061099030b2041c00c0c8201301c0c0e080820800e1824000c080c000102c07540c000c2d5210070582c01810300b1405802803181a4056581e0303030500000103020f03030605a20008511190a16000c5142c0588911000c40494110100d8680c0321441c001191141c00d81d83c501d5901c40e010510440014200320168101da001800070002008400c01d1103054581a20024101d06c2040001c121580303040801000c00f500000c58200802d940380300418007250599014a8030b681c80304002c401c07019000d40100304100c06103081145008071086001e5121001e52440c10017103100200021264806900310583e81503010b200c4440c54a0f14059107001003805480400008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 366865368 1250 366864118 366864133
    0xc0a020907120f1a1201060e070306050414090d0c06090f0503030103170a0504030b06010c0609050705031203040c0324050a0f05070e09010e0c0f03040602040812040e07080a09150905 80
    0x4400d441140708120a10304d902c140f6541100c107114003aa0001520300c100d42d81c560340050703581c03e10703213941d40141c0c070507a000304c4c1c0e9a03c2c240810055601300d1814000f28143c2c1c40a0101e000300020f2803a50301d44140c144800060164241007008064510707000d404038850300c500380708009000c001141624410611848882c60b0224142c01d203010380f09115020880400003400883c4203410410f611410506d01211080a10b0b6120000d64403c104121040d520050050000f45814004003501042802c10b09042d0f1515858245150801c0d10000d0705c4800111070b4081e01c808400c8414000d51034580c0c080c0006e003000455100244070268411980c0c91500021410441c890315901e0b40700200106801066401c00781c02500d4403074050001c124440b0100840002c2c5081c60020398803441c020000141c4545c5000070302c40c101800d2090000200c58108024801e2014840b80a90086828500202259a29855240100341c000c101801e0700481c640b8514409925410074050b4511540548082 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 366866618 1250 366865368 366865391
    0x20a08070303050d110408100b011d01120e030403050609031206010f0f0305090309030d030603020405011703040315090c080c010908010c171f032d02060a050c0a02090712 75
    0x10341195020090000d0020850f214100440360844c108100305d05407801e250a51f10f80c0100e03d030000300303a001251940c503002e5000e410340e0000b8081306100a4100c038107020b40c0704100001e140101c1c007450941c6055852a014203a07490401c03c0d2805140e20000302d0300c07141070070000d540d0b90350400c01b00084150403981c0000d8072548a2000034007240c041d51a01928280000015005050024120b80700762100780044805941d007000070448a0341640c600140700342c103600500080e514160480c80507040040712044c500400001210200c03501b2900c07a200b04071810300c7c3d800142c180e1003000b60889042c0c0d04040365900300400c220f190094241c1344c00340b01c1c540e1a184242620a100a440041580001c50743c84a0302c04400d003580c403804040e0540d05403034000e4015080c0c00500c2d0001e4840c45025040342c220100c22805051107a00303032201e118104811940060390b18450b038400b001c100540805d0801c40491304015643c80b00340d005202080e940f9000b0f00c000c01002c6003454803040f5506120142d40c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 366867868 1250 366866618 366866623
    0x90b04140c1806042a020f07060e13140f010513110406030c140a05030916080c0f190b09130203100e060a0305060c190305070f031a0301050c0304020a08 67
    0x180190040d00c56074500484025014500a006011135002a00d843c151140c51458188034030421010883c0341980001c002d00091401c0b40c2000b10075401d03405900300384443e80c0c121415a182ca0400c0312940c1c0204000c41400700506085400007042c2102e2205002110b02545015416180c00f80c81c80e5040d241c3e0f0440c4801035944032152004024030400092100790310940006020301c081f0300303080440c014142e007040c1c040d0b0701c0440701000081011003840646103090183c0e4100f000f058038020907950074501084d84070780380340c44028030030710344030f0b011804945440000215044000000d40c0c126075880301a6142548891049880350741807800c4141010081d209407805014003605450030f180c1040464010b02c13030003038003196218400706d00000000388104040c0788100d00c0150004c2e2a5a42010080320030904403200c0d00c00d1508082c1041070842e4482403001100d07034680703008a56043c0d800c05010302c0d100610455a05035003070401304200c0e0300d283c0e8000c42c00b9900c291070140c1c00300c0d030702c004058 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 366869118 1250 366867868 366867883
    0x20a03080906040308150d0b1905090706052208100e160e0c0703020309280b0421020109080a052d030f03060a05090708040201080c040503070603020705010906090b0414 74
    0xc02151050011940481540100040040014025a4441d07c082e00c030765070500c4045849040c04242d1850400d450002802250b0304200084010302090f418108090810b0040140c034001c00701112012402286401590500601908058a405813000c40c1c00c1d401400034800c010b1591310904ea0710798400c102c60007040c0100c0e061010382a0b01500c8100301e1107041d9111141c15070451005201c0c1000c07a585061444016480c103030800307160081d1444035240c0c20040c56104081c035000910040084400c40c04059051403220f41180ca4080000c0c40181c034801a107401040030fa10951412108000d00001c0240c41e08000b1190412000b80c003500303107000c0c3d031030340d041d801c0305a01f050000c003507094100c20103585c110500614000308036458201280103014112100c1001a92050520041d542c000400d0380d005082c007003810703140134105000309940b032405108003020107a0020360718090110a50100f0200b55110340140880402c80c10483d04540c1c0544050316440c400c0028480910340000d20203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 366870368 1250 366869118 366869123
    0xc0504060e090406061a0c060a0513140f161403030403020a051302071505010905070807020618070305060703060f0b070b010b0c150a1a04050903191806020a0308090604 74
    0x20030280300301002d0109608000c0c1089a031152215030204408014141e00a010a41600516114500942800d141c820041c01c218015844c00080c000b556141030181c1c691590045086030f01c0340d5005401a103001c040442100e1240103088402c2c40c04e41401d8000001c80d036000d00b14003507080b00002019220f1090741b000943c003440349541006035017002c42c4840e04a40c0700b4240107050144545500084200016101c034145540300014031100d2242d100380c2ea08002740d403400500c40d1400d00c0c03010f591000003030056a95010403824a540c0e0745020840500610350001c1511003a003440c0001501508142c06840060b43d00d0000200f1808000c1082d107001d1900f25043c00b60030f92130600640065072001b26031400e10b0240e485501004030310f007850390b4024bd80c0b10000240042c80200c030011503840e0002c0740341c03190f400c00c028031404900c000169280312100103001c2c07030b82d600c13081c0d400d6414181944030720401c9807038040c0014800d500802c021003000e00a441d01011560f9000c0139076107684048800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 366871618 1250 366870368 366870377
    0xb01081014031006060c06061403061b1308010902011e021209040204090207050a0b1503060f060f210d030513110406091a030f0a0b13030e12100c050406 67
    0x41240308028140004000300103003c3c0c0e01284400803d81d016101c00390000c0c000301c0c0031409501c040040600c507500060280d545418038258207640041d84405001c1d00d0741030408520f10302041404254022105d4250005410607215645d503802030307010b4145903034140d0100d40c05c2c411084800e90302070305201c9580c42e0b5502411034418010f071620960740101100e903800c01e03402c0c880032401490503c010007000740a28003c0050302072500c4c211170a00030007824030b1881c0514030549005500d0000700541c0118228100250658642001c5080020014003040d80001c6038100b00014030b4420b800300d030485151400761030200c503070800d054041c4c65003655a100090090300f84400450601004488000402000890800d58540c0300400740d40203080c04240d80034011010324110301d0308100e40d9961030760f100090422616a0f444a13219054024506144003400007003807000c0602c551881d401c2100010035410002080e1100300d55185940500001e1140c5050b500030a40b500a10644e021250540d0b01c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 366872868 1250 366871618 366871651
    0x80f010e06060d17040302090411031e03120c0903030301030f17090d150609110c1507020601170a121223060103090302010204170307120906120c020f0a03050d0b0108 73
    0x4d43d0f810f09140c0c038105055102c41070201100507603400c41c2d0580034a0051081444100d4003104050500c0080250b10b503803240b4070140782c90140c1d00801540e0100011000e00b00300b6683d00c8004041a21030020046e80c075000000010040100f100c01c2c0420f0306000307001c140711502103c40d8810702c61040d0503c0540c4840c182c218000014220340c2075080c1080070350004100303035070358030140301c01d44038210320300e15841d840030415040303628003003201d0b450314200125803001a0a018201a41700e900600640100c0580b410350040300c1242040f05034a0b095003c00d5032444182c07800c2c001810708070b01c40031380c1010b02d060000c0740e1012100768001010281500028a02c50340b110310042d402003c007000b08a05554092000045441d1006031500e65100c41c4400b45035507079091f14041c5040070b05441d100c03043c41081a014030076194081403c5408030207000c000a01c04100b004c080c2d203000c2e50718410300164401c0741884001c02d81e0140241489046050301481019182030041d04e00c410f00719001455600481c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 366874118 1250 366872868 366872873
    0x1d0f01171906020705010e0c120102030c09040c050c03030c031005040b010f1101090c0e01050a0602030c070308181c0c060c0b0f130f06021305120a02091b04080f010e06060d 76
    0x48074a110a07101e010300524094169448509440080d1041000d61304803211440f075509081800c19011b40f0704030000c40c0b942c81c0181b550702d114000d044800f8003480c0e4401d8171071400d074001c0c01140c1c280d0260304110307a02c0303240ca03119240c040c2e801180c244001001c00380c40024a030419002d1114005416103e05e580d581d0b059104581078090542084217940d02c654101d80483c9801070400081c083c0c81490000d158182010301c42d00484540c4084219801000343d0000c2c3e84c0003081402c1500e6001440e80e43e203600314081c2d040450240788080b41d10070401e50f1450208c0500001404000f4810b4000034000c65866009503000000f0610103842414158005140600d0031810a0340c0301150100c0c0340b14a000d82e458150f007038108010220b9103030f540065041e509044103820a07000700401c1f6010940ca041d00d8000c60303200e09500300000c3c001c0b0040c0d008030794007610341c40c030b103180710b40542440726111640c0b41146681c403195100000e0b5954a0400c1c20425607a0208205214100c09064200441440da = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 366875368 1250 366874118 366874153
    0x102071d280e060919030206130204060b040602010209010e22050c070b0103031701080d0509091b03191a0f090c07050a0b16020a0c1404061d0f0117 65
    0xd5203900c400c1150342421801c50401c501c2218411400070009200030310b8500020351912030221030b0b0074511a05005c0480000e0740c00519a80e00c00142100c42e040c1030071a01c0807a02418494009108650780880c2c00b282541c2c1c150b010b00400071090303882d441070b400c00c90240a10003c07190800e14407401c0702d00151b10300302d40d150000c41d002422034244034070307100143e103c3d00032402080e00200d00143c0c90b440d10106810152030300701d0140150074050036144066483c041d00f180300e801d080b140074405004c0018424080926007588891940748110781d20319024032110f00c10900030516980703161030441d0500c07803030101c808411500000608400c51a408820802001c413900078080c00304d4078030820001001600170302601c04554400c407a400e000e41441090700381070304540072080c0308561008031801d010902c0d8034421000c403800701c0c490343c0083c0440b40200e0040c2085410501c03501c2910880400b03143d0107445e040384140740754010701c10580d817100c600d2080e076a401101052564446403216a016120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 366876618 1250 366875368 366875401
    0x2090102030c0109030c031701060c2d03020706110606031e071809020a140d08031803040305070f0e190b04020d2904140a050402030307020a0308090102071d 69
    0x140100c03410065840741d4982991684c0c8801c4000130310f8501e0749000c05400040714544251114148616581070900c01001401101c4002c2d0408596a03075a007a40b440405455144400081c0d41c40092500d5041c060340da91400d02c640c4000a502d00c44604003041c011406500840000b4082c04840b00c44070312055844240983d8940c4030b0141042c0041c060203141442c04141520241c0490054401e00400030a4400da80c410900c05031107000080d06540c0c0c103c61122003584c803025040d202e8695000081c80ca240d0003c20701c08620000401005100b000210102114010003818034000d4403200842400e54040d0740d0310314007203011154400d11102d56000f410094801030801802c1400c000d0168094840c40d0b00c5100485aa0300024210300e9400f0130744030102b500c1071b5402c4c0080088208100c07402c1c50300501d0081c9103035680d00070a086640a01c12a03030380030f400411801100d6203130306064909a20260007180584034424000401c0304800a45111b00d5041e8010079850f950b41c2503095204008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 366877868 1250 366876618 366876637
    0xc02030c120f0616120501030b0a090c050a030f110102120d0e03090603070519030b06070602090310110d05010609030804150909150e012102011b21270902 68
    0x800c030403494416400c003c0a403280c003895000c1011a408484098900008030388100c130085d040c4030050010481501085030003d0100c2ca000500c42400d00300f8035546800b980045900c440005000404c0c000300c046428400b5001d0300f1440304e645410300069980702201503036038011101c10f02c40c8082145032548440603401a00c0241e80c0350000c0407002070101d910440c0d41c400412804980b5050504204d4507101708941d16007010003851170041c000428034003821000900b555000221900789480c00d024451034641803100c1480a604800f4600e8410303040054030204036031070000000390481c4542d00c41c5007282d401c0380c106850709090410181c3d42803034066000d42440340c0c10718000340c840700070312844003000384403800180b80710b003415090001c40300c06038440403c2d440d0f9000d000780349034140390300d20801d20744c24244009007005020005109001c049400303005800840d010400700c0c4030341407a40c07251000955460414411910703550071f141d40303024054807000c0e15210044c13001481c1f5034000c10340601c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 366879118 1250 366877868 366877873
    0x40506150d15030b010801050a0515100903020409081b1504020d02030a0c090501060e010201020f09060c0a06090f0b160806010807021011130b0c1b0d05030711030d0c02030c12 77
    0x11440d1010030002c0740309a000300c486039424001001807046c203109940d006401d00388180040d00300740b4400c00e0017040c0c03c4110381c401c448916016900078040e0001e00025640074105101c08041414032825582141c850b40d65a40703040080d640300410f01040840d0941030030b121001403511140c00707001c0c0040107a00c080740c15210f160f140782c000c00c20040c854001040740351004202c80d8102031009054070000c00a1034107682c014400510115903c40555152400c21759002e40c580c26403a40300d40c640090110080d01c00b51800c0900c00a00451039615440c80e03002d000e5102154491201080481c43d0702450480041c1d50840030070b8096110309541034000f009841200c08144150b0600c808848085008014410000400d4042e00104202200c02000302000b00b500b00880000c10340d0301d6042140e006441c0290301350b0480340c4c5075100d9403c0841c20360092308980e11000949000340303040720340003251840792045025080000b482040954034080e40a0082c0024003940700c10b101c81d440c031100c0800e55a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 366880368 1250 366879118 366879131
    0xe04060e160e06041d010b0a1e05060304051c03020a0305010e07051b030f1b011a15090604180e061008070302040207051c2003070b15010c080d020711040506150d 71
    0x5030025100c603810042c1d02d000006107503003130b0f4040114801c159840005d4480c0c9c15042148802c10a08480003152030a440140d0b69580b00e00e082d5050030801c0c42120f8141c0e002c11540502c2d2039259015090360090b03a10200300a0740c0312100002c00010494503500092010844c010b00c5401500c004401c0400940482e828098140b20080c041e0700030700e805000c4501080c02c4003c4e2418240544507a10031646407103100000d40350040340d000c00c0c01e80c98801008200040c600895140c002c100e60085c6498155a4a12007840d07861001905031500803450600c18107000c180345a00e0000f006003110001c07402407443c07900e95400d00003c2c0d00140016190b0f030185c0740c280c3e078a04180c2401e52004d4000c990724803a0806501c1054030038290700c004100a5580180500400602106d00d8141c0104104052010740503118004a400c140104801810100046401d00140c8aa600a0079056110b411504a4400008140011075034120740c035070380c44140720500441c6602b040004111020b4041d1011441 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 366881618 1250 366880368 366880391
    0x11203120b0603070e130b031c0e0907080411010306060e040f0b0909032805160f050a030816020a11010807090b120402041d06010b0f0409060e04060e160e0604 70
    0x741c1c00441c4c001c0c0205980c41c243c024541350241c2c81040c0100080c0301001080342c0580402d80e5042415441405580802080d084170790062401e00012280207000030701915002200800c01401a101210742c2500c0c03150061156009000300c1d816100c1d50340d81d64800c800000108805802c254141e0f106a41c0d8625900c01c2d203803120b040c083c0c41303a0341c010010b5a03200c40124078804030181d8a051901c0c10310841003441121940002140c090034840766101d80c116406040003c1e04014150006005115427150982055085032459104105141e41906040031081d000d0fa2280161000145100748000580c91250301a61380d5940110480c03500f40516501c0e5019030741160b0141050f21959603610301044111300d001c2c040c20b10a252803a0b020101001c80000d22545ea03d01070081054a85e004180d0f52074001da030b076050310700a080050082c01541e07502c004041d100002aa0281c50442c14585d416249090004162204c6990312421841043c9400c14948120b10081d11050b40a40c07a012040395 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 366882868 1250 366881618 366881629
    0x1e0203010909050f070f0506030c040503100603030908120d051f030f020f0402070b060f03010b04020d090b090a23010f02030c0913060602070e0405010e06010803070c060503011203120b 81
    0x20348185440040c0c01e2000f030908a00e014400b080100041e4030500060280450300590601101d40039601d094a03902d601d6080f00e07441c0200d40001d0b030948101c000600101e4103a810141c12240030703840e140e152075103501d0000c2d26914441c0350b0010541c1304010a501c110041d52103246e12641d00740e03032200c0744c61100c0364072440c00c4042d60040d01e0300d0800301000320640ca0a0009d090018900300c40031072800e2750315541d94480a00080c0241e01ca445500f602e4501c644080d0040201a08020300440d560b05030010480c00610301c0342400c0e2003441c644000a01803403c0010f80b00780c070b150009000b07849403002030341c0070307460141030340c02d4200c03c2d502ca800d041d980c10014005140104c0b0182001c94403102c100052105100003607284035052803c14004001c2c942e004150782003625889030a83c2625690b07401d0490242030071311b8410085220b08400002e041ca00440600b0050744a802c0725409640c0d54441101c0e0b41c00b0a00030507003a4034000e0350103000680035071808411030503005030105000140800161 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 366884118 1250 366882868 366882871
    0x8120f0d06081903021207020d0605060409140f010f140115020a1b141009090218030307030806090a0e0d080402010c0c09060501020127061e2301060c0f0201031e0203 73
    0x400424031840708104140d014402a040c0d420346d030360440c1c100030554001402d691195000035000e1952032000c1503098540350040c088442d00059075004d120704100b401c2c3d80e02d0000c070001d214254030f4410f201d9000d0405008500c0112200030401410b0b90a01e103481280c414000508015032141c00420000a5490081200e05000c00009000303502c1c82c1c82201c8010900b02404244606442152483d005410691a00585503080001610350481920740d065005091000907418480031a0940400da800060300d0b1080005440d12203e54503281110303c1580c0f11075010a07080c0d042881c840031100e22416006600c18014076111912007000e407a990051a415000201001e03162078090015507024056180c03d540c120240d50760500580110b490303622403812008026980742e2103404800405121200c1072490b10b400100700b20b0680341c8804100024452011004141540001030083e015011011300b50360007288005440891307500440050950b180081c1c003070400f0340401031a0344414401b45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 366885368 1250 366884118 366884143
    0x50a0b131706012318190e030316080c07080a03090602071103060603120f0306011808061504020c0c2e020703051506100e0301061d1008120f0d0608 65
    0x9045650600d01c00071420525038000c0c0d904c2c5003103001d45400036103c08443e035020b800381406148064950a68070b140401c11490801d442c036042c4651008142c001000a600034003a81c080c16070034142c0c0b40b8081d100203130308885000036000d0501444012401c3c0c14008d00036040d0605c1c000890500607038902c4200d0300000403d0b02c9051f0122084004c0f400d042000a4008004800a2003c20040105040e2900c158442e000e8107890120200f034469004401003000c2200305000000c8040d00d9903030040d9030b020100d9004a409417041e400c202581010f00c06c451032001c00d0f401600554815200740b02c081c86c42e0242c84400c0e82001c0100403d680c007903a11004000110754050031940340b45062092511001001e41041d0303400001c00e10080c1d6032218174500910380d0b60309003210702001c900006401010242d01900301c80c440d0060074200001896052803061061006854144e03072242d0580307584208c03082030307a00096020003204100c026007001500e002880204007240c119202e500390740c02d100c105c0d07000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 366886618 1250 366885368 366885373
    0x2060904020313110627030c0d0503120105180103081b0709020414120c1915050a110705060d0e01110a03140106030c05041703160822050a0b1317 64
    0x8180030003210090680c45400308954141c14445e581c000c0002c1b01c264000a07046809201d040c000c20b0b40c03002d20400c0c800741e40050800420002d2824110b44944c080c0840d0030340e65054800100d210f01c3c20ba0121070b07013081c40501c580c0040e0708560f1544800d40c0004d0081d0843e100310103590701c10410030440c2d800505010384002d42c4440c909159921807010702c00350305110f407026941e0341c40030940018404441450031185034025800c100814041c0b840f0b6504014001c04d044091a00c031180c0002c020b01e00b034007140e640c030804240300303c03881d64903a8030601520b540600e0030409030107001943d4018583c20080380c0b0000452860103600703c0cac0709600900d00d0034046a150789060500c092031008590051903141000d004000c40710000400398481d46c0503590701d2070520f07840046140c0c010820381c6c105c80014642d0b50401d5030542003251054000a41f400a540701c0034095070111484c41e2403c4041302c00240108106a081541d0074019822800d5180c018240e645000a10308110103000c2c203e50800c4000f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 366887868 1250 366886618 366886651
    0x40905011505010e0105120c070201050d0e010c080601022407030b031005070e030304150503150301090c0504110f1c02090a030c08190201020d080601090b0a05130e0402030706050304020609040203 86
    0x2422088408141314180081404a00c1000d5200c511540c2d1013159903250329990282840180c805005034180f0100d81c5150201e0504181d030154030150864100d0707101c01c002551401c004981c0ea410706840c000c11000c3d04014034a94002e4880110382024503070401003440e400d96070101b842c015000454000c12600c41041c8160729801c0b901c00b142c1801e0a80181d03103843d01340690000d1503442e0385100e900b0040000001118080d540f03812000014004000303101c0c100c503034180502003002d18003429114a14040008075038542d09006c441d082004004050304000b8041098410740741c030380a14450054007002000c050343e42d801e0085020b50302c10400b0f02286400d02280310310b0440315400c04070446000410040250ba000034000031a2922487c0241c800d43c0c0e51001282c20100e26400990f03421404600b042129030801c019120f806c0411407a040c1059841c1010004000c0c25100650140c12024050041034170940065600c5800604030502e84000200441c0072030340200c840c0c05c41100c0d01c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 366889118 1250 366887868 366887879
    0x150e2a0901050d03080103030e0a0518060405070810030206030a0f020c100c02010c0509060304060608120a08091504020603040614040c090b0f0a150e0d03091d04030807030b0409050115 81
    0x60429001d000e0680c3d4110090019540c003070202001804041c003840f1044e1301c50b01d456591102c000028001c05003544580d1500710710305034210030065901601c50780c01c0c940043c2000d44a070070087e105072840b4a076585104e01d99024010164009044400321680b0b0303040c401c50040c82c81c001404048800002010302a2110a03954116190f1030490011a410200b5020308036521400f680d143e2002120f10981ea901c8500e0180020b0110358800200c0340034940681911081440190183c01d8081c0c940a20300d0382c0e404401a12072031035100c03480510222001180141c00c19101440c3d000e4030034240001d000c1202c80ba40c0760404d008a40880b18551220020b101100c680d00600d421000d0907a0040c0c150701800c400038400301028081c15001904040944015038426000392690702c0003d40180303011001d5080c0188180200c2c00381d0303125180f00c111101810314012240034490354242d903030005140c407040d001710090700454070603d901640b15106074010643c207100e03910030096a480030b00c140c20b00d4030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 366890368 1250 366889118 366889129
    0xd0b0610050712210905160b070f0b040812100504060e1314030913140106020607050f03180f0601150201020f071407031403091c150e2a 60
    0x600c00c0d404104052100100048422801c2c2000c001c2c18100185038400d054006041c400807240042500e84c1413800820900001186a6034030300b0000601c425403648a251441c2c440c403540380010f0800e00440e03542c00105084891507a0050b11404115107020481c420400c07a070b030b6095030910540078090340c08204a01d40340c4262401080b00000030321440c03910103c440d01503d00d01e40c0280c02e00040c2c0b00e50300c018840c103008603064640028540080c0405059860b07009041081c0540200840c20002058550001440c1442184035640c0c3c18a0289078038480106a04040c0070558104200046044410000e0120301300100510f0024036440d0b16100d03200eaa5101d40002c01019644100144981d000000003281c0300242c201c05560411079440f0000b500d40031f0640c0c0050720380502084a601114070220051007043c504682d20501c81513414030440f050341c10414001d000d483c00210254190440c2e8110002c112560002c2d2100c08000a0091102c2e1200525001e1040c0f201200d00350b440c50320 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 366891618 1250 366890368 366890389
    0x1b0c14040c1b03051c06090b01080f070e150406030507030b090c070201030905030906030414010b0103050c0301211704061403011a0f090303130302281502010207020d0b06 75
    0x8903014406500d05041c00b400c24021202c0c4912a00c41035442081894014011aa05100c51406a403801030340c411151008150b0360049070616800c00c10154103d40c450000e00f8060040703280c080b0b00c651200b0318166907100b10302041a4201550a0b010101c0d03080010240006110b2520702040038030f03012078000c0840d08084080c902c41c0c01d804c0e06100e80c084420301590364245d4282800a45a403003030802503d14010300c202594031013000000c001c2002004403a0030310b680740000007440021440c1e4015000d4410480303a0a0701c030002030004000c096a00d40e6005120000e40c1400e40c16204584c9035203800041e11500e10941c02030001d420070502d98803503801c41a80341040c548600307650602c0041034aa455800000645e00750100b400c0040268038002c541050700e0040440341d4440b4801281540c0310258071050f0f103c2c2c1055020840c45d414001060448480d40800e000c50f42420000039030324440804a1320811990f091281c1001030b2034ac8505524100e000e128401c0d0546000303420410340080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 366892868 1250 366891618 366891659
    0xd0203041b06050d0e07080a140d0e0102211201030305190c080702010309051509060a0f0b030c01050313081b0105130803150d08031f12050316031b0c 66
    0x31450070800c4032981c00000e41d0003d030105900413490400500d40e85191051310b03000301c051409404034071005c120f0194040c80e068806001607801802440c1000e803000040d0f00e802c00d01682007030702e40c10340d06008214080340c07405440110a007000642d070000c001d030003000d820460200d68005100800c0d90356482c2c48259412081c41c20003552030b0a81e580304014005c1a10080c140354640780c40400f0018288401d0300322003401d04118581e0b01d016410706d13941b41c1054810221003460031030018407007030883c018180b403404090001c1084627060300045072181c3c8000d0444042d8074602460038005030016004002c1240380203881681d01aa01546508468014003405c0c003140420640200140c8001c095a500c14400002568580c407481f01040146602000041000303000200304400300f1903002c3c151320603050301c185c040805520750010360f0047d2003003400500254024040c4000c403180c1d12242441032403003031614003440c0b95a0250b0401d040301ca07200c100d40c01c21110500380441c84290590038050b05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 366894118 1250 366892868 366892913
    0x515060a050d0902030c100f0305010f0302030a0b04031e0c020907090608010306020325020102122d10030210050c0c240a2705030c0a08030406080910020d020304 71
    0x402030300c8054074510500240b41040c5450300551819507800b440508103209010781301d4107036002a080010000740030b84060320301080c580320001c559515460301070026030398050000c00c0302d501c03603454102d030001c401002207080040c41d0342c1c0000075080400696000300c2d41c0d40c032490441c008900c100554190300a0800f400c000003c0c504001c21681318041c18116504080300503525220391003a0152034480d10004c1c0410014114001c070500d90550003090030440c070011412a90f105d80c6813180c580341040c40208001c0d074600e984d03913144901d44647d02d0b800521600016140d030707139a5808961281e003070003100300201d40c020910a812030b5082c07010004003101203e0b1440c018040d1900c000c4180b0015601c416202804107411500600810826600366080c901020b41010491582c042280050040c0c0d8001d02034060b002c00e0782d05001d0b005500303036560300005c0c505081c10420701b1201c1c9480200f4a24a0388900c10301030464000d07501c024008105000409a960f2505041007808100f00a80780e4060b003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 366895368 1250 366894118 366894127
    0xc0906090902030603031b0f01140f0a050114040218090405061909020a06030c0e04141e09030412020607081809150306070e1914010224040b0406020f0d051506 70
    0x30741d400306c12a408401d110715050008192400000d01d00b00450704504401e42c80d082d00200c0031250031400c0741c450244079000481682e03c6a40000540f0700070310070a0075090380c1c0707107905109162580150141025211070159034042040004014540c00e0764240d4581c0c0050003800100d503840520800b1100b9082c0050014103543d80c081044441e4a00ca820b0030180c2c0e40f00780c202d8191042c0f1130752801100c010b2091000c100c0c85002c403d41c03004140d031918201a02503442c02201810502018401c0c426a4055402d01e49030120ba55100b0303140203030492740b21a0030080d1400050b514400b4190220b801340a55090007801000e014140d1005049440c051071400042d03c1070341c1d40011450b034094060b25015554025000101c0c950180c00e0a03c50845040c039000440c0c103c0030701c80f0502a111317003642124028580981e0a0b030130300054141144001c1c0881c00041c000c588490035031500244180001840c0441d00d40141101d43c0104070200085070703e9806015603d130009a1215041e0230072292103244c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 366896618 1250 366895368 366895381
    0x50c120112140607080a20071506050f01050409110f0a050a18080d030e01270209010b03090604030807050706062c150f04060807060f03060902120f04150c090609090203 74
    0x17100014405000180c0340d00d0005841c104c0e00038503108080002c1c0301262a54440c0c90a0998441c83d0b040b4501e002d442c0110010b41c0307140c10340510100301c40c113071142440c0c9400e000c40c07000a0b18644614048050040001c400da8051080003401021400c2d40c0e620b840d0036441900600b01e88145c1185480c42500d640309010755000801c05021900c03540c2000584106080442070140c00c60030001807130203840c1004404c0190101480b025a14030840d034040d0300da80c8031b50301c01c4cc060100381c4420403a0f41c41440020300090251850035004010b41c00d05506120407076840506464164000154405a10b02c0d15504118511500c0c2010381c0d080c10700700c1c4140b41c103028808003040044e078064414086440c0c18600c90311241d10800151540b1816241e02d0b64403144041c01c024032000c041d10000b45801b00019a010544c402e40e2922103030001600482e85030a400b040b15588050b0040e103c02024140075607030940540300d95a00e00400d52680180540b5140001d42030280550064400600400c01c0150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 366897868 1250 366896618 366896627
    0x32802060f0a09030e130f050604020c030403020904051f0207030215061c03110318100903020f0d0809101d031603080f0408030f1903150306050c120112140607 70
    0x380400e01c2c034000101c807009801c04030303036a4460b0140350f5005070303400200380b141850030f4000e501c4560765410305101d00d885520502c0124422001010180d400c140002c1c00140b505034200d07074115004804880c458092110785280003c02c400710341c441e4580c001600010140c041c0f04280b8000a405000341d09450908080341012041030b5402c0e68060000c038011041500603c1d00c03800b50300f40c100880e901da20004180f40b1003c1010440203100d0190121480e140c0c0d80b0822031081902c2d0f02415800c40c140c00d0b082400030030f102c001d00444400340c007070004c0d80742500c03946240b840c42001d036a01e01c0c4002420701032100c400741c2540c11050098002c4100e0100c660383e001e0344d010031680d002580c03070350310103003401c60400500864010346224000020054092000c401c007510317000a03e0345071042500c0c1510820703403c032401c17942844610f0100c20301c1040883d04680c0312585c0700d0380320760b4010314041035001d255000c01c000340c00411204030789081d8582413080c0302e004503603580401c000400701e6060100000c0e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 366899118 1250 366897868 366897871
    0x203090915090115090b0c0105011d040302120f04030203030a020a02040f0624180807030b0a022a03041503022110090c020109170703080702031801030b0f03032802060f 74
    0x3c030a81d0110000d00185485001e00c0d000801d24480c1098482104505d1f81e0f01814080c480c02880714413599200041c10a602603141c01564075030000d11034000300c2144450b81c0d03040500417540b083e00c10b000002c0541ca041c401444428001e901900d401c00e0544100700444883c903240c0c00006140030380034400d060400d040540080b02c0c0d008a41000119030318121004042c6000412161030120310025500000150311000c3c1ca00c01c81d4808020f5032551403203012230050412030f01c1c0d600741c4010b4210f0088100c504a145094a05054074606034031492002c2051020b00c2d124000170340c0c0007981c14003030222800f90b00c902c3d285103007072440681005c0154654911040c0a51403101d6500c4c1e0215150364000d612041045511034015545800801c010b00c0d0140c02c04030082d40414400c0001500300c1d171000c42100c0d20740c0c411038039004181003c3d0004400034007140c510103400900d261501c0440359010005007070710382101c00c605a1a03030310390406114071032160840c1e40305550007001400811029880b071503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 366900368 1250 366899118 366899129
    0x2100210150f0909050304030609081b033123040506040204050109030206030c0706061d0a0603050715020313080304050307060c0b0c0f0909040605071d0a061107090c02030909150901 80
    0x85024021030400c1070847c82241e00040c600361405206d80c0400c809800540343e01111400b130b02d1520705600100070381300d210760309040f003050704021419400b9245004040740d0600e042040d81010545403800041d201d03032002c1c6556020780c01c2c00c07501c04540c83c00340036260b8005801e540950510340751000103840040340d804002c0c440c050200009007011501401c0e50045500000705018182e030f1801d020034000010b0148070320140000b00044d51040c9640122400c0b69032100060140c103161440401540c00009100c2d81140020003010301400c942103000b0300034110300400355681e0303881d1004151400203207a0220b014814014480e42c00714040e100780e01c0d8420803240d1307101d580d42d00c0d80c43d050301284950402d803a80007010106210030b00416038003191180d1441c0c0c035103600015190003049880d80320704191503404800310400b417100074442c00c8240b00101c002801c88040541302c0041c2d5080e42d810b220b200780140d0010680c80e030280b406541c0250048440019242c801c18400c000c202010b6050045 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 366901618 1250 366900368 366900371
    0x172a060a0c0519030614061201091d16050a240309032c01080c1303080904060e180610050d12120606092405030a050403030902100210150f09 62
    0x303002040b80201c00722224008010807060010700301c181d024005200900910140f501143e02e448440d0510400f22440c10703e0300d40b4501c2c8241e10b801c00e8034015240f008103c2410b00b14100303500b00034020030800c070301c280440e0016135490b490802091010fa10f405a00c4605801c0e00c62104c48a011333030200281010b80c082e03142c04541054a030400f075070040500c880c000007207180000b184a1035992a0190b09100c402640c3d05215900c860300c141c80603005084403100c180110710420400900039000911400c4000f400110350070380c0d0f501040800703450455460708036244008a00300c0c944d80c141700c101d92003110f080140034400d060102154203203000c02d0000b0010402e030020303225082e000d0386030414034401248090162170b84400c401401282d2a1003070a00444102846900140c201c100071642d0400300e03036a01d411980d5814039000907000203403040c0c05040d035030303031603040075894080140320701260301d4000f46442451400c2020840726000c16011800c0d004003000c0c801e0f490580c03924011030b00e00b03550 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 366902868 1250 366901618 366901631
    0x90607030806150a020d020708010c020c0d110a03080a1412010b0c07030b090a0302070906210615230a06021f06050a080d021603080d0507020109172a060a 68
    0x2286001d642004542043c040200d050b20341d043d0700040950b14001150b0988034a10b6540c41c8940c240c8980180100268100c200e2000d020b04103503680074001400b5002c682c002d11900070200709500910f41055071791030030003e0070840d910b0300142214100305040c0503152611514101015403040103016503a0030010014010a81a00420141000d0754021040f40c801d401c2c41c2c80466904c00c044031084003d4001d010000401000501c500d2080b00c00242c20442d1442c845401150f015000c1d00040701c006644421140301a0b001082542c0030341000e1100742d511030f494400300d559440d41c05480d80d10803030041400344503140e8007166104075440d190550305098190140080e028040d0b0380c0009400145100c00056000c00019800700c3c502035a80a8490300d0040c04800c00b0741d00ca50f4000a0402c030302c03c102d840c0207100b05034401c80e44807490703100018200d6640d517a00383d042c0a6008030700091001c0841c8500303202c0500b00044a809500d62001018959224030302a03e440005121451940c1e496030f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 366904118 1250 366902868 366902881
    0x3121207030506121507021e0303130c0e0106050301051305061302030c04170309010801081506010e060c10051510120b030a0807081c0522081b0718020906070308 71
    0x4c2c01070142462480903641006183d4030300c09104d0008650440044c410b240e00e140d001c05452441d1401c002e00007001c0e624541d075264038070520b0706441c1e104444e1800c1c000ba001901c2c000508e4070f54003903e19940d800c0c0d0349500d0441000f80c4503510840f95903200c1d24060078010b00703564880048200306001d030030168480d41c450489140c01e000d16400000c000403108004850b070303c8003100904101d00240c03140d01c00340c1d880340a003c0d694490042c4820080640a02040040d0b0040f5200c012002c1c0040280c0c0c0741164501e44181001c03100040410300940b903906010701c01079002c000c0074850400f901c4c00740401d10144401051441080c07000c00c556680d9010b00619a14140000c46409801024080d07859034545400c030082e074420f5032031807280c0080b64569080361000d4004c1d180500c032000700c1d4031650340a801110900c0c000f046400c9400e1042003180100d10303416540f11212001c1c072240600b08a40c90043d4910361442d00700c0e9428003041c0f040090902c1603994030140c9040c1034061520040607a14903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 366905368 1250 366904118 366904129
    0x1021314221d0c03010e0705030604030c150c020a02031203070f0e0a0e250305040f0b070201060509010f0303030b0301020f04030f17030c0304030315082109040204030f0203121207030506 82
    0x40b800d40d5042d11440c411107060b1180000d900c100141c0a9008001d00c185015015403124818029254035400020115010921a03900d0314952030040c800e060700840700303180060031940900c401401603088a000340c0194607043c04401c110403500000d50b4074515140c94001c100710841e1200350240011503140c0f000c59200d0f1102c20000e0114104007000c00d007000007040351510703980c6602d004480c401840347e5001521034020b4030701441e032191107219848050fa40700200c440009201700b04640d61404005943e5880c2c0c1003981c000e2000c0302c0d802d0200b40c01d5040060548414201560090380100840c0c45058a030b0341c12503080320307040b0400d201c0050051500d0320303039070110501c0b004624001105000031031071140000e6009501c251001c01405c0c40e4500d40390b148184c1489080e40d203400c400e482c6000c50030246048070141c4c0c40c4182140c80d000400380001e0881e0001c0c2c1040d646511022008030860401300f2a4074511403c0d0f0052605118641407255603200005219100300b42d1594003090b50781d183c2c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 366906474 1106 366905368 366905381
    0x60e0105150c0606060705010b03070303110106080115030f14070e10050103050601200111040b04031e1e02130f0f06060f0504090908070203030406020102131422 71
    0x1844c04100440e0031424080d40c50b0754031006213980613501030140d0340203184242c80d4a01160f28100c0707005c1c00c40752181c010000b160b141c0301844100c00201c0c8820000c880c0c2c055040c804c1c0c09280d1616a02c4042d00d1266403a59101d95040031071071280c250203c5200b84402507030740d40125560801102030b0340c0d00f51042c0740400d44081400020703004840350b00b61001d03d1500081450009600910b920364055400500c83e0395010805104214650500100300034075070740720700312046481e203840a842c2100c040f40c0050050200c220811512040600000d50304003801c00c201d02800401680302411084402c02c903210f1600002240683c010a0207003c600043c2d51458240f03814411301d1070007802c810600384d5144a003808a000141e07801c00040000c0c08046c0c1c00903840d1828421544284481d0750020034401c40300a0601d195074a461171090200d03407018403e990900034401c0c410005040c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 366726618 366906474 := by
  have h0 := BRFrame.cov_init 366726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 366726618 ≤ n) (h2 : n < 366906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
