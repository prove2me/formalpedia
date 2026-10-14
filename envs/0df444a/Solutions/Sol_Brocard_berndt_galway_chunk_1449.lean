-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1449
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:02:43.234288+00:00
-- url     : https://prove2.me/submissions/5f4b3b40-7446-4834-864e-82b17198d2b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 260431654 ≤ n < 260611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 260432904 1250 260431654 260431697
    0x603010f230102032a031b070611150c0702060412060b0603160c140706050d0c0504030b01030b10090c02031b0d1b1b0f0311010212041401141201030c06 67
    0x6802d00d1601400c055005100030b400036442192013505000007d1024810810303842c00341c4a030145601180c010350340d00c00341240c3d4403c01100325040c40c4c0040c12010210000850003a4111050b071110500d40499503000511a03402984510203c10405d806038061065a100f824910102620164034521f0040310010b0541c40c02031040061181c0c05441009003c0540150b40d050104481100c1d10a6294800a071858100c400600c2d01d10303050003101e5001a128005840450360300c800381d9aa541d0031a0341e843d0840200602a42c80d802d0601e1001a012400e402845240d40c0d464010f555151014040640c01c203422803446032180c2e20110104a106a0180f42599010481c000c001e00b40701036441c00081d100301240300519008100300c80800e030600c6249045c0d04691049a2890340005502c00590301d440c0e6018040328140350501c4100300c02801c90354649510041450324001d144100507490742c07a50000c041d810f0740035481400500070040390407584005071245007492400090901300c2c05c0e111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 260434154 1250 260432904 260432917
    0x5010b0103140c07080903030d060e0a0608030316030f05070914040506130c09031703010513050907050114090306040c0806010501090e1302012a030206010504090804090207110603010f23010203 85
    0xa80f40000ba0a8040c4010b45099548014005058039607171944410620080c1110b03010340c956503103284000c299a01820f100c0e00e800c031f42c0f0705d001540c1143c1d160480101c00c050141000c005060300d6200c02c0c114030b03a0701d1284034415050b54981c00d0b60b01d030410a2404104540c80400c2e40594541014005d00d555440140c00703585100880104420400641c2181c440d80103034001030507100086ca043c001d510444018506a450a0311000710b01c6042e09250401c0d61801d5503d420150010681071106502c00d4120000c40300c01000114039040d81000801c0ca081e40880301620103440e4024184146041400400c2c0101401d190880882d030900b6250003141102400d25800e051200314001e003164041c040042c1040d1a030740c808103507802d45010b1010741c0c0f031101e84100d006000e4540089501e02e02445114290380d04801c000d41080d06045005009601850055404480c2c0304038080e030325980c043c000c6000e07000c68083e141200d403601c101e111254050310340c2070581404548903001c1503640041910708 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 260435404 1250 260434154 260434171
    0x1150b0304110607080a020a051504030c030f020f03040b09190e0a05101203021005010608130f051c020319030b0609040902132c0303010515030a020903010c080405010b010314 77
    0x240710780c03000d00095440c8134440c00100303408004600000c0305900850000d00c480d0242c401c0d6402032031850403240d07030080e08139070050118503405071500100c0d100e240340121810141c0100c0d00307070000849450345540c115a001c0901c0000c001210700e194100362500c0003d000b02041803904090520425000d0003c00914441e2034039601d600080c203452142080d20001c1800801c0c1400321429414000d40b12841c1c3c4203a0a00103091900005589100d01e0720244a04162200021040816650170482c1cac0300300c0c501550716124100c510300c0900c0e0001b07400356040701c4c10b0f0025540e40f0510900307581904406000f007000d144c60302c8001a071139240c6008580000108a8000945008600c006030034888610309070102d03649001c882e040c50440e4114010b0500c0d02006185115001040707802351350348424010709400c07841c80d0070190f60700d000b10340145030410400e940160030030f110480400e0841f445d88402a0003c0c0040050105110003841080300032030b420710f8144440030785000340192581000c1c1070140c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 260436654 1250 260435404 260435423
    0x3150705120a09080f07030e0f01021f0e060f09160503120a180e0901062408061c050105010e01050102031306260a0212131505060a17010e01150b0304 66
    0x200c40751003030f40c0b14500c2070f40c1c801000307503c1e1102d002100145030000c40c1c0403000b003005904029020f01e06882d400d07040c000141e0052400b08004d03c01da000c103400342030020781d116459070914840c00b0024000c0501c106001040038401d40f500ca07040c24940049404142d81d10030f00349100344001d403000700d94241082d1616507401e030784041028040710407044480448050100f01030022601c0442076018034080e002441c0244581910b540c4042d06030800040c01d00c042d0501e9a81c0c4021550183c040d03030760b00c0030700100104900c601d4614006418554840d0407203032650344400600c040300d080c010385405840d007032008504120181d051802c11031342a008203c1444070341c80442c544003011a000303010100c900c5c000810b1074140002072030040c0d04810701c04915040581c0010303503600000310203d180b02e41c00032107641e00c40005141e00c1005010241081e41c10451306c04c4007040150001031000c00050556000060068002c1201c60031507942c400540130542038031004111041008050341d41094209841c01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 260437904 1250 260436654 260436661
    0x4150f050c0609063304111c051006030902030316150e0f01060803120f06010201021603020604030201050705090a1e0f030305040614040e0a051302090112020315070512 74
    0x10340d41801081c03107450280c4038441c1040011003012840e14040c03249002c01210204030b14100d80030741c414440021403855842c007400d00789880d25400c00c402e070a660480c2c2c145007100d03600c01d00044840c0340749800e0030316803241d0900c4441e8400c00040002050301b4a010000546a41d00280e228444c2500c50007144005041c0320082c03000d0364132031402140c20b20800304040d100d031204854494104258806107135282c00d800080c0f4640100c01c98080080019140340c1c0c2c3d60743d683c04c1d03401c900400b4000d2811503500340400005550140b07001c0d80807602940052100d0b10345450000e0940b02c006000908100c0103201112807130700c481032000141e031302c070712105000800007242981c11583d5a511603441c41203900400024507070418010410761710956104a44100610300b408003c0c0b141d03200e4405030065081c0080c0c14031b0400c1d801181c05c0320840100c3c1c0341050300c03500020140da4003a000b58011313100c81c805107030031881c041022a2142070104851482440e203200d010b00700c0d00411007101440c0f40480d002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 260439154 1250 260437904 260437907
    0x610110709051906140a0618081203060f012a060e121c0e0c040203040f020a0b0301080706030b0307030f02150a031409162c040f0203011104150f 64
    0x50000341ca60100200500d1500806044000001c0e0100c0110240707000b8000c2403411180c00c6900d40d58a010303040c082c0991818004075210316490035a003842058200c0d000c0382000d400e00c408140f08241090300398803401c1240801040c0e94200a43c641070100610842a02c0311043c04000b660300703290200c4c1d40d448005410110050441100301c61540d026604c101d52240c03004038054106840c42c900804407039030303485842e40101c5070300b41c02c4078482da0f0007254924101c3c6801d80056034064451018030718100000c1e80820101c02554020030150034001c8018044505c00b0004a0020082446c0500011241b0400710791203121038080030f400c808080000a056446080c90342c40e1851180140c1d554581c40e4a40080040c09408182c000740000da03c003007010300d00300241482e10b60008880c460070b03d900e042102c840c03000ca008400001810003500050b10118604041d51095000341204041030140744109400c55a90ba44181c3c0034080a004c1400b081a10304c880402c8424035091816107035012200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 260440404 1250 260439154 260439163
    0xe010e1e03040e1e090f03030c13091d0c03010b0616060204050d03050d0b01080f0f1b0c030405030106050913060506040f0603030e01020607031109010c08070632061011 74
    0x407002501c80d141050100c000e82110803207072042100c010302413040e1510b60506071140c07040442e0103c142d00900100c0c3c9036500250081c000d8649507941008110307070350a10364060351126281000c8890450b02e2241d080c02d414070500a080070200c00820401108900150146c0070f1340d241c07080030718551584003041042c180d04480c080e0900030b010324203500044c58010416800707480d24503e840d050100c5407180754003840351280200c024013114031455407424040f641880000700041044213458217076841072504240185404003800010b96611b50500041c903003501c09640c8154090307004002003051403151031a514482640c0300710b000c1040d4480500040151020f013407280c034000d10b400c1001042540000021805100a07025103215580f1403000b6401c45d030407541e02050407182001900450342c45940c040610a105214041c24855240c40d242c04450310482544900c035212600001e020403039046119440ca00c040e0b40307002d945410004103512030b5078860761506100d105a07001c8002d19042c807 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 260441654 1250 260440404 260440409
    0x120702040e031204051c0f11121603090f141009031505061e0f010c080d0203070302130f031104090f05010c0207140909060103031b0c060309060e010e1e0304 69
    0x80803a61902852400c81c2c05003070080e94100c0c5ca612580c004c0d060300e03020510200c110781c6055200c004240d5064401544c1c0381c0d40304e0762510440d00401d11030102d0046424050840040801c14a182c0d19506180240c02040580c105091107016680b0070014080740c201e682c0000c010a41d80e1034103108565005030744a0301541c1000f0700d84166480c01d1b99035085158041c900c00e6004480840310502900309209031150110b40e402d40001d09281c01c14000e50080041340c98484c8105242490100c040c10000c0032604191034160000c1c0e0001011807200c3c03114500c16016040110b2500b400380e1a41e5070b0001030a040d042e0180c00380e074403a07a10105206810000c540700a80120080c00600d48064000b0f40303880c15030007200c644139840c050341c1c0c0c400c3c01c00c0300706a03104014100040c03100340d0858a0580b4492000c1e2840c0d00103150840d400e42c000740d402800140101000d031000f260485040c5020780070b4500e5003c020070b841e0b240c40c4404070b02100c00580c1c41402051011400e044044000c80135003548280d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 260442904 1250 260441654 260441681
    0x130f140a0305090f01030b0109030b0c070b1006031b1e0306030609120801060c110d080705030a080105090711060f090705120601050a0801022a0c040501080c0301050903030912070204 80
    0xc028003801c0c103411500804402d81c04403250040d08000d84015002c03201c030ba0500e10b001944011003030000455949603a070f0000c0107a1303a0b440c01c002c616a20324810000031140e224441e11102020049240c060045581c1c000c1058036640c00e01007030032f000410901e03140902c0d81c2c1e0070001a42602465000f0340c001c00c05550008014403d848a0341040b02c4424010941d600c0041c01d40000090000c0c810700e100038009a200302600c1d00b1406c454200254081a0300e4156041042081050001601003005004c880895118030f1000c2d89443e00b00a80510300424500c1445100e65540c082808003060a1fa44020104141841501d03000e0500340b8106058010b9500503044110030f648034500080c0050480b00e088410024842d1a68201b85c240e008021115040f07010001c0f1810810600b44800d00c00b006510742192550010140010182c1d0002c1c0c0c083c800c19000b010f00d0120509082c0a290b600421800c011459800d01d0600c10769140c0d110190b980140c0008240841159103507044458100e669 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 260444154 1250 260442904 260442913
    0x1e06010602060c0f1806041d15030a06020310051801030c0e07090303080405070312050912120a1223091c0206010611010f050a0203012c0105010c020d020a0803030601020c0306130f14 80
    0x120f030000d0088840041464000f02c80c0313500003801c9c00f481070501001005002d406881d00f00100d603510310207904080d081d0904500c442030003051940314100c112151040042c6900003951450810a0740c01d4910b400030030129030b0300c10400c58031980060142c01100d0b0700d85003a0500703544a0600038242002500000c2600c0040110a04002d40c004003500700e2050460320406545041000c1c1035540c90660402641c01c201440107110b41d9005896510101c00300110201c0e01211070b180c84070583e2454550528500c1c203940c14003240200407c18407003502049444115619200e40020b5611030052203100d0800648903414200070b6020b4014004900310030710248000d04003016640040c0d00240210040900d00da8208408404800c40e20f0084800ba01d15002e142e90800e00111440381200000341c2e04203070050620001611141414001020400d02640e200e04081c000203080c0143d842032184a5804170051104c06a034403030014111662107440c80221a072103103040d680caa606240b001d82940034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 260445404 1250 260444154 260444159
    0xc010b04051503070506040509010b031f08061e0421030b1806011103120a0b0406080a0c06140702130e150c03010608010906080a1407081e06010602060c0f180604 71
    0x26440c102142c003141074481031520b410600c0810b0089100d00c641c4107007001c004001060b119402540c04c4418401591200000d105000c1c44d07075510307907100c00702c40c0c1d1047e0100b144200d0000f02410103e010f000429080f801c051321404048401000e84244901247d5200505c0900030360000c2640c12010300074121f112103600010b80500030131155980422840300c0b1490f49480d0100880d9540884004c2c11400c41e100c0150701d400809400d13402c0c0740c02079681c0e200458140802c021488086108480440f415418520b0082020007825910109000103100c4400140d66019454824800f000e1000074031185141055280211901c00503034660044c20a000034510303200002c5060b180c1644036403459980e80c100718411074a0611952910b50000d08004000072010290b0390320180100d802c4810382034440307801d1414510807541e490071a5403034102d00380075480c051090600402160002c0e04080c41d19405000701482281510604960001194007101400f17a509032240c90002c3c11b46510381e038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 260446654 1250 260445404 260445421
    0x3010f18060605030a08031303020a0609060c030c05130302130b1807030e070303200a06020a02011505090f010501051c090f1a060303040620010e011b050708030103080c010b0405 78
    0x85010429076032582802c0000c203c50900003180d41074507601501003855a0f0fa515030380c1c00d0a2503d9041181103000d0303920031401213502c07070040b1740800340540d00000d0740c001584400b50499860380040d009014041c0043c0d420300791014107000840e60103403070381d00c030341c200d4480800010680c001d040c2d03a100b41c0020401110881402d9068442c9405d07842c00c1020b58188071b101c6036160918440200024007000c0d1180d90000e44400c2e000f404c0c1342c6042100c2280d11280e441401340d0b040240640010303035440452000d64544000081e004040685002d440703800d14000e4240e905605005290502a00084103416503050005641d0940011501002124200d150102e80100185e0040e1400810340010b209011108507140e4020040203004626261816405036003803100c196a203a5070103c82519a1005003007801261800e04440300001200680742110303010860212402c2810000244078110004400808503410349800801980d205c010f0300301ca4501520104100540241c00d0000344411403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 260447904 1250 260446654 260446691
    0xa031512050c0102070e01030c0605070219032103050c19020f030a0207091d06041b0306090803040302071512091e060509010b060c15070309080f2205060d050603010f 73
    0x158400d83c01e441c000344da152510641b09500b0300014280310190501000a240203400801a42e1b1010303116814000000400b007030681d501e548181e5001c0d07501e03010100c1d4624200b008a58241050a08000074141034990300818010200000c1040300a00d400381c200ea8000c0103100c18803450001103a55502d005038000f52141e10f24402d490720b00d030422000c211040501c810454480c41d001008188590b11902c41039124400b04c1c009a80b00f5080c1c00707010011842c0c0f4000c051001c0d000c0c0092640c0c07801c03e454000e01e801030503030000d55428240007070b10007e658401c2000782040c00640b0f01003100c0800b0705180c3c095000d102840c003d06015800e15030100500c1d41c11107031260500900170407100c0001c0b8140700c264404c1c2c50030b952054010040700c1d82c85c00c015400d1107800c440c507840d0000f0041c6095640d182c0b5680850400300441c0008194642c180307042402030105e50407500c0102010925000c04070b41c00d0700860040c04c1d109915100010003e40b001d5000075181171036a5814412004040803c1c10703038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 260449154 1250 260447904 260447923
    0x3060c0c06010f0e16090504020708030f0a0203132406150207050105180103111201060203030f011a0d020a111b01030509010501030209041b09020d2a050a03151205 72
    0xc0c0c0128030002444048a0703000d4821120306140008075580c3d0b00c001441c0781414030f00d80d00203000c203001001c0380d5a12544098001c40d4456118a0b40c1c900f0300c948c000c081c54000614001d5418010410464003c84079146103000d590301400e40262130240c1d00280304c10300d8008040c0d441070b40c54100000748148140100c0c05808446409590742d0f941c9034001100d02e0701c113061803420900c0390b0b800b8506281d4440d9004501e450010000603041241d140003140d8010001e9124200603030011082c0111030920703641080c01003802c1a642504d514110361a501d803801210800040c02d41d021078102512400307170100340f403030306003902c1542d0007680000d506040c0c0c81c080054590001f841c180001d5900501441154140e036001401040c0c19915581c034020300245c1402d168010303c94404c00003030f6145031070014100885a505010030f0321068041b4001c0317880d101c2420b502108200030403105c10146c101c03040703401401341c2d49000300e100c88a81c140344103240340c41ea00468020342c07a601040217001002c10480b42c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 260450404 1250 260449154 260449177
    0x4050109062903010606270305010c0302090114070c0e04030e04050412230304020d1a010e0103020411070201120b040e06040f030f0c0309060e04180b01030506010501110c041a03060c 80
    0x10b4004840b002e240c02c9500c60300a00700480c0c0740c0004d0902010303614031084110140242c0e4070b030303c803a165500c2600b0b5070b4400e843c0201180c0c010030704241c80c0da00701410603004c0c110401d08906215198803040d40404152203031000500312440494107051003091400e040e00c402900a0089043c10314004983c448917600703800c0020f611082c160b507101d114940c102079000e10a103a00341140c1781ca4080000ba051b021000b2603845800c0300b40310000c043d80e84d98590003040109940310349503141d40103010a0b1194503004585010f0204000380040c0e0f0803c8046501001000700050301c03c1c0c00501260040054049a94451240000b04030402071414080324074240301c1e54031035084e08030031a0207450156021000034085400c07403038103010346442042001c054140080c40494845103c00703040900d40442041595121a640c00600510800300f0150b0300500c0e080c60303d400720305003200c81c180d19106400000351103a03444540ca0340344481c1948190f001c0201c01400d88480e420138280403d95a40b00d880c0c2e411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 260451654 1250 260450404 260450471
    0x5101106060d0c1e031502130e0a2301180501080307150605120102070c0602060105010f0c03030b0904050c01030b030309010c02040518010213091104050105070b1801020a0509040605091302090405010906 89
    0x700351039107d000350b550440c01e80b20480140d0b800c01c50840c0074010024007201c0200d50381e2519094105035400e80d00031000c02810811125410040d00c100c2548640c8481e42d540741c00d18004002081d00041120220768106040302e03003078411007164802a252503407100d40e0281400130001c07240003040d030050180e184211940b40c4865590541640c40389400d1060300d0206420381c04034031300140100d0350408044c2c0720341b40000e00e066030755001650f010815107058445500c005858056540c061103103400c21030301140118207045020000904090502070000e0180351102d0106040a90002c0b841040f02d4401d4003d544a0440044002c111100c0d403180075086130502004600802c100811541601d00684d1110701e0051581c684081002019000803d400c014500350014003030203101400d0354419a07558940e80d19025010001030717a800e5046903205104100a01c101c4544400903086a6903055881c50b6142d80c581c200b00d401088a450054081d904240b03007030302d42c05c4100c641428039210144803c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 260452904 1250 260451654 260451683
    0x60311120703150605190308030403050d0b0301051512072105010b0418170c0c06071103070306021803010203090d110a06020f04061209030e041802060c0705101106060d0c1e03 77
    0x400300486d00d01c000341c03000e41f0030804a030101e485440106266404580c1c0407512208241c046421990111550020f44e0503d20400d01c042c43d2a44580074440c052100520307919003048021106000f0400d034540c001075a00310b44400b00700b030079000b41d000100000c200300400003510340b0310340008501c607204540f900780360304000c120041c0803003e0b9100303040a58020441150a402400780a500c422425030395814040d1203842940d400700502d4001d503100f041c015071141070048005c0c2c440442c004c25103200342d0050041000d0850006104649900280751055441c41069011070601d811603601800590001491540940100c0d009104640565503001560031b081a4010304680226000500044034022a240c1510301a00301c0300b6840481445002da200d16070b03000644542c804501e610454002007404c010301d141c41c221101d01900c450815a82140d503211642307486140090000b4402c8560711185001d1108203289800a00000381d19003010740a242500c0d180c3c00041d1004444442c00ba00d0700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 260454154 1250 260452904 260452939
    0x13030515010e071409030a0f050f070302011e3f0c120b2805031209062b060305030c0d1110020903010e0114040c050103060311120703150605 62
    0x50340e0407218410840d03081500d81c0d100c00c0710307001007000640150034010b10401686650a01001c0f04140c8941304460741040d00d441d0107814440d2843c1e03620a40c0d000b1031340030800741c0d8201d40310a5905030300c00308955031941d4154040e00c280141c084111030180f2502500c7d94003423a034121001992000200512190700c603500d0388001d65450710710500009400300000d02c004000c64101000100d4001d1203201c000725290000c40764144980f54500c00740d0704c1c540742049542024000c0c13011840d40c12101c540340c180200c0206401e0720440303990862690200c031005a03d203802501100802c40c8506061046d1507903410190b03540d41000c03d010320640960b101c100061400340001c00060b031000c4014280e0307401001d0820000350020030640f03806540310b08075912101d40c02cac0b19009001010090b202d0407800c0c18203102c4c820315002e03040035060502d0300b0028008521503034449241c11000f1600400b0072040f61410f00d081240f5070b40001c201c0b80c003004101c00c0c05070b000d1b04160142d48003514404e001c2e0615008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 260455404 1250 260454154 260454193
    0x13061109060d021c020a03020409050f06010c0201080703060e0c190e1315051c1a0c070b071e020c01030c2a0c03050a0b071e091401020f0102130305 65
    0x510310381c0a04100056510107000381c001d8500c59004100012801c160a0000c105030b038458450300000070303800141480707518814071500d6048294840c40301c030b440c5000030002e00441c80e2148003a060103800400194035921940120020b01a25241c598035420802107501040d0055115001500850070941600c0c9204900e030250b546002040000d10040d8034107900c00420402e10042c2d011680d0200200310b580b0351208142d103c4c0780300d92905010340c4003410101c071604002242c80504076142410302556442c0e81041c0d405850300700d5601c20b01074594200548901c080085031044030000c10b800180c060303401154190f07010401b070300d042c032100c0c1018a0403501e5403542e0825420304050700343d00c00a4040e4005824001503c6112805001c3d82c80303864451800450340300464202d003105080004881e440810b20600600032000a6917a01502802910000990150488070300c44200809500c2e031003003003130512519008000715601c040700e5041d01d50303031200b40c0401d50390340c8951300c01240342280146 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 260456654 1250 260455404 260455417
    0x30d0207120807020c1809151509011509030204050a0b030a05060121020a030b07020f030d020306040b0405060d060504081c05011715012706061805041109060904090605130611 77
    0x1071142000a00710180d018201b03002529598092041031080c50f41c2040c02c1c0c3c02c00c0e010306109078a80c1424403003039080150f1807005800c503113400d4194100e00384241d40c102c824036040d0307a030403140450f150340c5440d504c3c001014005407103580740c490710940d41d0a02101096440c182c594441090321020303038102000c0c420380d1007024020340100f1110f608201080a060810303411004a01c107403509480c1001045145400c840c004c0154581e0000c280041c500e428891000150b4040d5003e00c0b09190481c00100340d804510009000d01f80c55500090410480004490102c0074200003c44269081c4c0212401000240503120340302c0394261030706061038000600008052410701d04585c1c26030803c0611544114106401014540c1824019626012501480000c1d02c1c4c41c0d0f0b2050499080c4080001d032207182c90340704a0240f4680000215500c0b1180211104050248d4006903107503030283c08907004180c40600508440c1c40c00d801e02c40b48032400c041c8488100c5c0114401e029486500b00a00540d20901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 260457904 1250 260456654 260456659
    0x150307080a02010e0a0f0303121415012609101406090610020321061306030b1b1c0507080a0b0109063b0a0f0e07030e030d0207120807020c 61
    0xc01441d006611550982514020203072408041a81ea10b03200385405030340390401c8001c0b402d5a644281480d0b802d1051f0710302d00490300008426070411240b42c1c8032010040200d2070400440b03d981d440c91000c20852142402d034060f04030b0030a85061190706448080d034041000c2e60030f041245099055514038901c50082c80002c1201025441e0300e420004003011007584030741540803d012201e210202403039a0120032540e01031160ba1840c00e0400c01152464110f07400010302d14110b01480498112268907a00650803e406105000d1000c551101401101c0da00c140d03404855039001b0031510030742c109034010707000d0340c40c2c1a12549980c4a150290f80c41600a00c1c004ac140000800201e88035010040c184241000141358006900c46514040b041e0180250801084940c003030178582070812601e8010035484001c024602d08080341c09404690190080d4201a2506141e15440c2c80520807944500d1103042c04641d6240140381664000c403d551614020070220000980c440e800800c0603550740303200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 260459154 1250 260457904 260457913
    0x1060506040e06060309120c07051f08040809152706030405030304030c140d020d080901020c060604020f190201060e250305100807061e0e0306070c110405040b15030708 74
    0x3d010a000340303500010004800d0303202e0450013503114421400241482000c040141c100c4c2410300080c4030f2001303450b0720200d03003400c04c04c08051001d9500c4908150000d03801800a9a1803010000003030001e03074a4180c10032540d50004030443d06207034003100c4030960398018600d920101c402004101e0f0340e000c00c8130b01600c10f410800004002910a8842090480c40b82c0c891841c0311480b00b1440d840c200e101c18071107015030721175840d620603d500100040d42c06242640258a407010207603240b500d4203405040d1f20b000b03c3e008207005442c0c1c441031017a10072070100710364581c9002c048080c000f4081c008900c202003118070440046403d0300d010750f1040200110210f06e03c80504034910044008250040144204441c401d01c0440e0344402401048020542c40c3e5400b0030150030000490008981104a2000e104508502400300e450110700301d54081c1c01400e04031588002c0b4200050a84101081c495000740b40200300810012440c402c1c90007402c100301082ca50100345003d05640b1601c9009400d0160700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 260460404 1250 260459154 260459161
    0x2040602100e01060f080102070302071a0909040206070b0903030109051012020d03031e0c080c0c0d050d0f0204090504050c010201050130020402030f16090e0f0916030302030c01060506040e 83
    0x1229008400200002c10000441a03501c81c0750480c80490394104062a94001132076030145a41000058042d00500e9440110f003801c80c101400c1038810130a0307560191204000103002c0d0350311181910f6000c0d0304410110103500e4034100b02c0751640d2090180c21401840e10713010519803510300303283c48141d40e180804900401116020001c405044800841c20142c640ca0b80d14031408041721050103a612f800c4004c9088a600700bc00b41124000600807000c0f40c0b0280941d804000c000250050092101d06000356105600e085600180041d8200f81c0c0b400da00000300040d40700030980c01903201d1801002510a4860f50781c00490a070703102803041d44100d287c00c4201d5940e8200c4500d00146e00114022401ca00b03008a0b400303c2d06980045031a4280c440000041001e44400040c40c03104d60381c41464413804984c10844680404000508001d050544042c0001d8002d1010445140880c482c00030901095a403864002d650b035210f400740000715424494001050705080d801d843c240d401100d03c20f44140e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 260461654 1250 260460404 260460433
    0x30304090f020d06180609020708041a120f07141908070201090204050f0f01150507030c020d02030115030302120a0903020618150711011115090c28060302040602 71
    0x20740c00c014030100c07a400c010300401d0b0b01162207654000c0c0340d41d50007407000302180105003003150000d5000080c1580100300440008030034008540c00e90300c1d8040c0c03180c2c01040d035441070709203401401046c1c901194103174148640d034031517064814400d0b1560380d0b4001c070554200112044e140900608002007009040c514070354235000320811075003d00c0707500c000254114141c000900f41c9c0c405a401d008140001c2041c4099100100c08031030242450240070390301d200e40304000502c94460720002404000310240c00c1000c6548200010303c210380c005000b880f802d0a40342c8075000302401c6200803000343c0300d8a448030010780740c8803043ea800400310b519054411859502480b0700e40c0e020031303054103182000101019050340c1399000c1550f07031561101c0e02da803101c4062404d03072811500200018184000140f503480c1601000454a003441c03040345030700c81c2d152240717144c2a242c10070317401041e5401280e0f188503020006400c420511200300004052040a80d9031034141d04a118500440700103070001c00b1046500c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 260462904 1250 260461654 260461661
    0x90706030e03092412011401030b03031e070f0b060405090f0703140f0f1c020304050d0f05010605060a0c021e03191e03270509130206120f090d08040203030409 70
    0x844901c0007000011107104a0819503000303991a4110f440b029005014002e900d0215191f0041c00b030a042006100203000a541ca008507401101880100844680c0e480242410707100c0c1c0550105403040410380c14030345208127030710440300da0380150301d403c00281445400182c051500401c2c400640b804600715180c40e011200f031100319012500c500c0c1c8013800300398420815080000c4102c400b43c80c00d907000d503003500d5030032184811303010855006220a22050392400d0a1021080c4d001d00c03504c100d800303245001405086241d111603401040455521096500004016400c038800c0b500180e034035698501c00b011111090143d145c00d540503060410348480401d403009409030040306441103055404544103420f9200190840000304076000e00700030710b402301c945200310401c030362440c205c803506080100b43c0800340201603400491000e031008041d034a8600032901008c0c6217104c0d0034401e06d010508400401d9007541c90090b43d00c03958210b5140d07a072103019124012035004010b145043e14121505024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 260464154 1250 260462904 260462929
    0x160f090b0d14010509190302060c16060f1e0501031e230a020405010e1515040305070e0f0705031b0702150a03050703051f0b030c040f0806090706030e0309 68
    0x1c1801c256581010954081141484400e000001320350342c5003a01c031190601024100841c0e4860320a040900040d40200c0c0b21680140070850058940812034020304010b224000c000d0205441d000851182c21001c0e04034220b42c2800d101c940c00315050b4240c891080300e10910010b0155003c40c0c41e08030101180c8904c240c015400b40303a42c0800d46100481c2049240b00000c1d81203040ea10a00141d02141483c0c0102c0307004022510840166107000400328985010203c28284a820a80c0c002e6030b4150724541600c0c00b954100f401c0340e112a84071000700159000c00e4610200c00333a5403070001083d051182c0100d0717110340b107007842a20481f0256200c800704c0b1780162608a0380318600380c01041e0f10300c030f9400150006454503540810181090b904c05811144050544003800c07130b0080d4010729a140d201c03000c80480da50782e400c40d0303034941e80c0103031005450103503800410030704040b0000040d840c140045d5207030003101060281d07400503a0311041901111300141c200d180e140c105000ba07a90a00d01200240038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 260465404 1250 260464154 260464159
    0x60906170c07020604241d0904020102100612060609091e30080601080112080f0d240806070c020409140d0504090608030301030b0f1f17160f090b 64
    0x200b00c1d5030b60005096030010340040c202c0e00e10a540d029200141560020242c495134180300c80741c0c3d00340c2d10b8080e0302c119060035250302400c108004034085910030810648841103201042000d6a250080346d4045c030403400080d6480c034207001000c5446942c41c411858125070103180003840c2240d43c42c280c0740d000c8540c03905036500c5142c8031540075009580400640d00e80807020087c03d42d10b101c104c0140c0000c001501d401d0401c014a0010b120f640702442c1d00185883e000b4103600d03280d84561000d81c400384618503440207000e041c01086009850445190712030348080005040b0107d8580d4002580c40c4030072600800000c0400398000054205036008002040c0690302290800264490281c034141c5541c10010008500041c1082240490301c0b60b1000f43c100c40001e1850b55141d41c6900c946010041c4c1070700c0c0b04549100218440b00c0441d00040038040503010b800000541d286850784001715040603022603401012242c81c1d011040041081c00c0d03815280b1481e11183c00c01e47c090b4010210724140f1078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 260466654 1250 260465404 260465407
    0x81c03020d09030509180f060409050a0210020607080108011e0b01030b09010b09040c020703050307080c2b270303110717010603030e15030f13060509070f060906170c 73
    0xc409541400307a0001c25003e0b4541c20390f00c0b000743e0300b44002c0f1000c403000310040249000174892421441015103420140844000c01e214855082c03440c100140d68100a5005131440c007244c50300c1c0e07000b140072803041000d80c07a0680c0e680e13a1017035234600340c031503412607001460500e498980d101185076103d1040d081040c580014448208001b00b41498000e800000001102007108130441c82c190099200300d500780d2019211143c59903031001e41d6805042401001040007088280400304200b0481c42200c00c0d02c108401e1003e42d0708089c01800c0000c075541030004500d106043c1441c040c500c0d401d514880f500015410380e07403a6403000c41c0c8a5005074411000c6004100000903c0c114001160750745403c4140002010351440c80e01810303111420316507900640c296152900042070b2001900e5026030544141f0b81c460b43c50b00000b040c4440c289800404d510704d00814000c55040c001803070001c1d5201780902c68060380d1645030560f4015100c1c458007001035a01162030344400410540241c0059418940e203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 260467904 1250 260466654 260466667
    0x50d082502010f150b030c300a061221030e0109050c0306060f011b030c06050c03152d0307080f031908010e06010815030607030902130204081c0302 65
    0x120301aa40c0000100c0140e45a03100310614500900c0f58110440010300c00c0c2000f2880c00301c40351018040180200380c00580072903e03c0202056141c400a02c200141c501304403008406075071101400d007074405100c1185402e00c0401c000451803c0020f401e9003188003038091504050000d8882d140131240a000c0645030300742a0710001003401785003e841d101d60082e0920380342ca81d0525103801c10041c40d4510502c400c5546c442140d800c4004071800a1604034440005862800c040c0e6020001302801444c113442c0408015461441d5405180619403140f4a082000f09001c02c01600e448803c48000f0381a1566040641c10007000741040102a0f0203025600d2080e07903100c0a07803d140503070300685d2081d040002e0000100718011106540440241807250140d4101440b00d003090400600c44e42c140304d0620301083c80c48281034100402040002c085074814504014010003601c2c20503801c0340a9201e40e8030747d0801040c2802500c00b6240e0b80f00060081031755500188400001e581084020300d5400c00c0710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 260469154 1250 260467904 260467951
    0x90b0103060317071505071e110a030905091323010e03070602040303080a06080312040228061704150513120e010801080a020a0501030b040e0f150f04050d08 69
    0x4828800d0f1000d500307192500c11500b00800d8030301012402c3c0000515000410a055070403c06001d8000350349400c03041106104001594a03c2c1c040c6a540d0709441003510001c00c00d0707840264503040e0f07041030710010259210b00c5509020400034240040018203001c43c2d6240e07903034040300c803200340e07052050001c1200c02c04040014150341c03080000740c4aa640008003442495001080503402c442c000c4410002685085280c40d101e001d403800e1125a4544000802c0a6580308041009010610b80c40841d0480305c5c08108807003402e80348958400718583c800c02440c0c03030003c01289440380340c028035080104400c803000c00009100041091050700c0c5540e48000c003060a01181d07460021103034031012202041c0d8000980b4550059100103055440600c3c03820050321003403011001c941081c2000320b0003145a000180c007a080c080d104c00c116125080e604604060b000481300f0744c400750802d941c0259144c6140904215000b203d02920950210313107101d20040c80f5a2007141e0145c0c4681c103107450281c01e0702e003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 260470404 1250 260469154 260469173
    0x140312030603010b1e01020124031502091309060606051e0c0a0b0709091404050a030e01031107050c13020717071505091509030406020709050903070203011404060501050f0a090b01030603 82
    0x1042d85c00b60b1030303064010085503024810242030080c007030010789066455050b00c0144800500005080c1c000d10300411816440c2901a82e115000c01441080000030801071440141009042910403038280344c03000400d98000e800f1115507164829076100e81d50f100c1e1030964042c1d40401000ca80c6841808d01c9507010503d01c19407640107200541c0c80d00652454030362407500342c0302030074082201c0354000c205000000d02d0004143d400c19038541414207c141c03038000164014408140003105000000503140100716001c1943c0c1d0121104684241d1340707800c03240400c4100e004202008008a000ca40080310282c8400c000e030030203510807070116075084904c54200c410f40b0410744540105500c0142d00d603071501c451007141d69000d40807030000d604051420000942c1d91350144680078034079030b803080407840104003442280c28458001c0c000b030111600c2451030b0f803250320b42140d09460780d516100010a0600c0e00180c4c859030b01000408040c0e009040c10302c0040241401c4a0080c14142d54290010010380a031a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 260471654 1250 260470404 260470429
    0xc030c05190312110f0d0c020c03060112052a01050d0609021611030d0e041d01020304030f1d0105030106080601110111041404060f0b0f0c070806010f140312030603010b 74
    0x2a5604540308100343c00742d00755001c81d07001a11300e0f00240103110f904a14031080e0f5510b0518207402003a0190092001d03030401c0e440b03070030254240c0100030003c100c3ca0249501d0028581c80307103084444c0340c0c1c0001f0180c80c40e01c00c004002d0044000031001e041096208038085c01e90300008000024a4690321807505040360300101b40e051084108008200600400c5820244881d030240d01402c40d11507078183c01409519030380001c0c0c0c820781d694404030255a0507501d266040010041c002c46d40c900306428082c15440034000c910000036240c5148289180a455000303040d048103031165811a420101c060721141c2005240d50304001da18426440d240109000e01c0d241121914481c5540b203041162482684074001ea09038055801c2150401c8640c1d008401e400c1110300d900002522210300748400d8246115401c1403004034441e02c01c01003800c0c9000b14505040710407009161024558800710b140c81c0c00030309400540d043e00051380e10186961408000c650154008000150344030460000501c80c85114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 260472904 1250 260471654 260471657
    0x50901090c06020102120a0f06030b0a140603150103030f0509030d0801050f15040b030408090a030c081515040504080915070204271707020d030f090b0a0c030c051903 73
    0x40040e002031001e05039001d40548820310007549088000b81d286500000c0c05080314000e6075a8460070b420100071948040c02450b40312040607038a040038180b00001d05440c0d0042240400c4010200c3c00910700021100311402c204a90303001103a195860540c0c0c0e80c4c23009500e4600b4000304000b5211030340d03011301009811000c3c9846407442e5505000034845021050f1884030f008a8103038241a00d407841c07040070360301240c030a46452542c90381c440c0b1780106140690300d005a00000002c501004009001540906403031100c004c941c081c0c0300624000e24444d100380c4582403036040000124103e0b05080e08010360150180842914045500000c20b0841001520508002c030000c00c1c4e803000c500d0240513500d4109214040041c41300201200880e00b00101d40008080b003c01140b100c00045206081d100e24903001040580350071100c0c01e014141500341021100068810b02000c541100400c00342d81c010560f584d03c0b90f10520301a5415500890198010380e41340c07003068801d1298800304215151600c2c0319 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 260474154 1250 260472904 260472911
    0x100e0103330f080a0b04020f06040e09010b04050601050d1d0601061d03010b0603160309050303010b04410103020d020c03040302100f050f09040219050a0905040b240d050901 76
    0xc1808010001100d40c100b006400c1800e007080100d020000342568a1a800001c0c1c011180c95610000e814458007120240d04800081000100b94074032194651156000e000280103400a41e41000200d40c4202c4070b407804140e003404a80f1800c0e6060b0310001ea810142011100324800301c2c1c0203245003050990018000640070600544400c40b100382c410001c2d401a40244501340040e0300041c6c1d1750200400d11005112111410320146200e0f80092415a8101040e25a00c1d40c44c1c10030744403140e101d40160900005001401c0c8840071034128081a00fa4803416141d200343c114601b281540302c840408181015028041007124010074402482104940703c0219503d920f0740c4140080305521002945c140003045403401d5540f80c000080396804200810a56a2040700b070300020b00a01400c040c070401c80603820041058143c02070b00611a14201d902c1f00440a5503500401040c0c0f110b014600da080f000c60500c446210050313040702c0c000040c01c010359500740030081255400721a402c540a0a00303a44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 260475404 1250 260474154 260474231
    0x9120607030b06070c06030b060f040b131e1a07020315090f1b06090d0803041b05061305060306030109050d020a02013b0301060b04180507090302100e0103 68
    0x105841610142c14007501d6040c28400c0c5034a4840103001107103d124141911038040d95000c4e651602291000c0c5004807009480d035440d01481000c940080f41a014086251040031030514115211000f01d403040804840001d42010303c00361307074415130b0868094003002c144890001a0f40501c2001c20806000511040600c4c2a003c010310340b00f01150b0781c0803070350000714290f0b052640800b0b81c50740c070300e0095980c503954102100c041071038070103104005042e411001c03080c00100122804962401224081c002c40c0b119100d1003000510320038582207440a80719440200450f0400d030001e141d00030b1008000050101c0e180e2a01403e082141c0c80c400c1c0148c1180d01e0f04011981c1010380c003000103d1000e01e000f1010460405007401680c00d48038180c907600d11940e0841240d45c00d40001010b0071002d522142c6440c0c1c0c802c411280ca01841400b5040c241c106070018600a00c51071180c0200c0b500200842016184000203440610032808064109910b0703207004d0310350700409182080304004d21000d1040c00c22 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 260476654 1250 260475404 260475407
    0x9130f0608150a050712090201020c0907120b03031303060911060a05040303020d170423030c011a040c1403041a04120e0103060b1902010b0d0804030b01060804021302030c09120607 79
    0x100003d200040b001e103000280301c2025844490985084001c3d8400600d228107400182e1800522040c0641d001d00ea10003005a0030341d0100c88521860349120040c00020200d404042e100c0c0a24051074245801e002810400700f002d5402840c10140500c00c18420410958042015644844c8001c5c0129000017010810954100b022012a40251500c07100d80d0010345041da080413000b0388050405aa190720b914815820820718843c04007100c401c595640fa0704154040c080d00c8900840010001c0900907501541010b004031920b4242030340e00e4800100302c086600b5040d030405002510f10310418040314400554400910740030358000c08201c0d40c50911541c00030a06001c40111034101802c0c41400c0181c28110016210000070340c00300c1010220b41807004900400b100000540e000110105000a201d4400020010340b8090544070b00140c0e240c00c0c0c259540da9050700e009411883c0f107001500300030050340c003545d00300b14005403a51a0042c5100000d0715250610000d4440d90004418411403d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 260477904 1250 260476654 260476693
    0x10020106030c0b07050d03020904180605060a080307080421140a1e0c0504112101090c02070602070504090317150307090c1403060a05120105010614030c09130f0608 72
    0x5001e1035909074513080565556a0b1038240d00310509040c5600440c031b906065556400204214807541407166600b003090800601a1909946090251a00c1c080201c1c20000101c1100c1c42c681d088184907140c9441c0c01c0d02410443c82c0700e10a0804852151811800130b885001808000c401d01c40c000c004001040c1010940440b000c0f00d132981c4c442940380104001111001b00504481c02214002003880c034206040362284103500400c01e0401142c0c4120003404a80e820160584550b503e0800003060074280c1aa50740f0a0b0340185809680140380800551809400100c0c8044c4645024108841c028514183d41c0b40207690072504140480420001030404015000040c4410041403102c1c0da405030000d4615402c018180056040010004000d6103a42070040300402003e840d40c60001c56400940c0d0080c007081c000c40d0001004013861900109414090780d0184600c0c0001034603022410003000308100f104820008040d4541c5041c408003501813203003034010058480034090340520402e00d206207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 260479154 1250 260477904 260477909
    0xa0e0115090302100f0e0409050601090b0307060804080306210c040b01031517030c1515040c05090d05012d05090115030212030c1606080601020c031002090105070210020106030c 78
    0x100700e00c1c0300e010400360b40c5010492100c0140780c10091301441341c2c4042200c04682418602e0b410509001c506010050b000031160b040302d0864008002450a0104164071244c69105401c00940d403031000c42c0c0442c54180003076800034030041c4120603200921034000010141501d002600e40c0040120701c1180c2071601a000b4900800d280c1008441e401080e43d40701c242c810f004103101c2c1500d200701140f144d4010400c49801190044c211450200e0752403181185c000c049074168803122004c2c01e802c0540c1050300803080c040103540c40d01c0b41800381d41000d209640344140ea00b5039a9640f10101404042c20307a403505a084000c0c2582190712440800b038100c1034480151400180781c0c0760421528054860030811800e0300d40c1100e1200d000c9200407002442c40c042c00c0220300c44c4d0f000b0388403043c040d6081108880e08840c42c90b181c550140c0c0d00e8200680c0c48a02c64901c1741d81540080c17551100440c8a5402000354000504100b414480746402103250041e0748000440540c2d0b5034002442032000c4400003000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 260480404 1250 260479154 260479157
    0x10121e02130b13060303080a20031017060405030406032309060703200a030207030210061d090316030f0201180b011403060421050403020d11010815060403020d110a0e0115 75
    0x84d02d8515600188000c100409613115241d480c240e9503442c0300401450000000d01c00106a10380c140201c4002494145129802460094107a429100000815614440d5402c14080c0d41400c0c0f030080180d0103000c0d0248900910711940c6164102e048610210030b000707000c01e200400143c41e0a031809000c480e4103d0b061100e400272480d5000c12009050111040022039180143c3c840c20b25242c160b20f0b0460b541040f4000500b4074401203a458a90030505a031268154004d4090380c0b545c2400d142c8134429888182d4a400f9584c45405c0400c1c000d80c00083c0b0350489100020b0940084d1104004bd00b0000504a0b0f480044000402c50b003e2401c0188000241c100c020701614181070b5989019000c09092803d11958200c0c20118541c0c0544266402541c000d48003d2a0b04d2152810b14014400c044846002ca0301500220303651b191095450083c866000d8489403a15042d82c003007040040f061581210505208840881c80d52a4418040001c00c2198080c8400303506141c40004c01c101042024070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 260481654 1250 260480404 260480411
    0x20c030a020306060f0103110406020a0606060e09060d08040503100b040606020d021911040903270b07020d0204020d0207080a0f050307093809040510121e02130b13 72
    0x4016940203e5219084a001c6810306403c210600040e0058800c0030464000780710f001c540011381940200303000041521a480400050b07071201c60036160401102c035555008004c0000080d12401d000c882c1c182194003642d403141c203290f42c0d180004e240c08a0703282042c0360540c43c0c20000c0f0b020b06290003040003400c0640064440c1402c06c0600035a500d1110104c4440c801c520a810424005107a584a50b4007901074018000361b06541070203084007500c1140b9142854450982e0006601c203001c007241030710002c003145441e00c0c1c036075020040004030211059074400d82c20882c0c4ac2408100744024401e2621840c405901c6056004c805000d5840c08054403040c41010000c10045580c8182084160796140210b40349044440c0c12130b0808801490b4500c40c0d45800c070456804040300c6a0181c00b101104440c2407205540740d00b402040700c0d0462007400c011000c802c1440c00040c1c1364a941c04183d090090b407182c0d00030700c0f43d000100d1000744009400c074807560b100d09075000e90402e0b2610490202c624101030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 260482904 1250 260481654 260481673
    0xe010506030c012d08040516180e0f06010f05031902060904020d09050a0521070c0504180c030b0402010806060a08010e100f0b0309070f0b0901050a0504090903030903020c03 76
    0x30b44420020700d05904000d8800890005808200c83d20303200c08800030301540d0882c0c45403074041c1404100b654150307120703c9125060040c451407801c0034010b841d91074900580b15520b80e08250054492101c41c50740500504001070407002d02001440d0017094002051011a44ac01040c182000042c10b040342070759108207510000360300e0702011144030f032100751401a501c807c01000100203051140c001046400b440a200f82800f0b0006494581c540c41e8481c840540d504425100f10103214000f00249404881c410030091860039911207070300407003025616460301181c0e60b549202e9a03885c2d002141d60180030018803080d07580c40f2003032030350207a020381b06107150a8002c3c0010348441c40500c104445030303400000081c4901c2d00780a0110040c01c11500c10082d454441000c82444d41040b05e000e9114466041d0004030580c0520140c822512500075040c54840c1541c01151583d10024111050080030400010120710328820b6101d000d00990b000a8095000c1c90024180003040608900c0381d800000d52 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 260484154 1250 260482904 260482909
    0xc0a0f080d080402040b031c0807020d0206180c060d0e06010f14130e010212010905060a030c0b0f0702060a030c0201050f011d04050a0503160b0f150d02010c050712060e010506 77
    0x81079925101e041c00c007010741c0c403840010f000d0103c0c1c1401607094090041c4500c400842070b0000c45140da03040d1a488400d41e911a02240c0d103915040309000160320410100717500201131880d40309450540c0f17007901d0105c402c000104080d03510a14145542d1581c0e0206c80c54010400c3c4521400b615a001d016280716203000c2c04c7c002d13003480b43d440c10752240c4085184507112140650140c602c0e844007070001e640307450b000c0b0b143c581100c10034401d01440030b04000010f40545041e4a40d0300542e0360103288580f0107410010b814150360840590700444442c00c0140f50051394825018140d1400c2990340402c400142840080c00c0d140c0250950028001d0300005100c103001c1c072050303282403000b001032269031680e850604915000360101d000e00366000c0080c410880d0b18408410b04030007401040098155118580542182e00040b14010382c01410040f40303c210345442d00d15803000798014503084d60b48119580320203043c42c503143d014017805081d00307a03030200b0003006005040c1c82c010102d000300464a400c101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 260485404 1250 260484154 260484163
    0x8030103210c06020a181710110318010b0307030b160801050f06071a100f0b0909060d050f0601090b01020c0103090b01030b06010507061407031107030905060d1103090c0a0f08 77
    0x100600e5660046001d10361355220b00d0b44041c2c04483c1c1c8102008044d6611447c0e02c40721400892200e4a0107010500b103110081c80c09904101c02d00c09008515640c3c0f9102c11894070040d41c2d211505030354030b50200000c1c7ea88c04000071400380d07024048203051800c9c00c640c4449813454880d40380301480058001001290f850610700d110104c2d06a4046d45e4032a400c0c0740980483c0420b545803180c0070404400d100c00040400109800d4800d1102e4143c0c1d0240c403013010034064012102e0b9242e201e81d0303074000070350380b81881c1405c0b16406119000701d801044404505c981810802d8100c5068944da41a046545680c100300f50710f440402030a00308807000c599101c024001c4d00c140805811100103074003003201644a03900300d52640f60889003c211030154145500600401a109540024200b100ca40c180c088107204a88103075600d81c407444125490801806003503040302c00b0040410796900c014407201c5580800442c030a09452001e031440307440f200e040004007101a00451107100945a080c840c01700c0002c1e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 260486654 1250 260485404 260485427
    0x60d03080c040902160c06360b07060b0a050117010b0306060f0f120604050c0a0806060d0906090c121205070507050a0e06150a2106120803010321 64
    0x500885181d84104010081e44299408900c0c00c0744001210f0b0100142c14000301042031060320080003842ea2008101c070007028031011481e1040d002e20018000702e0403100f0b2092080100340000101c030390359900c03000e50754000b84810340306181c03100e202481914204d103230000070b480e00342004060f400800718030b24168401401100d801039030000100701982d0b0ba00c0103440280f502c4400d816910040307003180e00c020340c20001d80005441306003008a402494903029862080e210419800c0c1807400c0024200c2e640324001d03210b1a0001004c2100040c02c086034024465114020080800c0003032451419900c4450316900c1300f520310a03150a400001240551a001c06407054034003251501da079810458200380040d84819440304041000280350b18564451a101d800704840ce011100f004900e400202e1080002c54000103c0600014000003500602580d050340481d10000310305443d2004028841603412084da01c510000c4010020400704030010381c02c40d28a1845295640f00c90000504061000c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 260487904 1250 260486654 260486657
    0x1081b130f230910180804030c090c0207062109060e150c0f04061409041b08100f1e0902030a06031721060607060606050903070603020f03010303030905120c0606010314060d03 77
    0xb01000c00348145c402e42605545038100381440c1ea43d503524501071114140324480d008400307040000000f2080e0010440c03100310b800c5501d1715200c0b40c245210806503c003001505000d0307580d03903a8001c00071408900c03405001d007200c64000c01c1001640e5071300903480b860091134070041d1300c400c00030092a0701016043c0c808030303101c0f410311a20380150545140d125000e0203440e01e030010b2506107903400c0304a0b216414401940d0030f4450718a1901c070303140ca40021241502982c2c000c2c25040604002c801d003402094102c0346c0c1407000803c0665210109001030742c0c801d41c0c01007911900c6500510500c1110444802d0303010303000f20900d03d401000303041405160b040f2440c51039540c01c1000000d5141c0c403030004a8080070740c010002c0100a84844014005811500943c1d000c0e2041d1440441c1c0d56009108030b600b14480041200d0642e031941e1b808401900c801c01080780c141c0106002d0606508680c1d0192801c5602e24018101c1850000001002c0300c2c1141c1c180300d29400000c0500c84552200b401150310346805 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 260489154 1250 260487904 260487911
    0x10230030405030403170a0e0303070309030b0a0906020d232206140a1a0607030905040b030c06030a02031b0405090f0a150303020a02031501081b130f230910 69
    0x2a0b082190440c095075001030085400001c042070346c103c03500000e1203040d4076500c404011404240074581d0302c0c0282900203021841a02050000c500030342900d591040240b040841c80e0900c50740e0f608103031b03080354031031805940c0c0380c1540d401d85030382c010031a4848488103000c20047d45060b50000318445a401c005840854243c81c1c0d0b14140b0034141c01c40c0c1c072050424003c01e040ca06100c2050300041800c0308560a0b4800e03004176980b9249000070032500c5090b0150758502d1264207003400c01004168079814a981b51081e1003c000d50b07500e0712405184500090140181c41e490030072100d980040c51024081d401c007104000600c641c1d0344003e4520303004141c071100039000d6031390f058001004000b9000020303070421151200008041e400a100e03d101c510a0b41a910450301d140035400c00c01c4400c2c010466540c11a040c1182264150400d5040c0300c1e2004154406001c01e50a520301155291880002c0b480d40710004a040c940764600341c0241c68031021016a01d070315000a01c151210070701011298400d8a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 260490404 1250 260489154 260489161
    0x141207061a0109180b0618040506060a020703021e0a17071509030809180901060503010e0304030b0402060717040b090f030a0b01060509130204080604050d08040b0a0207080d0609060501023003 84
    0x4e55200c01d21180c0302401c05686c4414a284030b41821202240f001d1081d8109000a40340742000026940084940d40041121509542c01c01c0000401c01000c802a005c0001c0810701a540e000140700c01000d020240c8600b04425010240c00c004490f00818181c032031250150230144e501058040403603030480e02c3c590f11007411000042d000c21401c10010540c840d03890503c20030b00b0041d448101120400c900810034070305e51000f4940c0701d000d1072001500c031040d0039002901500b003030310007002c00c648500130040207600f205103190441d4006070440300305c403140881d60345203e08141680c8040305100b10001c3c0104d6400e90b5925200c010140112000c001d00403c40040c141c6442041d05a0101e2029084d51248d480d03150395595000c084800351414800c007071851020074050300529005941141b20415140e6485000c0e03001703540b01d0202140d901d4410010140c103110188154006130a064101090309481e0000082c58a00c1420300e070b0241449003840282c80c060760108031402250820031680c3ca958 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 260491654 1250 260490404 260490449
    0x30b010e13020a0e010f06030603051c26011502010e0c040c030b0607080d06050909030711060702090f040c08010e0606040e12030406020702031002030c090904141207061a0109 77
    0x110712420003900000705400115010007214640390589601c4403044d84103903511141181170300d2603480042c045401c48c1403148051b074040031074208002c0c49410030b01e800e4010081000340403107410314543c07001101c500050201d10314441c004840c4a86500c000e000004900f102c1e903444580b0903014510450351058084921402134020300e048a00080c9001d4445485040c4916564403d000c40000540351542c00309240c0b0740140383c01e0140207048029420300841e9501d03160291b58071032071aa41711606103c800300507545c0b103800603c01c031900c41019100d410301d0b113450300c8480c100d600b101d80e01d0b0b4105480500ba48d4070015903d54404400c45003c2840c01e60034145a003020301808101c1103007640001040107001d042c0d0020917182d4400c3d0225205002c034403c40d14120300083d10038081d00402048040d8040c9002018a85c000d4041c1544200f60580c00300d04610300510f01002c0c0c0a445000308015003408074a11540b00003800181c40c602101408000003401ca42a41c001c2400b6000c2e404640d49400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 260492904 1250 260491654 260491681
    0x50f090f0a05030a060614060c150c04030b04030203090f03010c0f1b1703190903050304020607111c021306050609010f27090507020111090d060b060304060506010807050301030b010e 80
    0x2040301400761402500c50341424009002e0768051f20700d504000d01c070918a217060000884141c16805005444840755651446402820243c045c009811003404080080f66400c120240610f00c40c0c3c0046685600300018400d01030941d0802501c80e0345802441d1241380d42158075508003030003600e0b01d40340d14000a4000c038842500c0341d00c05062090800c140b07804910710040114024468440041031450000094005444681d8002000500c0c2800401e0043c10500d020b4a10140f05031106081070b40c4240115070380c0d250900480c00c40300e0a01d556101513050450b00c0c01d08a0300c1c004007d10842c0e0604000c115248502006681040300b00f41d20036002510400d070200e80381e00100304419802d54161060b40e445a07142c000c58424a14010100301074074014841e68540e03003105100700307040c815444104400c0b0349036903d054a495454581c8a5059900d03d4011841144600e10001e085e0420400040c4407480051442c400e01504000500200e240d41140394110381e91494805420782d200013641042 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 260494154 1250 260492904 260492909
    0x10150315060908070905100b031e0924060306130203070812120703181709090f01030c08030a1b0212191509030909022a0f0706050f090f0a 61
    0x40c06099808a0001d501c581d07003030201c48450003160708098486040720101d80f4240c8400041404a0408108020f00080503541c420094100039288240a00c20f285070604215410356664208140c00d060549031810020740c032803490311502c11640b07002804217589000c040c00b80d42d8001d0380c100b070040843d50104048030151843d101903030584030554501139050307040140340c00700390048100003c0301c45120f031007448258190308017100012203450300d0f0904040700c29000041032903010444105541c68080b40e40d4052181c03040c0e1030225600d14246650102450703003054010b500100210700d1001d0b400b165903010101000a001e0940e5054800180403810060a0010900545004001142c024011a00e02c2801141c0c0511b016101c001040229801008001c0c0410507101e0141702094155000c0e022002e6025414042040c0702d84000c03420544840040d46a5480032511038041c0806101640c000d1040d42007050900440128489150250b841c00078015100301868000c1d994503448642d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 260495404 1250 260494154 260494181
    0x30a090804030f03030513030c0f060615050c01180c090f0b0901030818150a080411150415030203040b0c070c1502030417030301030804180605060a030509060708101503 74
    0x40d1030b03a8030300d0300381c40c1c02c14660410b41c04a440d180004d0001051042d04582c03690f41a640c203c414000350303417031041d0709072102001e40c0c4d44c03a078401c008100c1104d0300716500a030542584a02d519544450501400c1d94614081c40d86146003622116001881d55403030b030b40a80e850048041380500d450482c440c0100654008298000d003800000010701041d40014105c030205860150a03419015040c402c1d1805c0c4108043c02d2410104880343d0a54072a040050300148210342a080c00940c600002d505d03442ca010424440e030000003001c020141035140c0c0c1c0700c08005d09041c20360440c602074030f48641e038001c010171804041c18000f07242010480c00748010360180481c00d440c00d1114280d440000e59030340041c01001000024555030380b042c84400070a480c100d80e4003080b060701e4942081003000102036030312414801c040d00c1d504045400d42e1501d000d03000c803d0702a130300003c840c6021410a486c240c80584508140a0000e083c07050030800400b81400b41e0b040c036540c2174941c468441c003c4005100c18100c800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 260496654 1250 260495404 260495407
    0xd141605030f1c050c030a0b01120e030306011206050f0d050102070c0603020904060807080c0f01090308030106020d0e010e01120e121305041b0203070b0c040504020309071703040303050f030a0908 86
    0x44400b4440c0020300b1001400c04842400705003800c0042040703510036610024080b00c1400001d81112043d0407103c0c0300c04040c5003015440300001c0703030070b0181e8409007480e810316000401000180d5900060040c084c40c0b4591083c00300c0c5182c140030a00001c0f800c2c910b1409424985039080c00d202c0250103c410003a1b20000d2075454968540c1c00a000b9001140300318444d45c20000c0001e550380e0b0005a40d02034604403405407408500d8041003105629030f80d0704060522808500003c007090202000c4c6000700382a030003400300400450700061401c003840070514103000b40b101003403940307982c0f11441c4110071a001c0c50014040181c3c0c108285420a10981c015070380c01c00003a8491140400706981003240e10680e410300420381d40b60710317a00031014200007100040e0f2084c000040400c009289071a0803806120340d85281584800201e0b061f640b0844604500c0d90213a48100000d45140d2606410305003a48042d43c01e042c155a0020258442e451b84d900c0f0120003c0040b485003003150f80405102170740400c445 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 260497904 1250 260496654 260496667
    0x18030f080c0f0601051203091e03070509150102010b0117041b0510030603150b090c09010909021224130b122506050412300c050f0d14160503 62
    0x25035403442c00340201c42c0610b403001c06d80420070b540082941d500040061040e0520f0540328510842c00c0c0e00306480d9541031150802c0018035498201049000701e103035800c43d00ca4034181c5400a801d5420708407240381040720b0540c10300010300c2c4642116030016444641c0c0c030502c402a84d400000041c40703400c0650701240c09000b814032280c140c0e03c4401240d100c0c480340000d20f10044c0d5518201d9911400681d00941124002070725064800020a06004141011030360704d6225802102207801090104140714404000d10031265101c040301e030250003c0c0c101281c0101c1c6c110011900d45142080d403080510f0310781c0e0241c02c1c5a034580201e10101e40d0301c4400c80b2805002c48400001120b48240b51588585001001044446c81901103034242c2c2c2160042204040480d51002100445403200c0e0f1007045034440c0c0203c1d05440a2078801d8848800d0351101103981d1305041a070304249903808a181150b001c041d0641d0055007000801c8140c4220300d44464507a61500740c030350400030b20000001d000d030100103502d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 260499154 1250 260497904 260497933
    0xf05070f03140108030405010c0f0f06020711100e13180501090c122d170405040c0203070f1b170105010e060103140c130509101518030f080c 62
    0xc106550310656401c0c0b209024403544105452420f0090840fa90400c2005000c41c0d4010036440185511441d0700860030391803501c07014103600204e0421185070b03400242c0802406550b0424021a50040310446d2040c078401c8006011104403400382d42c00b594203041b010500d0105036000100b0f126544043c2c0003407400605d0841c1c02800c20450448003414840701c04103507001d81d1083c0c141030942c00003959102c0d040e0005040525050112040481145402d21f0f00000c1ca51104c02c3c12130180c420b1005840f44c0c01d00c410041070724401141d4108643c8103118510100d0031940d40740d07450360340005600c02c918001401401003032030541c005041c038004184006001e104158041812030301040ca0411250b221080118182c502007515143c1c00c166120100701c00081000082090b4088400440e42c020703606e0f004981d56000840f0302c080b00b4940703118200b00c1d540e07585040c4548550b1700d01d07000d43c114040c0208000345107020300010781080311100f00c18040010710800c0700c5001994000301c1e40303441d4a0490b03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 260500404 1250 260499154 260499167
    0xe09010f180c080d0504050105130b0d06050a050411030417040312050c0c0108190b060d0c030209030601060c050a08030604090807142109120a0206031311100c080901030f0507 77
    0x1d04a48401442d1400154a400450621180c5075103130b441502c1d180c5020300448103a000140345c4e04c101c0e10340d55800a000100000280b02541ca100c2c5c0200780c43d0700d00400c1006903c625800706015a05000d40d41032101000e00460b03910a6200101245d01090001240c0303180c011750300004c010301020342d004907600307403c00091b149584880c81120b070f05903000001102da010060b61403100c600006130b0350060014494014840da100d015184a0800139000c4450b819182c5280e13100012960000348003801c4e05052141c80c5c0034240c50b0504410405180d51407658a228000700504220800300124929540f2500300340040c680180e403c03a00d521301400d02e080d101c019040c1c0344640f4440c402581803602c10486c00e609040e0b0200102c14140f10503034050280310044500c081d0920300680e0100307801030396500061400780943d05085640d0642d680381000c103240da03000603240305400040094105582c07007414801c00c158003051240d00e4400c500010f03005400701d074112401850600c82040040341d440b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 260501654 1250 260500404 260500451
    0x10021b12030123090402010e040915020408010f0608030403020d051006090b0f030c1f1107030b19090803042d11010f0c020a1a0d0f02040317130e09010f 67
    0x20443d1034a24415120742e2180d40c080b645035411030b001a00040144d80158044580400080d0002c601503c40b6a40c1c0d01481c1c0c21124a5083e0550214061010f4030f424411412007500000080144a0078009860b94034007440c40000e214040c040e5140e01000018072004030f4034a850074060002c81c2d00c070781c1004090894143d5444c09002d0590440d032541c60002070f0120241006000300e03842c1c000c00c0602114110a98048909010040d2866002140200245c000440c0111000700781c1c2c1c2840083c00101e544c444800034005401e2a500002007a03082080742d400071b50081c3c20100e1480500300800004502d28000c0540200107500c0300180f10401400740c4990909984620704c0d511900000d440c02c100c030541c081c0d000601c10b01d0622413900e611101c141c2c2c581c1c0e6261028108010700d40320006a4075201c0c1c0a81c1c09980104003002046244803040b54890058803c1900300101b06000e4007609941d07105030014907185d00003040070030400790b2240070030a0020310b060000c0246006101084c04a00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 260502904 1250 260501654 260501669
    0x1404060201091a0601081f0e040c0501080106081e060a210b060103020408030405040b04090f031115070f180f14090c0a05030c0309161e080303070210021b120301 71
    0x114084412240f8a10045105220503102c1902030380301c050b813001c104084681944002d015030a00030605240d01c1c5c503020b1185224100038000142004001440300f00c0c107907c45001d00c01014140300c8001da24482e880700c1400c14011841d22940d594002589000c15548410740b43c500002940341c0301003d1381c04081400380620038152280c1c0b25400110101d1149124038289500180414045840d0075000811000e0f00140f01280c031540b1340d2140d21380c20741489001c4020034000623a100000c1414090401c0000c1d400c80307200c0b02403414a038042d081c8150407030580200801c1001c0a00300d0640e6020120203410074410f030f0214251a43c0002c0500c1c460102003d11540c5004c001034020300070076003124140300c0f0340d560f40740c1180c55020005400380c10103040342156000d00150075034500700d510031840080c0440f5099280343e45a1484030074203c5d05d80d0700700b00c950350020010000016000118418468805940160b4a81c0241c040c0307034445120030000070340c1e0300420b40b10400345252800603505070340d10b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 260504154 1250 260502904 260502923
    0xb06040303051e0c1b030c04020f0307090e0402010f0813080c03040e01150203040509101508010e0609090c0f030a060608010b011b030f11031b0105070e0a1d07140406020109 76
    0x188450500d1301486403001c0041d84417a10710064040303c000c1442900d00c000d021a10104010400603069800c541d08820910801000f0040d03c1d99005004600521040c8601c03903c03424a41c000030104c038505440d003030500080002041c0740500e0500010f074000c1e000400030b07844001d120440c80d101d074480c0c892400054000c03000490380101412480382d00056075001103203450329040500c4002d040c01010091094040900040d40c0d030440ac0c441c00f0503010540e5807800560401c4100105003902401e014004c0030a0020400c888000080c0d01984042c200c034070180c0003044c400080d00c1c0990580b0002c0000e81441d20001b0b40c050150004850b14000f43c03226140e070003114074044114081c1420150000d4814540c2c07520290180c1c4070b2060b14070441e000c0d00e20348200e00d01000d4080b010080b43d034090b41e41d00c03410001c0103984000ea01d414048101c0f112903081e4038180041c0b1450904880030b44114400c24041591280100e1070fa160810061214a840ba40d0b1a82c005c2d00910b101c01041d1000d500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 260505404 1250 260504154 260504197
    0xd170910050408071e0803040e0712020909060f04020706090f020f01050304080906070204020c060405161a04170106080f0c130203090d0c0203010e16050f06190804060b0604030305 79
    0x150701941c003540c403440020640c0c03a1800d0007404003c101c6524a010a0180304008600410140002d0010f4a0140071000150500c54401012200c2e60848114154030620844015944100c482500800202d84007140c0312404e0740050024850100700070035907423402e40d12000f08200201223020180c000c1f5020789510b2184001901d8911088070000c11041c4100140f524602d030440217001c0b054005400141001300d1461441c2c40d2840c140c034291002d501842c000c003099004c1000000c00b4048070002c44a1b250051000d0080b90300980c00382c44100440d0754200d40508009501c5074008201e43c60403219100c800f8844144c0300d107418030207503000e5820303040410651241f03030084034051501600100340074a0300c0030003200c0b85001000100d900d5502e1711108000710004005440080031062039040e03520b0f2400003006113003803000070094041c2c00c0911100d40c041c0c40c905110144625136041a1100b0703960f914102004041004603154000804a004000c0c1948240a4840b824001084820310f00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 260506654 1250 260505404 260505407
    0xa032016020f010804020303070f03050f1b1002090a050f060708120702010e061006050705011506030f0f050919170301030b06010210060509010504020c030408030415140909060405060d170910 84
    0x204c1120013a400d503204008002c0040d0303e00c100d0340403140c02803034818201029004c01107010b9105680d00d81142c0000e0342050640081440140005900d0001c01c41c5021715000120700502c50511815200d100c4022040c0c000b07403100d2088601403544000580e0f9103c11107035182001c1d84d02542c03410015071070040400d4549000103540d5001d482c1d03480703024406526245c000c8503540e2055008a0700c1d5500e031f95001d151005542c03024000b624a648010070501101e01d1548102c0340220340c588540707400c0a091084035030000c60507401c1d0f6402e071003000e05204010308200c1102d8151201a003540c9200000010602c4200c141690183c4030981c2590720071107450016030709698040c0070701a80f20140c140108030300c1c5416030041c56284000001d8030304190391400743d03a00f5900302b580052001c05440141c8200242e01c00c05110041d030002c80260300b4664501c1c081034002600408141c0500e03980e0010a0340e5a50300381440b40515801600504c000f00210703d0861a9000078180300c1c003031280c0c601c192012a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 260507904 1250 260506654 260506667
    0x71d040b070309051507030f060635010e0c13031a1324180c030b071805060a1e120510031a0a0605060a2309060a032016020f01 56
    0xb544c000f401030605020b17403000c1c403000d118043c000c40245580d4111441403015a07004000060240f51284018114840740005003926031803810b041005804401442500c912030340d0505440c000c40c200b9a065950111010f030038406c018204a4811500380004108000028000d50404c105070009460b0340390400e0000c42d0101c80c0c8001844030340ca004041000c0707018040c4649810b00181804105809031844441100d440d040d81640c80039401d040500911030324448c1103070480240d01c0c0c0202ca50002d4441ea2480712910300034544640000983da261280c4540010300c0f4440c94100c100195240ca600702425000820007080c00076030500300020141011410380004694001b03520010f07201c240040f0b10008230005201642d000c0d582c8001290a4881030060090391085884142d50308040140c240712030102d4100740361f280e10f0200701a0740141c031a1410340b84a0303d12400c02096441400d941241d6040601d800554404000b1910348110022180c0800119009540d8120504c180c20011982d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 260509154 1250 260507904 260507921
    0x103150605090d020105040527070207050a060509240712030b0d030305040602190f0305060406030c05090702120d1505090106140c07180509010e06040c1502071d040b0703 75
    0x1c0740c001d00c051800741c01c01c1c00000782c409105141047c9826115030000d214a01520003860700c0034001e5621740840c5030b86048040d0000098002090074500e0400060510040d0b4042c00e030400902240003112034540c0030001300b803580003080d214404070301000c3e108220f80180760300760794030403608603041e084600901c5040e00c03502c4042d012030082c061a880540c0070300ba019204840f4141d0030808109485c545a10503117130f001190396001144124044018181c0d40e0140819120305d05d854810400110074a240c20222a0f0542e2251340c2039580401c20390405030fa040c03d810100000007008100749045e5481004045049121044131680301c4040c0901241f00340924800320b10765500d600c0c540c00c2c80d180617020003e0320404075042c242d241d8040781880d42101c88250303101501c9500b406210f40d000c1c051407101c4500c0500a01207450140c035000404441886100b054421142c0408034a5200b03000480141c01002149454046c043c0101101c0e843c2c2200c0c1500d242d034626022501003403203030255401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 260510404 1250 260509154 260509157
    0x101b0806040e0c1c0c0801060e09060907060c02040902031b030d05040e011406040b0a121107120e03161205010c0503070203040b0a171005030f1f0c11070806010501031506 75
    0x15070400c00040c024501035a01803415060926501c0c01c0000705d0690318900540340c88000401e140d4506450030600171809002c0d403030690401340070000369200001c2c120044420901d8000d0003283c4500200d0010209400c1c0603425001d000314030405140800803803102090160112903e40b01c3c2110101c58a001f02c1c0940c07001640b03040c0040241851119882c8100319009005a1402c0e507105401c0c100e41c0d00103000000483c01c2000c0c42000c45d031062107041100c2c0c0050b050030340382c5051503540d0440c0e1181703422050180f041000892131591070800403070628811260143d5540c6840d881811070301b4200702011692517081815401c0c0143c8290180d0f4040c201c41c1c2c00550a0a050040303610550304040c0841c2e0421444000858500c1164207205000b012607a04c2e121503e8104010301d400d003501c070420101c1d10780c130240c081218110f401c1d58001102151000018403204a168100c0b2845250281b80c6054481d60001280c0350b40c011980300e048030300980301000841c81d9254551042c1425214920 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 260511654 1250 260510404 260510413
    0x203070c0515120709031a070509040f0609020a030509010b010f0f08090c090a09050c060f160503090d030842010903021207140411030117101b0806040e 67
    0x2200d4104070801c45858154040c000d0f06144030030104100c603240480c0d8031300014409280c10014061940f000d555450050700703200380c9a20f41400081c166100324404140602d0340d138041d2614800480d40464060710f01e40c05c0955070b4810100005010300000e8440c11440e501e403000300d1081d50301075201150000c040d41c41e11000190403041c20303100c0c42d8000380080e200f8084c181d1080c10640d03d241e12203104500c4c52100050a0425042c00791901149040e0340b400303580304200c3d060f1000100c00c262201c0c07086c160311a6000d030b031080c030300316003540110607400e03400141c00d5440004058008804502c40c0e2010f00c0021071040e07810120808c0c202c4e050001c1c580361070804400c03801002c0b41c1100c2c4201d00c6410304000c1801d0f43d49030301240b4003101d0880c100da0140c111402c284141c018092080c01e50f00d0023101d092007407408251450000b071106100e04034094000c4102c0a000f40f86c188803043c180d0300c240c2401c0020041c00410401001202076001e400280b4600019605107010301c218072103280d90324000d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 260512904 1250 260511654 260511659
    0x605010e060310080a0803090f07081b030102120406092009060f040b090709060e0102030903151e040f020117190b01090902190e010906080f0604060314010506010f0203070c 76
    0x12070300d03601c09849004009203198002c2062001000155101c2d0b00c1407031119580e01e00110014244001542d00c0c040d1604845010400d20030300095001c00e48130541408003003041801b00003402481000e4847e10036612007800c11017031101d141e001d01049406103c0d61200c0c040f030541264101c103645a03036164004d0b20980451900d04102d0b41401c0c2c0300e00080c1001075030003050030005e11554800c45e1650002180242c09102a0340c2c0120f60b05442c12082c0019414504c2450019032243ea60340300014900341c011001450706030440605101031580015003810038107040c2050300200000d1102680400d94188030052158640e9490a2160070741d080a40124000010480050948140715504008040c0b1021848040c1440240f120107000d10183c0c00c00c81c1e00700000380860651030110341c140201d903081004060b802072801e07540a80e904048010030382c2d58600060040502e41c001903c04c0c1840c6000780c11150701540128003a060980b21502c0b03060039040c1c12030f5070b0f21400d4402448400359032003c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 260514154 1250 260512904 260512909
    0xf02041401320d09140c0307030b0f2511160b09040c110d230c06150109030c080c01090906121e02120a0314040e0f070c1416090605010e 60
    0x110721544544030406407510526000036403d8070640384094030500405170b200b01c490030003003000d420103180c2030300504070161440e00c1d00700510000a119040907500070000036804440100720100f800c054100580078074110306802171042d100c0c220120914418111183d032286030402a13001141e00400c886440c008001c014007014105030380800c02400800b085803d110507060001000c01000c50350b4102a000c2187c11800701c0f4003c2003210010030004000178058a0004550698404822a003500d11380a490004869003e001c0d070000c0d013201c42e151001305c1c41441c04140c105002c58241e075040340351074503841e5030000c4541903c40e8213401c21051058000142d04800c8000d0320007005444001d800e181034000c076800000b0120060010f80088911804064000e694502c400c100d400741b00b404d15080c9844140d01a06c0604040641c0304000001400580b042c0100350700182c3c0855080c00640180c21b020303586807004107107c90b0941c28100c010482c088030f0300c0b8a00c11500143c1d241e046105040d800e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 260515404 1250 260514154 260514227
    0x50d080901020106230f0d0506040311070f0303080f060a060e010f0905090c03070f050306090103064706070c090203040c0f0308042c01030b0612010f02041401 70
    0x803a41d042d07540318200003a42500406034003440718203654501201c42490800c2012002d4640c0c0001e2040002c41400b50100780001111684140d01d401c01c5c0705402e480d042c4081c906490b503031060003440640c50002c0209640f05104a00400c00e407428070079151201000c00c1040e10a40c05403900086401118401701c1d841503820015907581800c0c00142191680081102c1060840d41740170554000028030402c1c951042c81c9800c0030086290860941c00e290300000d4000b00c040c40058080e54440225400742a031b40080c1c10000b4101d440c640c3c151200c080c201c44400800403414444899500f480309003181441c40445d9809a0705c01d4800200785c2c02c10f200d030402900050404e55030310701c10200104d405a00416020082c500542030661154948002048a0444a00d000d00c682203034240c0c086090400251340c6040d2907022698103c42d079640008078a0313404600403075010a600780b10684040d55130300c1c0e0041c401e691000c580b0b4140e403800140191641c0d40200070326102c201d41d080c0c1c0d1b50410040110f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 260516654 1250 260515404 260515417
    0x105030f0606130609060f060207080a030e09180604050a030f11031b030f2101050a051f0e06040f0f17101509050f0f010504060b040b0c0312131209050d08 68
    0xe0f00010030544510300d0350704450309030300301c6a40956040d0701070041d40d80400045005111250062045c69a00c0e0360082c015a42207154034010030950011072403100407004103c1100210720110340691503d810702035a01c1c44402c201303601168a20040e0402c0034841c00b1300184c0403905100551921085d1102da0030300045090722048103000900070341101c4035995004200e480b400e84001d00c08043c44c1010352280180c103a100910490b400c0d503041000c2d0303e4004207c035800c050700c0d9a109402e80030080641b220b200f0b0014013940140e0004012400c0400c3d20107403420f40b40c003c010101e41c5600c0e04030b5213280454641e140c040b00e40c1300054205c20750420390040340102590044101c1495900d1000e0710030707140103440c0c003021030050100b00100c02140c9413400d070041a0464051001d6494084656520b21440c003800b81450000295086021410400c9401c000d800b0418030300f0b94601444a13000e000d443c260200d9a070200c81d00300119840c0310307100c0b0000740c4100400309207a0864035500d5125540c00b0343c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 260517904 1250 260516654 260516689
    0x130f1a03060315010e04050c0402072a1a0a0201180b0610050d052503110f07141b091807060e12070b090103060801050c0906070c120302150105030f0606 67
    0x450111210948110084c003c00c81129182ea403810070b8034046003051190119030340160b106114503030201d2140107910303804199044007181c80002a5058001c1c91425400000b016024142c920510101e50402000003010715402080555a2440300b035100124108014041d8102503020410710320701304014601491860801516250001e504041500c8041710640e40100c0300e80c200f00c410746a8000165002c4040d031a0070411b0141d05410403589025800643d441000b010500c48100050f10b60b00c4207404411004a55810050a40c0d0b8072904401c0d04944e4018102180854075620119044601c02c0744004040e003000c0341020b00445101c80780c0c0741c12651100700c40400c103c0c8681c060004001a02c45c2105050340c8650030300002d41a5a89503201007001c0e1314000401003103545000c1510705411044499a98130074607070030326280030740c800d0b00030740c2c1030700d00c14071301c0c0301c1010380000b03000600c1c41c2c000102d003542d0780e44e417000c064980880216640e2140c011100095070b80c60300344454205114203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 260519154 1250 260517904 260517913
    0x23061905060d0605090304150e030a060e0f1609060b1603031806020711091003031707021e060f0c0301030221100c02060907080303011818060c05130f1a030603 70
    0x115110f810585500381c2c0e8403246500009401d02100ba01c0b502280d400d12924205004d50410407000f00b40e840081c0d02e005050155120504841c43d0801e00c500c030b000c001c2207012542c55000c82c0d00071541d0310303005214400806240142c0059181110400d58040b81498400c0c43d081110326241500a0507611640f001c000340f101c02d80d02d000650a201a0401f98010454004100480028090040d00180c0402024002214100000780c0e201075250404001c0a565011585507105c06a180c1104200c1c00c4000c2504251088030900c0001940c0f0301c00d1007044d006006540780e400d41725160748400c3c08082e4022804914101800c004624040b01d010641e40444032103809440905d400c60f0f00901c0c031200103170030a90500155020800211000c2e0101b20059495035150074410310b5008650307002c500d1141c0d100c0910042c030300914203264280c280c2168080c0050013032524003d1960707010070312001c29000740b034102040036149001d1050079600d0002030031511070a03120809209401c000c01c11b41c0c1c58810b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 260520404 1250 260519154 260519179
    0x804060c17070b0402011d0d02040932190b060402070311030c0a060f0501240c06020d06150309031d06070c091d19020405070e0405042306190506 64
    0x1141c009000b52805003140e6115824a0f05c0010026085506440c0724007000074982c5000703035140f1044050042d81202d002400403450719110070f0000d08103c3c042140f080a00340040041c2e205003003094007000712800c0e140b00700036040e012100c826085001038100010200018031900b0b0607401000c0d1540241090080061940302e0103146500c43c0ea0100c000d80c02c00d80d90b003400c12006d80204600618104000d100b150b04142c2c0c96500702c01c140840f40300c815408040d088020b4020b410861800d50060070956603851010940e6000d050785220f8444940041c00700c14285521a00c01c44091550580d5444003e50b100e82041c0d0b101c100c5c41c81e20680c0004104041e00006082c64018001013400c404c01007060b03040b100ba668000c82001e0103940041c1c1080d5501c030072640d001e22180310710b5581100c0000b11611841c204503a100303141807507503400c189080140018000c0310094841c21071490101e9240800100354459102c2405595003d080030b110915030f01d240075250030066028401910a10030100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 260521654 1250 260520404 260520443
    0x3060e0102160303020406020717030702101106010e01052106060108150603090706110d0f26090a02030d020115032303070c080c060f09010c0606080f01150807030804060c 75
    0x312030341c01c21004a0350001d01080565010300ca00c02c0240f41c06101cac42d88155a0f0f03442c8a49034030850000a1180000020407505140a1080742c002009020215011503858400300804d0398002c1c01107600c111344180c0d980b010000a070800e12a080410703005003602c2d4860000540300c2e00005410a00d815400740301012894640001079841188041c000700b415a10705100609103a04060360341405410002c940305125800c40310030f07842c0c42450b203081c10050900404030060f00341d040f00d44103035001c003000900604a50004c0d510003414000c400b40c1e503084400d0310003a401c8a4481e080c29111146030381003000401c042900c078074150b245040140d08542c03040543d050030355004040c22900e80201940511040e4020050814010000d0390b016141a44040240e000b90141d80c042c130341002241058030080140582000c4010f1a051044a500403503280c40329000e00b40501010b0b400199515000603081000214041140d4101c030182d8502414038904840e004c0d960b0350181e0307038105620f10100048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 260522904 1250 260521654 260521687
    0x201030b0f0303070b0a060b0f0a08130807051f022703160e0a0c020a0201210b100e130c140a0215100501020c01080709090b030a021c03020f070f03060e0102 69
    0x1521039190f0b0b640601d00f4164030300031030b07e81d6088101ca120052140e100c16004000440e40310080504115905a0312a00200c52840da035410041c1040004105a01080000160b03e06a821394013603002c20040c110320814200d001d00030199800d500071684c950142145c0d285640080310000d0705643e41c20308440c548200d40c036544d62009031002409030411216942c07901c500d010490072031004d000030b48003c1c0c000174896001108500500101c000100c080910705610201485101403e20811100b004101510694032001024000da00c0501c085401c10218030490311403c2c030a440d450005c0c0d0440c4102c501075081101c2900a42c070a41400301e1a44405044151186020b551741c440000d0400000908003003945005c0f03418013030024144102c0340e0300f100703074101581c0100e40b0028856940000280c6440300c01032001c1d41001d000452065254074011300b03179584074025000c03204a140d44600c1d540d5035841a11034151034040d0200288000740759500000303005040e020000d0700700624018860a070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 260524154 1250 260522904 260522917
    0xc090103111302120105010f020a051213080606030307122c181b0c071d01030b060901080a1101140d05010e0c0f09060a051209030703030b100203070201030b0f0303 72
    0x12041e03a01d41203010785080030031851420740b40c2c1401d60034192018103200d010381042c05124184218507400e1804503100708043d002140e00201101d00604003820001b02030b5000c4c02c0015910000c0f02c0020a913188001561400b0322005801545403181c40d031500501c101c2007040d0341c000c0000c4441d406241041c07201503441086002c0380150b221202c80c004006251010440c81228500072401704440c500e040003a81c11240070746030328181e5540144121a0410f0040e412240100300d207114140300c42403544580e50305880c442d1301410201d480da60204129843c00340319400c2c066110419100004441c510764a035408410b041c540401d2070b180198110707641050b80c031501c00d03030b543d40010081c5404100d61160400c03035043c0a140b421500101040491190b5a12903004160000e81c4010b4148108200c03404081041d540c801e05e030802c3c80301c0076283d5000e81c400760002800d203060714800d40703000c580030741108d00a07400541c540300c0240e0043d0058406480c41c83e5000e51800d00405c1142c4080c00205030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 260525404 1250 260524154 260524163
    0x3072d080703030b0333040804090f0515030109050304090207230307020f0109050a030f11041506080901060b03060f15030a020405121c1d03240711030406110c090103 73
    0x30080e505205051800d4110b10032401c1e00032009200046da200031001807031001044500702c203280c1ea5103090141c0d0354070880c0e000d440d44910f03094003542c111180b540032501440c49403d0300c105a40640c400c05003070b04c02c0b501c8003074101d0b001040304000629a960090050a104201560064010100b04260745690303200380d1005420000d08201181341408000892103802d003004003585080030301041c0c1c0706c007590000070450182c0d02c1040c01030104030780446042e028028824400c039042080000301e40030707885c415203001c00c218101103403a00c00c06010322002d8a0028107901c0c15507994108100100c3d2000c5402508005000501020809240d0055115500b41003025036200c0c540307010b00c801a1074510407421903800c1744001ea41030201d60080640203c0d101d1074141030040744603007110440c1010390b840075070601c80c810960100240d44540c401822860344080501c1c0d94030180d040c3ca00004a0101c40082c0d00100070900216000303954a0640040b11002c46041c0c150314000704607451002e800545 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 260526654 1250 260525404 260525411
    0xc0616030e03030a1b0323120f01151209120507020306010b0f07020609010e030d03021306030e0a1101210507080603061e070e0405150913150b0f180106030c0203072d08070303 77
    0x2d030005480000c0ca038000d03e250400c02d50380d6241c11240c0803003029410701032f01007081120310000000c0381d94000104054201c1441588408101b6000d843d69200060490003401030100005101c907421041c0da000c0b038204145e09150007080c0d4204520f96114a05e01c50605c8641d180d11040c0351810045280c40e4003040d00e005a90b018060101581d8640c40e5010508150600c1d038030399003102021a0165003213502000006c0340030b0303100006a800010005074014914041800131103000d00c660040c40c0a64500e444058031500c40a00b450703226441142d60750303c14028408100803880c3c0c1c3c1c2682540c84921850100c1301100e120380000c2c00d80d1402e0b10300b1151500c081c441c846c454646088801c0c0c01111100459010710315660751a5010030001243c034040558450014056407204d4403d1300e03204000030101484826101409014858280a43c01c0000c1c503181880071082d000104503200305401031001c1084050140c80d2201081c0401c1c0400d103820f82e0580d03a0b0b0001140d1034047c0c04924440d44010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 260527904 1250 260526654 260526667
    0xa0e0610090b030f01090f0c020307060b0d14030307080112030f0807120606030e0c010f090306050601031103042a062127290403050c0c0616030e03030a1b0323 70
    0x1b030680ba04032405088142c90100b83c0025140c001085498081c0c1c001c00100d80c0c0c07441a0006a4080720082025140c05000b4800721100b59004c0000c6115880b0f2307860304200390341c071a485000d19061000d0014042800d0303410000c802402503a14981c001e80600e00019000403010f840c0040c0e402035840000030a44645a1200401c1c0134002003421600a1900c0c0411f41250300c4000e1800320203200180909540f00c010580d0740e44240c100c80300c0f0f41314021005549040c6894a20030740309140000b0800034a103240c0040c80381220380207034401c640840d51200c074003844e034107030f008210240500034141c425600c6000d1101c1d50000d00011b41003140048081d44c1410380ea080c030a54614100c000e4807000080c0303946903800140400c0c44550000e030545000d61311220707295200751501d2441e52002d6401680803c001d614180c10746102040c0d18400c1d524010715292801c03cec10b035680908071900c400300c0c0040c0003840800e0420a012141c4900078580b4409210240514400340040140d9086001400040301c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 260529154 1250 260527904 260527919
    0x121d030c070815010b0d090c26060408180a15022104081009051e010b01110c060d090203030d0f0605040506030307020307030201080c040e01080f06060a0e0610090b030f01 75
    0x81c0030041511101511001242c488030b410300e00d0050040d00402c500c0420b071850769074659405507100d10b07408002201200e803070b117400c540d400020100150a03481d0040884074561408180c2da80030341d50000700c85041c40020020351420200054001c0e0b00444102130005e10140d6911100765607a1481e00504580c441040c40701002900359244c03c500342a003000100301c5d841d0f000600104c0d120840384000b4500c5828503005080c00130000d80000401c40300746292000c1070066011543d450004d03201c481c000d003800255544c4458601e00c10b541c0c411070500070511400589c0c0c0240010030300c01401e0b44d2500400e40790050071603400f608101a01c981e81c0307000388103509051041c02e800c003404030011414482560f000a07910002c1d804020704018458000c42e007886040c03000d58000c1d01c0c1e44070a0800b1581c490780010380d5803902503410042842000b0106580d41803c0e840e03c015900c07034000000301c503960602400048541c40404600300109000001000e6890030051805684180c0c111001c0e549411b10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 260530404 1250 260529154 260529163
    0xa0e0a0f1b030c05060703030e01020a02011a0301141503010204030803070c020109120b0411011407111e090429040f020901050306150103150e010e04060f020f0a121d030c 75
    0x1d5501d0020300414050000c10006a4603200302c80007140c00642d16011031500700c000d840340e46514074a83d0b0012500640d1190190069500a1411350841041561036010182680c1030024002d0028030f075a404961030841c41c01ca84000d4980150015203800e5584d50380102076482201c4520016a00892030003c543e4001c450f00c00078010143c0c030300100c002540346e50300d0041c40900700a10100d4992400b03240340e40206691032880b4201d1211644510290802600705510300b004244201103442c0c40c11481000184039084032440075052a1240d501c554410100300000400c4000910301c41d40b440200070402d03c007803442a0310498181040c00d440748180420000183c020500c60b800460400c4810703082c80d000784041100920300820347c1400400c210a185c1d03515040060403140d4800003084010350710101c580550311415007003142d1680c41e0142400c0b40200b40005800440070003c0300001442290300401c00f030080c0c01d00003040420340981d00c1101c00740303401e4012a81c00c04951004595800e20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 260531654 1250 260530404 260530433
    0x301080c0307060f0f0311030901140a05010305120a020109020409060b03060f0708150a0801050a05070f05040f0302090a0b040504050c1306080d05070c0e0c0d180f0305030a0e0a0f 79
    0x90080209a09100f00601030001c6401d09404219130034040c504c8a902c25044500b00702407111106503207080c5030b641240a801590000c51882d0381c40350101e44000c000740305035030489030044081c00301e5103480f42c40c0031203680c004202a4110743d02c03005000096942e80c403c01d650307648154800106800c0240038982030403002080580070000e01010040300b150010f00d03003640007002954042031180750200282035124a40c0140300c1d55864034081000300c04095000134002c2c0c000780c54510f003420340c7c101c04450714400c9001d8160b41e40c00c826010001404c4c608812034100720f40b00d0740401c1e8804514085811140b08440503900d55000c00d0355405a824480c00d0084090043c400c140700300c905150480c1d0740c41c141c038001c10782003020000d080020300400c0e4040c80003130003210103441d0b403038180b00394100c2060f0000710501007030038a40f07e03240000f0100e007414200300076881034020000c3d088d00d89041c0c406070002040002d81c5c540703038102e5113000c80d400e001600c0220b2040390034004217100d03810420030040114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 260532904 1250 260531654 260531659
    0x4180f0b1009030b07030f0f050603060f0108100b040f0c020c0a0b04120f11030a050714100210050705040519090b060903190206091c02030f070b3c0301080c 69
    0x450042030701903100711160256500003a01c0101c1e6181c0180880041c07a41a8012020714a894441d4080a100360062401048120704a910030380341c0070b6255034002030a01c9090001c0d40a14494a440011500600e00101d001000007403002290f01c10b1005484500b402040141c004015404491a00c0180d00002c2d08880c901181040e04080701c00c800b600800340060074130085d441d403401c1003003106a82040d0058000e4141c49010587c4d10306196250b005020b62441d454001110210506240056034000d216582c01801800315440c0171074002c042c064001401c001c03080002052a0b00d900081c01030014a0400c00b482a618200740c0b0b10469450040480c450b000810400c4100e43c3d0020300c540103c80712602e031000384089440013074564843c4c170040d1500f0000c1d1341e94110902c4402d4510610285c002e41c180d40038400d075952050340342c4400380a80e00d0a40e005101100204100d280c0300103d4a207244010305509512940c0b041405142c905660342c0000000010b20007914103003e00c60711008203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 260534154 1250 260532904 260532919
    0x2191401050109052e1a0a030f0903120c0c080417060604020c0c220c03060305010f0902100c030302070b27030a05040311040b0901170d110d0302070804180f0b 70
    0x900b800008003041c1c018850380380c005c3d90101c0051550710f5000c4002403d0010480c06822484821003140d5081100b076000440d18182030066501c03003e008840032036505582d407008114108c1403e80040071410191010841000d8005002034441d00c02040174280c034414404500280c0b6503070500c2c100008000500030750050000d010549000140e1003020701044400c0d80b014060900300c08281280c2e25066854642821b81d0b05603000d030554006002d4901403030087c040c0c0c1c4c0c01c222201e002c1d42c1000308000d4010301301d4001c0b441c01c240b10300703002203540c2d20a19015140808a440d200b02201040c1c9400034803485815111941840e248080c08003051200055030420511400140c0740f40102d10028021825085c10140c0035a580d600103104088014240e1246503120740400d844000304841c46440c61080405041d0078500407060082142c00f1030004050149004208038040c0d0001901190510320038400840c05281e222058200d9403101c8400180b44504404010281c1d00d680c018503019054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 260535404 1250 260534154 260534161
    0x12160b1e090601090c1b110102030c010627050411040218030a051510060203030f0406021603030507031a091906030b04210e010206040222090b04050106050a1d04030219140105010905 80
    0x24400c0b5000301850300705201701503031002440181cac1107110300081c10b080c44d464100c0200e10619051402c92419802c00d45a9020104240c007010031204150f5019103203003c4000b0011241c64150001e101454881c00420000401500403d103410b800100c12615900180e25281020780c0d00c9445660203c0b085030140c040c14541800a5207030b200140041080041440c0010b00b402029011100ca10404008d1421003075000e060040003082c00361080c40011b41003030400c80c0d40503c42d115100c070f00c03c0000c0041e50f06840e1000520b8201c104078084048480c2c4859000010800c840c420b544a43c5c0124108024008500d045140103021510000140100140c02c0c04080c2d81c0000c540d030b0301940c103980301000402a0340d803d0401c0044480100c1c11603041501c05020004034600c5280503501c03d80081c00700e0768840003001052080e0307025841750499003800490110824041064115000e80107039640c800091040c02c005401440c020f581c402020114405420340c2441814014400c1800400c072504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 260536654 1250 260535404 260535437
    0x3020312210c0708030a0b030111090604090b12030f0d0e1603030f14030108030c07050402040e0402190f170c100210020a171302010212160b1e090601090c 68
    0x7100389107552621032181c40082e030300c1c00a0340119002c02d600480708a1712403814a80c800094445550303c18007a500b04000c04150740c5101040c0c0d41c01905c000c1005050606012030380000748880c401c3c080c0d1103240c11401d000c0c0c200061004014115400280540d82d0060002c1c02d81a9280104403940903840714641d0410421881d4030385090340e90614100382e90b01d9098070112180080041c040004000000c0002070081d400402031055103c01400c4e0388045698204005c224040e61081f41c0308184400001001803820003148285041c83c050b1403840c80d500da20070b500250016401007600105443ca0940b0611400c2240d0b0400810440350b5101c1d45240c0c40c0003d484101a2450780746082d00412103012490040050411180c0c942da0409070310f10300100030b480d201c810b0100c10780c058003514560040d128803d408540d000141c50440c001c5461550b520307580c2c8054020000800c2266491001071002500300c846400340d01d01368000c00f4170703506040c1118219218003480710140003441c4558007114 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 260537904 1250 260536654 260536687
    0x3091208010506030a0203070e300304030b0c130e0c1201080604030c0303021b16090509060702030403030c0602070506040c050f0109051503040c0302030a03260105010c0b0402030102040b04030c03020312 89
    0x1001c21702503101d8440704401d4441054001c40d4a40c00710f001c100001010340c05080d4100f00200d0403e02100d444640c16039141c4905c612b0001400911043c00001c11440202c07000304980242c64a13610b415a617201410000c001d000d0700c6505421f030380040c0396030446001022241c0908842000f510345030034290380241254121352070090a041e004603035603410840d50198100d594822005460244901000c025410101c0d4065888154649004030311070ac1c8000a14a12800c0580c00440c03526095807002c1e500e019401104594803a02001204001001803007800d00807840385603403004980c02d140c2007002e03120804482d0350400040c0c1e50f0800290741c0e51541c41e0401e454481c0500c0e0349840300d040c084a40c21054202039058803402003a0783c100b60f8005603a00340c520b000040d00c0c803010100b011201480b0001e21880f030008200e1b800e04000300b83e084215035007292000b800103140c2580c40741410b1070340d08250310603603484100d03402c10020f40c1000c2c01840c9103100c1d50300d002c0c2d05d0314812540310700c1c0380c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 260539154 1250 260537904 260537911
    0x114071403190f090309150207060c14100f0b011d1003021605010504030210060518062101051f09020a08010b070623090c3c100309120801050603 64
    0x100d0a240c00c041d001079642e10074035440030014014484c0780d1840c2400f5150740380c14072031000f101000c00c4400040c6480031078000281c40545e50782510100241e21010740081c0c458180e0403540c040d03601c055003131060510540b09407003331040000c224005100c00140c07100000e0b00740d2121040d110588100d01da40c3d4800589403034900c6d070500507110007030a25420041c4881d0000180598a40001c1c0410b041d000190100400349880c014000c46844100740f02054100c02c4c4041260004071b8080707011071408000440703101e1500414070b50316403108032076542941c0e806d0b500e000d0301d0401404840156403c9046a0000d8a0503000551409801800c002c200711030520800050f40f60100c0e14508020070745d04a14a11441e54804044102007042100d6180d00192904000d610591681c5016402d24600001e05100d00e0002c00000280001480c1d0078000d8500b06030980c049c158042400d140d94604800f110302d0150b584c001440a06c5203003407205640d0003c1c0c19014409440d00410165503450100d030791 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 260540404 1250 260539154 260539171
    0x110412030807022b0513060207050a12081207020309150c15060310110c030f040f08060610031a090408070b0c0301230d020d1406060402070f0b070507020a080114071403 74
    0x74a049251040b2501e01401840c44806d1101e00710000d8980c0d0300046040036114111015220b45550303504407904102d10510003003162030140400160164042d01a5034070680a006403072a003c0d00f40c002036001c1c0d402504090005a0215180c08044000c101c83e081001d02950050b130b0a050210009503210410202400744a0701e130020701060103842800d0b2480d405c1044c0440b03071070315a50303822aa000d801038014140c00e80c40ca9500099040700000f642c501074503024028184d003500401d030440243c00c14482003580c80380c1c202c8000388181c40d900030141c803950054100c10340b10100ca1401c030011110113402010100c03020b00c018014548600c80300794104022403585080075070b450000c01d85030420780c03502070350242c2060303941000d010414203469024a1900c00f42d0b140395036000f041204900540001034071014000030390070005150114016000136050a026080481540c00503403260180e03000705810f65102d64258001032000080c00740c010034241030001250f40702c100c6030300160000030800342 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 260541654 1250 260540404 260540473
    0x8092109011418010f030207120c080918040b0a111234080c040f18200a02010506032a010309080a051c2d11041203080702 54
    0x1826030042d0355501c1c80e8960201e4140e1500c80800300e00c04412480d000d054041240001c92002c980d202e0300c00c0710f14155001c0d8240c200844002000c8a500840e0348003180c00c03032030070400e084c12551000d420940c2c00646542030140d524041c54503007403030540500700f00c404606050462448114240030f5900317882078000740002039a540301129001c0000811001d0101000044140d01c084216001c0114045141c4800e04640c43e06a0f0301c081620403442020b907100d41c00d4a060002e00b215420b50700c0301c800900c0010401c400c41c400c880030440d0840043c0451000c0015807414001c2c0c080c068240d106c08110050304828441c00c2005a43d404d0000d0309454003034884030700d00b45e40d0b030117a84030565aa4110391070ba5191014040040e0450740403101440c1c51101c80b0103c1c000428107401645141a00e118100f08003074110400c06803045600041f598160341c48804031b00c00c120385900608010855020120a8410300d03003005400340c000502001c085400c5185825100044014561004160f10b2042c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 260542904 1250 260541654 260541667
    0xb0408030702070e190c0806060405040f09120c0516080606090601020115030506070905040608070302040902010c140309040c050307090e06010509060304060c0f09061e1106040b07080921 82
    0x40b82030041c41d0700004e10280c1c03480c0034007825650401c0c10044030346504004104101d4610420750f00410b0803600598004020402400607050540105291140c421804a281038696072480984165104008002201703440e101c001e0207020028403084082407200d220500382000089a100d1000078116401500030001082e010b9100f50300003100d00d01646041c0c401d031a100d00d005521200103658150010f001c003900030945e80780c580314480407100711500902100c0d284d82e007800041c1c00d101009034148201d00c3c0140000c50600ea401d02044614078025565030f44100341000201c0b0350105201c0200702091003001481078006440200f5030754862001d4846954410048034030348035080071590000000f000b4801000480c1d0808002c280c244d446605240c1480c18045a181e061880303088000703500703900c56128a031010b01310300080748114541407a50801d05c031011450418140da003100c409008004100c01582e11080303d90b0070001c3c0300007034a072096010f2207040a1041e1051244401040011341 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 260544154 1250 260542904 260542907
    0x60109020f0702100c0203010f0e060a0c050415020d260402150d090311070b0a020a03080702010b0a0303050c01050709140f120f1e0303040b13020102070306020c1014040b04080307 79
    0x1da40c92264014844d964140e144075004121400e4602c0490007582400c101c8150704803c0e0080f44080310b107642c020880d507500c01c014000908803455060040c05003c000200d4401082e405219400006400138000c2ea401000020140a010805200760724100701c1c9914a070841c03d0002d035000b9404440c0c00c0d03840910280b075400c0c14071030f03e52400505490600107070101a001415014840c8000d010303549100c2d070b506880121032150030804401070b0030040d1407900190180b50f0b8290001264400003411315858804110748111a40017600400c41c0848c0c0c072503007800d09029842d804202841c0c0440d000e440c0c50212944000301090051085100c0039400720340b504d4215100020300d008204507000c2e02c1d400f1003015201d1101c942880d00a01c9810604190050000103c9028580c0406500c00030303510080903800743c500e03e440880c11402104400008112a0b0001e0b0a101640f40007811a10000200c104122211480d01d4011038070b1000030403000c507050408450740b09400ca4800c90340c03691032000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 260545404 1250 260544154 260544157
    0x1812090902030a0e0106080105090604080706150905150d050c150d140f0708070c06090f02030109050d090f12030e0a09050709140111060601210f0b10050408060109020f 74
    0x5465101d1010080000007100354004a25103040200204900303500e50400310f0070785600720340041d000e81c4890040703000280c00000804005000f41000618646000403003503594102e03910101c200798983e410b2040f4824890000202c0e0003003111380800c540b40c1a078a1302d44651210410318820041c3d10040000d54100b02c00721130040c120003100b009901c2000010980040043e1100c4404185000004030101d008040712401048030341c881c441601c40e242d482601a0076041d800725004c40c200124280141c50034041d4a5880c0d00c260094900d03040360000c001c012031701c16804040e051801400812181d4400008a01101d4040c40c0141d003d04544000c14040340b125400703250168608001c00104641c04401881902e40c0318210490382180b4400456a114981592074107a0b006031011511a41c05120030b1107000c00f07d062a5482c3e0003070301800c0412500900c04480d07410b51109250179141c43d00482810701044541009410f150410440b9981c0700c005005452482d40d0000380946088103410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 260546654 1250 260545404 260545409
    0x14090c0a0908030c10060e01030c050405040804031b03020306100609030b0606040312030e060601090806070807110304030b04020901060f081501120513061b1d0a05030f030a080a181209 81
    0x141181d5855400380c8030556250341c038000c0e180c5d203149490404107080401a030024101d0303401601070b034846030030001004001c080180c03007143d13080c40800c070010010b020583c41c1001a0481c56800a1551540c0141800d2000080c5044041c0d9204d00c6d0a10005412a0f0000182e94106040c440c0d190344900c081051442140c1019110410300802420181e034540c10514203846194107030b50182c3c45140040d10544082c0c0100200c58200070000b07442144184041540300546190030308080410420381410343d4010b8205030342c4802c01c1c104000c2503081c00010640107100c18075040214241c4c000004040b04070246c0750304081c80501c001c65441d0f038440e4a201203a0000036208015900703118200d40b4400711000411030f403403070814500e00f510303440a041003181e00c105c503141ca415152810406c01017004240c40c46070751201000c2e1000c1059201041041e01300032043c002166150003851300a0600031004004103034040c1032140c005584584513050702c12841e030080c0c810500061400056400300204e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 260547904 1250 260546654 260546669
    0x301060305190501141b0c0c04020d0614061303030c0807020604180507030920120a0308071106070e0d1401050a0204060e0307030203060601110a05070801050a0614090c0a09 76
    0x1200c03092580450042810b00b098800c4000300841c680410450107400780032141d070100c12011208505900154030b005100700c802d071405494100d0328080000d4126000003020714000c030b50380d55080c0311002c482065500603520032582541026540310324420080c045000040070004041c80328030401440c0401e42c0c68a5600501003501e982c0c450401a00420040240145090400700494030840c064420002c1f2240c014108024a40913500e45840742c0c00142c4c1d000d6000b505070200140f8001c014440c0c440e90038425034404140d8200088000d00c8000c1145e24926150806801e00483d5500b0001106a2820a9903101c2203210075082c44462403406141c240394039400d2404210104445030300030700c20b031185030700c404542111803005d00d56101c01d0303404000d400d544403e02103075196010358403204c92006600101d840880290782c500742071504940c81b10070b0a80d16070382841302518541c0107041c05080300e50102000300909000107860000041d1034015446030016010441c40d2107488030b02d003e0b1055 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 260549154 1250 260547904 260547913
    0xc04090915020315040c050c0d180504090b100605040b040e07030902130510060f050301090203090106050a030f02090a0905100903120603050309040e06010501080a1113091e0506031b0301060305 85
    0x407100300d01842d280c25080d0702c05c6107003400741c0c2c1141d4081c038152040c100550006010714005004162000d02089200941614011400103410790791f901408084a10600540030142401203002c150b0420070f40020091200034041030003514501d01c280e03401c403074102c261861140ca80719810b5006150110019400101900b41c0300d18201540d00710500940c5240c416083c4280c0c4c1da482244c0844051080304001101040104001207042d005180c00c598071f0300000510b15956400100481d160780c0c8100c03404001041035000f07501c3d05030055540b00c01c609106004070007059541c0e80c0c845d0410700701e00c44803d65030303204402810b00c2180d01c1c1c2d12120b0340f040100302260716401e00ca5917980018221031312a5040040045000c407001c50042d0482ea03068441c0c2c030302919a4010480074141445007560302039020f11824408410306001b8400170b02e42d44e24009004205d420341e10386005204c0c61180d82803410a014000c0c41d0f28005211243c50110305410404002c0040029014007100d42c00542288103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 260550404 1250 260549154 260549161
    0x6110a03080a140c070311060705091212130807090603030c0f0f020306070c14030a09120807120906031a0303040b0d020c030301080606130b0607060903120f0b0301060e0c040909150203 81
    0x100e0300000d002d403034021f85840d406450a0113240d59074403030449000000030b01c10312252120741031a00390700900c10819415030301d03c3c0c902680103004c140c00400390b002869450680401450105001384406440303c020b00b4130420381903440290110701d410700c00800140400c4c0600b02880403221100ca4280c0e030082c2560310074200707154010200720a0307000a580b40c9641d058807407001d030300c00011282e10301c12540390b0100d010319082c3d41441c41070340814280c0c0d800408120100008a107100f12503202d015a0700d61040c51403c107080102142c0410032074078200e400905010b64580d8002040d50111000d0041c125030319481481100082e0080c80d0b030003101480302000200e078070403011a00c1792040d8030540d490010560641ca81b401500c6420b49040d8000100300004804108607800c403030000ae02a040031a000d40000349801d0444911b0b0034a402d28a1343ca04820b001031400b802542c00410356080302e10102c7c01c140061001c50321503489100314041d41c610000e81001465042504010102c010454581c40e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 260551654 1250 260550404 260550421
    0x19020a150c02190f030e0312030f1602030c1c03060503060103060c030e210a03021917090c060f0a11070308090406150e040902010e062206110a03080a14 67
    0x290600c401016006030004180c007040c11400b12070f0415040660040702c2d9100b5102501c600c031601e040c042d098010340043c4000101404011400f90079040b0036041686040881030b1100f410045815045400c100300c0400c040000044031241c980951440340f1480340c0202c0184e009084a13404960140500800002480702c203030f05c4004e00d103145441c241b103240300d4001d55644980ca07603043d00308000100300803d5a50303041d500243c003c00e0402c0c100140307414499841e0700d603154580c1d08110000342d085480e03489460292040b41e0703001180d02004000c0d12020100240076409440d02021036018045002c40980b413081750041c00c220580c50540e06140d4490401035110741c452000345000303600f09a000610002c60140364004504590344840402c0d00050420029050044080c0c0c10482d02010320b2806641e280002d01901e982c03d18a05008901081d202c0d114821b0b5078044418020300c442d0780c000042001c1880034071180d00d0320f03080d40d1175900c0c40716120040100060f22030700d601c00201000441c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 260552904 1250 260551654 260551661
    0xe033f090105060609150d0906050f06030f07060c020f0d141b010918050411030304061805151b1501060905090a1109060a02030d0f021201080f0319020a15 68
    0xe5900a00a120030380e1400c05204003485403452454000e184501e80c0f084806110f030260000d0b2481c0d05020910724070a03149c80c01a41e0040d601508079545403414040b15280c1040148201c2e200040035003106490903401410b0719011160184c081c50050340c5410f034640da144905294640d10042801d007209c030b202150342d9114200286952a2010341d54400e50641c000c0a64404940341c01c054442180c2c11403001d040505000341003101c0880d900c40100c101603900744040c00c05444240d40e080501180904607007011103c1d548000d00841c5032100213248403100c6821034400c21050781d00a44043c0c05d11042500e020481d40c65251b04005000001c116150302c0001706080303503401c44441026031241e6251b04121111001c02024040d01041809400e083c890040c04803015540140d0b400c16508040c00c1050b0750710b1482d5100202e42c002a0a04500c00c002c4a16001d4010000103200000407421400e80d280300d02442c490300040100c8200f514a4070030010040040c0c1d004071100c0880302c2150709030001d07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 260554154 1250 260552904 260552911
    0x1214010e070203040305060118020d2d11180307031704050909010509071a0c19020405160e0402090a1706010f15140c03040b0f040305060105040e033f 66
    0x1015140350115012920010644040da600b020143c038059103000c012007408032500b410700728030310380910175205e078100140700d10103028880c030707010824414032900c2d81d0081d0b41c03203205641c29142ca0301d0194041144000700f03490400100c10101c940c12800d601c0040c0ca0820f9a80c4000c0641c1800c0c10366410f4906114054011948251030141194484454103400c2c0e030380c01c83d00c2d01140d50000104100504454050405204501401501d004e900c3d41a260a0100c100c0322610b016081c110035404500301440f8075984040c1451229000030368030b010041c40d031113070442d42e9441242c012038880041e640d00070f001d00090a200c80c0d680e4001031142155615402c007442800140146c1c0f0000154500501c2c003c40310307000441d9600900602d818040d22180c2e04401000303205480103200104a0740d0b07107003008180065442c0c20494460b0320710b1408501c1c00d403050700281c1c0a1410862a000788441c0002518442d0031040602d50300700b400340c2038400880e1000240d0585c06141c5650855042142c075460a00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 260555404 1250 260554154 260554169
    0x90705091309061413320703051e0d08060604051309030f090803040506070507050306010308131a190c0503030a0b0301060b1e03130524060409080415121401 69
    0x149139100c2a110390f00e0004541020704660004140c6000480401030301c040d03c0000c0e07181405500544007081005105040c803100c843d401007000740b007880003c0051003001040142480f01c840f030401d180c00d440356461f20130719081c000da00002c19850369408065401400028001034041070000c400c00d07004c2e04000303a050300400da0f000b02400107144201d550030261405100110310b071514040600500f40e12903030b010745180c001ca002c0840c0f156000e1103a18000d502440b4140c1c0c40303588408503043c2e1202c00d0351103070040b400d13030b10319814444091030140d0722081d688241c08180140511004c0c0c80344041c1480090203400f0005c1088003028240d4001101d850065000b01300c4161640341c007400318401c11904042c03141409216140e0243d40c000103590208200100c1810f050480e0340c1c091030150381d98540d0f914100c810250144025040c220542c2c82401100d0503c074074000386c5c4900809229a00170859544000c0210009281c0510101c0b08206e000c9201042601c121a000a0140300203000340c3d907 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 260556654 1250 260555404 260555411
    0xc0f030c071112030a050d0209040606020c0310060510121404150c140927010b1801030510090209010c1403030402030c030a051504030903061a091605030609070509130906 75
    0xc1d45080400c8030500300503d0100071494403000907425035254000c1c03050302c0c040369020810303500e0a40b154000d04005005940007010001c1540081505040d0241a10306429103481010000750b565044142261042410800c4101007000603101c081c008107125100760f5130300c0500348401c004001d0600582c012420800b00700403441048211015242038012480340c82042c40f01c0c50700c0745000c1c402c881210504407003c254041c2d2001e40c000c1456805d0384003481152000c10000c4000481500c500d07080c0e00240703810406032800407001844c1050034042c680c01941d000c6840b4640303900a9060b4801250011a560010145c1203959640c0b640212012030003405210031422140c100010707006411070380320019108210b914442c507001c1400c0148181d08001501a001000c903a007031140e66010b40254600c2d00007000008180401c034a00a403101d01300356003000b5081d6496a01206a0303802c10412146005241c80340076040702c050142c40180340d4001d0703683d03580440c00180d60b070000d021544206001d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 260557904 1250 260556654 260556683
    0x160302010c021207110307080604030806010206370f0207050304030c080105040201120b130e0a020406060207080a030302181503090d031103191b020a0212070303090b030c0f030c07 79
    0x483e110302e00d429086101d07640500800f03000896241da0350190301005000c407440940c4d2988031914011301a241540807841c6d0009114007940d062102c140d000b041c0401ea48041c07152200c1010782042900f0782d209144150203491551158542c000c88960b204000c010b644903d810f08080380c0303d90040c402110740c4c2c0c802c04e000296070b04060044074419501615002c00f5001ca82881a000e0003501c00c40b50341c003103868540c1505914651140f250703c08048001022072500510501088a004e42c01c54015503200c0d54041040c1352000549640712541450050f071102c1c8482410f4010800c024801a4080080b024500c003400542018500c510294000c0718950454804281c04440e440841c8a1000c2d0040001603100100c8180c8940603420a0b03800258100301e101c50b0106201c0032661800c01604512485410b51070940d044c1c04110045c0320142003600e1440d41c000d00001010310070101c095402000003000015101300342c0743c44888100400e9501d01d40605030300025070207203804031071180c02141c55 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 260559154 1250 260557904 260557907
    0x31401050303091c05030409091214091306030b010605071704060f081e0405060108010606030506090112020303070506160807110604080d111314010f080712060902160302010c 77
    0x1068100c0d14040c02452070901e20609004c428540c1228952621204014100000b00100300400040400f07070340018448015103014000100009604002c000007a80303058110850001111810481215040082143e0480e04009032030b03035074005070903001a4030002a402e034100c8001c0c0041803184180902c0710300c0c00c081000301400b80780140c100140c500c03000f83c1c00b25405614142e401081e10700480310260203c0e04030740d6418600320740c21280b030340102d0010000c2ca43d00b40520f0000d0807180c01d040c0800d2900c08081201d030348051060010761000c08100e0000c0d9241401101d10258201c403d1b1001c3c1d03e000ca021401c01c07a0382101c6040001d0380000080e07015441000c00107042384409020385403c0e10b450320380d006a500584211030407195100c1480a110246800400303030660390442a5610307914159481804c074590000c098144801140000c0312070b640820410ba10889908001120f114941c20b09001041241c02034441140700281146900c0c40340721201688521983c001d012200207000c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 260560404 1250 260559154 260559191
    0x103050c011e090e0714032e050108060d0303021603020c0901060e0d0312060b0a080108060a0516081512010e06100b0909040614040807060b030d090b0c0a060c09050103 74
    0x1422000190a03d81c1400000e80c41c0340340e60307040503051070541c00382104072005c21a00d07441a1108019030024481c0d1219032841d0100404140c001640243d5036140707044c00191003181c008210b60700c145101c0e0016010540aa416582c0118640c0d100c406214082c5c5000707540c400b0300c101c0141c42030808030300020310b6500c01d030a259520340c80540070a00c03403282540c00f5100388010802483d20162113290100d01c0d000b003403000c3c000081e62a41c9103c41d5515042c0c032a400c00c0720141c4008101c504000030410604024a070303441d403100581c680881c9030b6030b44480400e8400b1243c198182d102c18850300301c00090005411a02400c80344605848494603030384c8022103581d0503441201480c00742803143c00410311340f400700103500074003805020509103812900e034900c00c1400c5030121580400451607005100341482080c2203200150010410386100d242d028041019501c6507000b01e03d00010168000700e0240001007140d5804030b000c1c0410321341241c7c0035051000c24050b141c00686044c00f6138192124112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 260561654 1250 260560404 260560457
    0x7081b07050d031e0e150a0314040201090b0304240506010314070207140114030a05100b09090a09031209140f03070b010308090109031a180a020901090e070504050103050c01 76
    0x2c55002d268071302c80140c1d0611022600b0f0700d400340058800c001c506138680c0603003081511015441c003540c0d80040040501118540c0c42504500e0b40302e102040b0050b40c0000000041c1c80301ca0100546030f80d10343c9050400d01d411003044c034105540d010003150040d0082e801c41d0340100c1c4242c84c2070044461884c0400c4504008035403150043e800f0407010001c82c42c0c842c0e01c001b0315110604d00070221a12400c1c400e10303560302c10755500003115540c0d02002401e11056079000701821000d100e83c0d00d44800d1500040d201d02c000b07001c0350341580d50342210504042c0506544000217141d0441806445203e051904003510070480d01e040707601498409070803811020041b01c004552041c284c1203182d085485000c141c3d0096a60181440328074030012010800980b41c0b00280d0f030484040c6281c528126581a40c1da0810030380340d070b1061340701d0a85540103a40e00a0510b054407080342d00010380a0301d80f04c0d03140c07400b112a403189420500e800d00200901c1400709001c442444d0a03202e0b054264840700b9044034500110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 260562904 1250 260561654 260561657
    0x150e1c170105090901090503030414010e030313030e370504020c030f07030203130f0f06050301061b11122103040b01090903120c051c060f0b0f07081b07050d03 70
    0x1000600491400360f2590f03400520000c000581c0070b050384e550600d142d0050314107880502e2011040001d103103007409001d0200e5032401c05141076007001e0305062070b0084662002418001c08001403080d070b07110b480c0040302c20000c3c0b0f503010034200305034599015001c1660328000e0f180140e0500228080c100b500844007101c0042004500e85102060035104580007040c04408500041210020807241103000c0d0000d8a4000f250884003850030316903800420135a8800300c180001031004000c4250004440114004a0102d5030440300d0f039031500303c9002109a00b0303954840e604440100c484903000401c8040402440d8500000c00e01d2900c045a59001c2207a00504505001d0010b01014046400c0684442d11908100c9241d10580d42004103866204500300d0000e54082044607800b50b04494116080c000078004009040c1800c0d4405101076044c003d007041000009400307552280140100c4d06030303a4012104546a1480f40b9010301400413858144610740704140700802e29160503d004490305030300d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 260564154 1250 260562904 260562947
    0x9071409090a0b010f08060112020607060e07080f031b01110a0f030207020411120a0501031e051f0209030d02030c03070b150d0311010c08060307030b04150e1c 70
    0x14000c011500500904a0145028001056000403100141c141c003810301c07940654282400c14880c42d25200c0d0580c03080b5840c152004642c0d005d030700c1e02002c0300c0f903040d0420404100b0b000d01a0001d40b41007590350000c5107500c50b10716200c024a202101500d5890010100c0c544010400c100c082d00342d072203000350040c40c40710400490b007802d270003070180083c1400c180c1409402c3c4003482d00050112010205c0042600b100010200c01401850310f030254080b4601408000c1941103454403d00d001070801c1000b2561180c50b2040c0c2800000c00c2641c4103184202d110b400d0420309010341c00c0c0a9080006842d00070300c0380001e00c007902d03400402034032582070300b1a0085080402039146c00340414006040700c3c0f10075181d65450084d51303e8950050310104c0c06070b1942e00814203400034070303821076260728180d50030041880e003401040e65005c01c8a508481c3c10514000803900caa00307120b04005c02610090304401d00c1d00700c0b223004030706001c9881c40c9881024100407812001c401f0b03054800d06444030100c581181e2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 260565404 1250 260564154 260564189
    0x90306161d0907390303051312050a020a0b040c030b0105030a030f030c050d09061a03190b0403030b1801240f18090216060b01020d1706180106080f0907 67
    0x115003495400003603e451aa00320350013841d95051604803941e220b2005454120b0b07818107040d098050300380c003d401d050241c60804580c2c7c0307030008002e240c448058100b29000405c07403811403080052100b03580e0041d14401090919280a20013a07156110885a01101c0b10001500b49404518907030015010349512001c219024021002440020103c43c03d12005004c10807255000344503a0b4015403080f1800180805921226000c1c21056410240310b07034803440c0d80d64006603070038882d003c00c1076000c486008162100d15003540a000d0010f05079800c54800203460854030003241281c2c0c126241004600610040b9900c6001003410b81f02d1118081040075000700045032291011082a0616040c0c0c4441a620b4143e0501603a01c810b60722400d10300b840000d101840a1440b8410032503100740002d01c9048803c1d08003510207144034940070000e030b910000003105900e880711186034a00d40a002551103603124100a0700b1a541958401c0e220310101c4000b40420030001a07600030b41e101c280b0854a50030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 260566654 1250 260565404 260565407
    0x17010e011d060f06370f0501141b03030403080103110301051509040219090204090e01020306090105010c0f1a090609060103080d0c120c050a0206090111040b070503090306161d0907 79
    0x4090022500000001c0c031900c12480c2c0500f082c00c0010a02c1c0b412220100e5505c41404401201c0e080b040074050201c4040225a03040540c82400600d2444920f80f60920711042d198094151020380700d140c00000208802c040c0e00c14107036416603125070419490301c041d50f018182200c104603001d80e91054070094001c03051412419031603006200500f400c0d081001480c0d5614203000319030200102c40e40201c0d06102080440c05011505085080214110710740000020400c850610940f418011507141c1c2c0014008100d8440c1d22554000101c03038491074020700034000c8030a084039030418901908020030307030070785000c40e8240c1200c0d0440101800c0a028240340402028812185010700c0303041c5000040740340860041d0354402d6000d07120f440d124000118080e0074020000c01c150b407164941410700003144220803d48003507500c0a40c280d40c039004680340c400c2c90f500c01c403003400e5410b108580030000078413180304007003001e101d169540103c0801e1490045220020100007280d002c0043c90001d03d071075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 260567904 1250 260566654 260566681
    0x406090f030f1403070507060801051311030f060612040b070e0d11010e0102030403140a050f07060207140114070c15050c0a0b090c09010e0106030c0e010c120917010e011d06 76
    0x100c50f400241d901d4890666129444c00b00755601803c081144903004001e585030003180702e84134403900c40c02030001e40088400c0c0100307880b0042c1100b50040c000700104155841e00f900782d5080c0310350201100c40900b043d0a1062032500708071040000541234501e00b442900f810a103030007080d940040c01c07814540d00d8000540390001d024901034110f100070702001020514055581c80d0030116071018094224050a020341083d070103071550440d40d4003045c01041510b44c001001821141c888446420014403103004803910f0620850b800c6861074045440c1c0d050148140080045a21505201d810b1802d008015122800b501d8003141158011000d01004903019170051076100c040001900d145d000780f1000201d00031020303002828208106801803240c25094441e89105400394105000c00d80507610000b400c240314020020660b5007814400b41c00390f40221800c101422044948040f0070061150042c008c1202e0011080203600700b00d19040d4103a0318902035520018410003411103540d86800e0804007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 260569154 1250 260567904 260567933
    0x190b0a09060e0a0c0e0705040f0e040305190206091c09090207020402310e01050604180e030412020108010509060d020d1103011401030201170f07200a0501020406090f030f 75
    0x1d0300c1d21201082081c40c0c00307002c1044180e1141d2a612841410b0130200121060014a100c050040402050203a03d01311208902110412074043c0c11070313625858200c60390700941000c203d0030000c803c98401d1154020541611482c680c0d021100c400c00010110340b90005007040440101f4103200003480414031540040402c1070003e00058902071950341c2403800e000c10142682001d1200044440d0000c02942e071140080000c0500380b14154103210000e07002d03100e1445501d441b180c100c5000c8800b507503d074101711000d5048200b9652101e94a880d50108030145000884c00a40303c0b00020a507880d00c002140e0059001130000e2004100c5507080c41100702481b170083d62400b46a40244247d903409000b644541c1104070500d640075403443c4009000340410b00c0d10660b44210300d00800040b214031403c01a8403681d98607104101c3c4801d070303140e41d2031158144d82c0308000b07024003184203090010540081081b2080c40e80c40d542d8959445101c3c02c80c100c0c640c00000d000a1002c880e42c00440c03292461900d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 260570404 1250 260569154 260569163
    0x92b1e08071812030806090c0403080322060c080603010606030212010510120207030e150a0c060b150d0c090b071101180504140f0105060705030412030c080a0e03190b0a09 75
    0x1e040d8588a070310882c183c1503841100001da04078104100c9040c555007094000120740d110741c4c185070540d40c0d07014035400014011115200c076a002e05002d108006501441c0640100080028040f2540d004000010840b00d0303034080d60904030001407140c800c0c401c881407960409120036169080008000300c1100205011003000b00c3d540140b1b000c48402d02c001c0c000c4070f101e920341544440590b42402001c2044000110b0003020600c844045160070081d500041980850005250440b44000440e046580d51241065100100720038540c41500d5100c2c0341040103680341c41c040942c1d200000e241d00d214687d001460b11407500004460f07540a8080000302840c40d030225512180c8030340101d422180b000540100c03000405040c0100410307185881800740c002550050315081442e02d85554034400d81c481c00310302d01c0820007118180343c800c0f42800501c6910a4007d6034420a1540003030000544c030903031a10900404209800740d022546c40346401c02d86c48240030443d569440e02000082081100584 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 260571654 1250 260570404 260570447
    0x120606031b0114070503130f060909050403050304030c0816050c1806101107050405090c10020309060702060904091b081b0a0306020d0f0c11010b060301050306040b092b1e0807 77
    0x204410f81f41d0243c5c4068030700083c0400c0d1552608000802e000b101d5445401c2492030304c03080c0301c0402e51003001c60354841e03098101480d40240a2030483e41e948200c0007030301c2d00c40c0c958100352400c010000c141030210050449480414800c940c04003490540c00382d840e541d0107041500030040142c000c403402c600181405058132980ea41c0d8402180c01d646c0102c92101c0550024105d20040703142080842c041501070380700850401c55080f02094440c8103940001c0e1148801141d04200369030350750080010342e07a100c91b440c41444189201d02c1030390032480c041e400050040d908142c5208103000d500d050010030080c001c2c084149941c441c0e4009500041c450000b140c0c5490f003495140c1c1040c0130b080c0c600007180e51413100720082e0002d0b8500315448a11100d2244004100410081e980003480b941c12507081000758142c0e40b551030f0380078600040d80d86030106ca00d403c481c0c02450340501e00d008010309002a19440f000002d004a5800104002d820150101d41c0480226990078410b0561a01c00b011307145411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 260572904 1250 260571654 260571667
    0x6060f06091814041a1b180d0c060314091c0806030f160f05010206040206040509061c0c1406030613050c0c0708030a020c0d0f020f060702120606031b0114070503 71
    0x201000c3e00c045034250f0b4490302c8810b0102030103040c1e1082503845002190384440f80c4e0186a071546061203400494111566010395100701c568800801d81c030425400b170810000c55654440240c0030341a402400c00300c00400f9400180b01c210041581100e50660380d991055100c0510000e0f00e01d1100613100a40511451082c1e400000302040316411003c1c4040c40c0040c0c4501d4124120321094079604031030f0454101c3ca040c0b00058035180c042d0340039110200d44200c200da81d03d60100f0300da0701445079070600d160143c0c4052030602070804041800d80340c101c50300c00700854508080c865984401d854180e04403c90103d400d400301ea00340d10498007c1002e105503442d0a0500d04024900900f82d0880342064000103a24061142c04204907140f000c1c098446800014003500c1d011208803124401034010340d11400c10b0f210a9445038100c9505030703801003406141810703518180769101c100300d40150081c0304214071518918034101e42c112071940160f540d5240021350303440600c0c081c2c12125080f80d40c0c0c4010b00c800d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 260574154 1250 260572904 260572931
    0x80f180d050105100801090218041103031804050a02042d0503010903030204090614010807030e0102090d050a0309050f060906090607080c21041401030c0215090a06060f060918 77
    0x64100003400380d03001003920300708400d00c144e1826155200c202c45071305d00300d2020b00680b60002c4d03854a58000d015460201d03a241e0400011012010ba1401d9041c000004c0d809031b9660611304a000307404003520304004035640c83d01640124070890040c5242e0b00c484111952000d00c4514807a140904841501344006a4640119083d640c1155046020076004207081c4140c41c09441031800a20b400600310039926403050001c7c1c088040a8031100800d610340d0003d1100b01c9094044403103180d00034210400b14103050400c0b503110240c256080300045c5202100252602e0104071582c600c4100a0590345440212401c02940e0b50041c40c01e5074100e02c06001500100718020054180384e01c982c070150030811108008002c0088000103252030540082c0b2041c031000c440c150781c410030784030203003800a2541400d84003a483c11984400d01003070a8100d10411040240129000d00072a1148600f805039588800140c407220405004260001d5034450080118031000548101c003510041d400181407007901d4023 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 260575404 1250 260574154 260574169
    0x609060f0902040f02041a0d0b0d030903030e150d0902010e09010305012013140609040c020f0f010e2806110a20060c0a02010212090c150403080f18 65
    0x140162141d40c0c800794602981403500a11062a441c01e00452401d4104445d0507000b4030b415150441c003140c0031500201503000c541c07000e800c070b0340000c0c5514032030000c0f4980203044900902003240010141920724485040c0103118940702c06942c12014140302180020f0300003009280d000380e04004290402c00307010703203413641300b00c1c00380d03014100108600c4040c00c400c00b02000701c00d0050908030000c000c9007090219041d14201078501e10b40e5121070000031400000c0880c0620100c0039403261500701d002851a4002485900548141e420307a502107401c907000600300e5020f0301d0120312541180c101d4544240401c05080608080d100381c054001859403501d50484549400b1040b15540004500568640010520200e1940c10200081c1c0803420b01d075050f1125405415506004404160020924000c0d01602c5e41003503144950006441c0003144035544981d20b03d42c04c2e005642001c0082d41c000828003c84007502e0300f10a0b01032410300c400304080100c2d03001c102414907100440d4000300e0540d40701c18 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 260576654 1250 260575404 260575421
    0xc0c02060a0306210b01061b0209191b0305010501020307200402160602070209060604052d030d03050103020a0501031407050a0201110d02090a080c10030213050a080703030807050a0903020d060906 86
    0x40320556401150300d05281145e0701a00b01703000b132101d1141401861007a04812000d030545c1641c096421351100340851b0226043c5200f8203001e1428031030f10350b55618025410340c0b8654034640c2c0900190340e0300c00040ea01c9100d43e03c00a402141c0c0346040242c2441380b00c08004d12907a01400051404890440c095810300c004001181c6443c1c0001d84003003949442920103801007011a480707446d0034a450f000801c007034000740c51034140c640c003003034011144460051600c0f0843c401600b6030794415035802c4024010070003404103d00c1204411808582c0307510911407030010030015960308041d6120083c2c190b0301604400043c0d001c5640303511904400c40b07000c0c0081d080c4c8290b0744c60b0158498045900300103041440d9048520940c1c0651144644d555074120b400c0c08201c441e0400507644c3c1c0b2400c00844880f0095007109403c12080080022034540c0016054108d034001c2e82c40c0b440300e1301c80500132034044c819400c01c0c01c000b031800070040c405440c1500350104007d00c04c01c800103600000c0e0383c491040d18406c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 260577904 1250 260576654 260576699
    0x170c0a1d1b03010e010e0106030b0105040e0417040801150e0411120f030d0b090604141b090409050d1e140d09140309030f03090907080612010501030807030f030c0c02060a0306 77
    0x104c01003203100c8844d003c0c42d01420031405d06000c9506a2000248175024a208551003151003c5c0820103200c5864400e9100307928800e080c517034464035860100e018081004020408100344040002d0110302c0b2819030740980c0e070000c40311010010900030042c900603210382e00846d034003480c0e081c0e900f40c84040004081d010780c14000440c134a400302040114032603005024a0140c1c0c18140003c8020003d001b5096114055a000e64020200c407030103846140903240d01c454106203498507280c01d0082c0000c40c61240103607942c0e1200c050041d4140c101c0030034480c0000901003501100e07084083e00c0094040d00900311400d40009002071551103000c2952122824030074150400209450300b41030a0003026501408000103500e03010141011902c00003004201204108000b030105095980745420050811000c0000303020950711b904100c10140d01103030b0102c000c180e8800501182c0e5020340542d0800c0c545035210807103449650f400380b104d190300c0002c0c01c0e0308042d0b8904021a00c0340d2401f0f00340d081c5e503485 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 260579154 1250 260577904 260577929
    0x28080d03050a05060303160818210105060d0b04060504020609031b030c01030e060a090309180c030b0904050a023003040305010f02120c0a0203040b04170c0a1d1b0301 73
    0xb2140c0c1c0800c440e405401a0700039081045000501c240384000c514005c5d900c200616610a460500825810a008615035000c110107a04c1030403080388204280081a0301d500070086529403034204811132005940081048030000c000401007501c0394010f590090000d0040c0c0d24000d8107200090602e58450b008107030103c01b040c0507a6641c14108915040d081c803e0808000000441d4902036550380c00600454500380c03940303960700070948604030180040084400c001d1074810f000c0038060140a51056000001e4944910f594651504544041c01560890050804c05e249a001e0210307c100c0008820017804608006040040300c0c2d0410041d02c000400c0a561582d0843c0782030b50a4a0b081c844062560b40148501740c0084180c5034010b42107181d110106564400809050303080d402954080810b000300440c001a110002414100880140d1020b0325410580740d0b0402102230128060303141070081912145440c4030098030768640081000c0261901403c0b140d2410034658800d030050040b4095 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 260580404 1250 260579154 260579161
    0xc01060f0909060c0f020a1e02030601150305060a0b0a120603080f0a031d150403090b0d0e0c090f070309020d0f0f02120a030503130305120103030302090a09020928080d0305 76
    0x2104d10414440080500d0190359200001c203000b981d030b482240c0c01911400b100d03000c0c20958555030b80354401d070f141d014058507129030307482c21a000c3d40c0c0300903034196010a0800780002d0340751605540e0a8103a600040e001340c20300350403800c112611420b84501c47c4030503584110200c0861640c1c8058035500100c030386410307560306403940010300350f500401e103411001d041864141c40301600413a11501407285242815065a52401d04458204103a4030405001c140041c40c55050a465040381440c0f419423011201d02140100600c01c03804d10441c3c1c02c002020424000c15000d0b442a0440320076107000130310358a41d41c41540c40310100d0300c140301c030100c51400020910740c003141026141c1c042040001000750083c1141380d100031b0a180f000a111501c11f06a0340714803410140641d05540d41850000c405800039a1a03282c05070080d40030790600c6100714251f03240014540c0d080e0084404400001d4800c40c3ca012010503150704a2168084c4d2000030f03200d005000c5507003841008000ca04210555004c600707400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 260581654 1250 260580404 260580413
    0xc0703080307170c2b020c0a0b01170d0509040e030d060504140708162a14121801030e0d050d06060509300d0c0b0603030304050a080c01060f0909 64
    0x8240609071601c00c0e0303285003048600b02220096a8910100c1001042c145c81d084841003942007414070040307681840810341c080c1e000000584440140c0c8070301e0100c0000e90b21810803001240d003900d88a90140e100307a0448d215a48500c01501d142c030000303040482d4480c0014015801d41d04901c2c1d4001c45140c1e43d41c0e0801492810340148125860b1030110b20089040a4038006e00f50780300106012001003005001030074461103111050761510009003202e803000f05a4509028503030740d00f081134076074150b05030b503420645102003540e681e03002d1000b18043c03030100144106502e60030700d8500c05040c59542c081d00340030b980041c0203181c4540d0355a075810341d617101d41c0d1307400b801155890380155080000c280010001d507107400300103142c26490b108051a00e06000b40c070f1306841c62003a100c0d184941c0514001d4007a669001441d50b100c040c40340d030701000a41d4544091507902d000c00c55015201c0e9001e00010b2000c039104070002c0c6900500c80380080f07116034440d00302c80701c00e669507400040741d56074942c080d00a01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 260582904 1250 260581654 260581667
    0xc06030402030c0d030509030d23042102060909070203071704080c0108180105100603110a120902030f0712110907090e10080a1a0a0c081503070e04060501050a08030703080114060c0703080307 84
    0x15400980b80b07600b0300f8140454015504058280d02900050010463302555a11401c0c0ea10420004050005034580354070000c2d00c90b005540219181240b101c1c482d4001c9030b0240644068444010051090300e0860b070045404400140c5540d103401c404504040038540c003801864841e800140600800d946000740c01070031906018182161800300b408050081503110440307100d4800c00d0a07002c1140312140c00040d0410750110070401c0e0b10f00c1940000038804081b4130b07114012a028440c009036411f0010280030040030116032003000105036000920900b0354583c443c40e00804111004240c03544c5580307150b881e00014150071345010f00c1407014001039038084c1c2c135800e0340584000d805020110403007501074800a0040e01441c200f0343d001c6102c0c074603510100a800e0080c801100502441d08041c14001d004000078000eaa0003414503120105030b0f114000210346440f9407641e0740c442680c2c43d0080d074091419600c2100c035031080040040e48045082044144080c40c010101981e0b20308ac030400240c1f64 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 260584154 1250 260582904 260582957
    0x7050606010f02030406020d030c020309030703050c0109140a1208070b010e0a0f140402040b0f0402032505040b09100e0325050319120c0f0b090c06030402030c0d030509030d 76
    0x46600170001031120b554003140d0418004610704003c80c01082490b8141d041d8010003842d1501849400070000501c0300c0054007200220081e26141e840c1c039110326400c03401042900f5100d030030081801080005840d40c940003254a8040c11480d0b081400a55521000900c207034480f0f51804180350511166480512a103200300300c01c07020800002e000907841d101420340082001e0700c20350341c400d041ea4581d02e030030090102416005004541d40c0c07601c016080039450700702090341d511000b9041c40c040014019011a0709950000c09210b00b4030340c0082c108910f81503000708a4080291000e0b4500140d101041402c2403009814482c05100e000c221103801e1840c11644034500ca9400070030a80024070441844503a070390740100300c41e43c0a499082c000c1d11005080d040080500700d2183c080b0041c013190a9550380241c001c0350a80340800003020800c02c042c00255000f82d80754000703894100492030020712040005210342403040c02e06040200090070050260b5012011410080b0b50440155040c0c410307243c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 260585404 1250 260584154 260584157
    0x8040302030d2d09080d0201050405160e0a02030a140a0e0c0103060b09040e1c050c150714090a1802090102070b4009021815030a0c0e0607050606010f 66
    0x1c0d02a00038042940300410a22000e240741410700910f60b03d58070415540c000317403840c1e8044900301a4203200c024000e0408550a031068041c0e2200c00460891020a400071100180c03200d4056440d03040d034510083d800505071082c0c866484900003520151030064602c11011107c0c0040c91100419100f070514010b2040c1c213041514040c028041c0701c00e110240d038a003070415a000211140c1d80c0d40201d01c0c0c40045e41541c040511b41e568550f0042d94007200400da446804015548031003034494950f84080c405a400707001150300581f0194449440f5006070410010007003440986540e9003412800c03207050441c84c3c041c12900050f1000003542c04102000041c94608821407920200618400070701d240a50215224010b840c05101d1a0a15141d0f0161081d40040444c1880b991a00102c2c001d61140a64100040c6810b41e8407481c2d141c070b001320b0019111a20201407440d0b6035640018014140001c1706000e01081d0354079603800d512044050010305124000904172401c014001424960380710307421030b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 260586654 1250 260585404 260585417
    0xd030b1206060307060c060905150103150b010c30180b070b0408070201020f030c0d080a0c09030209090304030f0c05010201110a021009020d1b060e0406030b040f020f06030408040302030d 82
    0x182c2d407000901c000440340c180c07070008174580581c9840c902034081c9a2010348544a4621507840c481c81c00000d01c1c0c100e070f114074240c00040c400c00c000301c3d050b95a1b4202c5079000c07410468106010035840c1c82800604000f190005850441c0400304144580c2260300000000b410200e41c81594402c044520000d00002d103201428192070381c1d181082c803540284001c000e08070200c2c0510459000b004020384805826003500e44030a1034054069446050714402800a00c544001c21088803840c840d495a031105580d90400290968081c0314000304094401815403104001c00404551803080c0c01c1c1815204240c085155803809000a094600385000341441d81d40030041500326030340006004050000040010540c02e2440c00001c101003030310040a010003000c2d00c400b400607502001454151481a01d03148075000100e81030004803032840c0400bd1403a4481c0010070041048000344200403072000b058000b5072450700c400b02d40d181c0c0060b078040310000408a020301c110300e010700103891400c00e18075291 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 260587904 1250 260586654 260586661
    0x906180111161106030f0a0b040b09040330020702040507030c09170109080d0203041208060a090e030c030a0809010f0203161209050f070e0606030108060f070509030d030b1206 77
    0x41001c1c8101e00b03042c4080c07907650140301c041002e00720500041c0395001303000e242c5038940b0f900c0e503400500c13040b995031407164506241140b251403c1d00c00d8640ea03042c0501190095910344da07064401c8038240100d041d00c09260303401554010b440c214a58012005034002585030070039441844240c40010301070034145818a50400215a4407080540c111031902c1c503480d0190120040741c42c01000c3c0510301800004002910400c0b0710104c0e001107000794800c0f1465094442da07000c040355213160070f4444e01d030b12410f03890042129842e260044441d00d1a400c0650380390564080310700d455640a49000c8021581400030003030318010a01c20300d00c0e00c054034802940f451a01c892200814459021b201060103450407159030300340d1455002032940c030b50000484002c02c0400307282e6a601e10b00c3d07104441050385100c0001d0303824100281564100d6102600903c1c10b501e440c04880e081d042c000b00311070204081445950b10594003040205046422520300040200703980040c0030000c404115880d607079070b0205092 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 260589154 1250 260587904 260587931
    0xc0303230403050f0f0f070b0a2a020712140609010504030e090901140a0605030c01030e100b060f03010303090f060f021c030e01060b12070804030e0d06060305030309061801 76
    0x1e500540c545082030b603c9a9101e041843c500a8140030650424081081202d0b00075180c0103102d0b4038081d604010f015900d0665500a907208501240004850b000c030144852615030b071160210a524015500015250741102450b41002d1005840303540345035407108200c200511519400004050084c08070b81381035200500100740c03242259000312615400034103003600c02e60001b8586000361080c5072050030650003240c064499409030758841e010b008000419580640f1034011410031060142c1507001000b08c1003002042501803c07500080104007400c5200c0e0294004c41c00b80d03100f6158000080e0a141e1050000d09082d0440c03000e028001d80d4003400603400141c083c1c1c40c6841c8a03a07203400780300107060480c0a401364128400c510f40c00d102d40880c0300722124006c3d02502d50a0070829400b683c582c80c040701e80807000d40300540450b01c8c0038012012428844007a01185000c0c600c0400c20564039500c047c6164000c0700c4484554010005008980038441c1104c103407034801030000c1c04048000580c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 260590404 1250 260589154 260589221
    0x5011703041208160c03020411130b0c01020f0a050a0215060d140106080304060314060d0f030e150703020604030908060c04090f0f0903020d1202030c0304030507020a03050d0c0303 79
    0x1984884100d542d81210811034510100c40300e9844405859241180360315192409140c180400c0744500c2c04c01c1286202c0d081110240c40e4803009a03921144414507114444009070312101c80e00c1aa0b5400300001031200200100510300c3d1551503540c6540c66200300c030700a08207000b00c004401205010000d0018603910810390015040e00081031b1007000200c100350764010802c580c02038201e800080340014070560540d00c0003a80e5844a80c108049035038003400c01400586006000300070b0203c449850b4007180c070a900e11080c010002e00245148903131407016503241d400446003100140c2c032090810040691001640c8018001030700280441c0c140010107141d58021406551081681c44240c001d440c2401d4020701118145421304100b16801c03814000c0d01c401401c10003602144010120f182c0b0304a50b80b08480c03040c60324100c8207040d178071030741e40807a096400380c07500340d91090300a40048003040701440148034031192900d5908055110340b40207010390b0a0030040d00424843c5152152000d6181203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 260591654 1250 260590404 260590409
    0xc070e13140601030b042013020a0908030309070b0a030902040617010b030f030d2403051e0a030530070f170f0117120f040306060806090a020f0d0f060209040501170304 74
    0x113411460040520500c0e6111061114947c3e501c04000140c0d0003000325a980141100116a6641e031b00c56900c8202c483d5882c40180c600304450750200400f08021714910f800b410420788107140108100340d664002401b5184a074101000307010602d000701c0382c03580c000d200b0485c081e482603010341118140641e41c603450740941c0410541c170f01d071a2400307201c40c42400890022900c103215007c00700e050b140d041c03540d41e980c0c04003481c24000f82014060103035840001005503140c0d41c56a500392414440b1100c0c00040744044104000d11680601d04099907100c81001e144241040d540d185070740740c141c00700100759000d8a8540401003007010140303d811365038032811a0640d8041c0c1c1000401441284480c0e2520071154916254250301040c8407c2070103080d8028000c8034014041407101507103c280c0680c44d04000d032545000360340201841c00050811020381d52451030000e1010204d400d0a84035200032031030708503044841541c000b8080d50b091505201d02409000b540090000e8142da02c242581c0e03038841c60 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 260592904 1250 260591654 260591663
    0xd0e060306030f0a111206040b0403033204020102100902090105040b0612010807030302070f0e0a0b011e12110301080303190219320403080c070e13140601030b04 71
    0x20700341e803800c01524000603403a0701120004403543c100880c101c000c2c3d050b9507104840410240c00c12007400a0b0031030085800c0380d86040217859a03a400e41c000d00b10746e0b851600d820080059080c0002100d26203c6911005044464091400740300081c00c200f808410b0b4120706242401a00168560341681c40c192281074030002480000503000030718601403c0f00c104440070b110000411300c3c550100d09402241e00c6502199441034488007141140c141c1030180c454518603240015080c00015007082c519a032040c100324200103807011381c0070903200301c0c244500d011494082ea04901085070348200d59a905010b810181954184a205522403001609010280c0095201c034166001c4507811585400407c903c0c0703000c0ea0740c0c42100600514540081042c90803401190141c0320080c0072050441000861940c074507150555840007003640190052101078840d003000854080c402c0c0646a000d49000c41d0520581d04107840d0007604282141e09030401508068010400282e50070070035600241d02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 260594154 1250 260592904 260592907
    0x10b1303080c010f060b2122032d09050d0503030705031b0d060501081014060a1404090516020c0d020f061207030b040f090c0618090f0615020d0e06 65
    0x10010014054652200b41304111840c0c420300160084800005102c8041c84028042404200401805a040f800c80300a0400c010611500300000c2c000c8882e83c00c0c2500c60b081402c0d015000c41d880404900d0748102178440402181d40c0001020f402c404000300070642242d407845180416941e16440303010140150090110100103d0924080184034005030f8021030071407500c4924000c99900a802c443c480c05021500e80f4020810310103600d0440c0c0f09480c2a100d5508100060303100348036040c1c0c405251101082824101d52500d2054180104014003690401060070704000348586841d510001c0000e06651103000074006079150400782504080e01151501049100c070b4000c110241f003034440c401c030320708980c00400c00c210342c04d64080541034500340e134100a00700380c9400324008c9920511000e0304c0d00188c42c0040091900c00d01268000c50035240d0a20102603950310a5003e40700034484001c005516241f0600c4103901c0c00550f8201c81026100034041c4040d405405400320481c00307884c5020303100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 260595404 1250 260594154 260594167
    0x60c040311011202070812010902091509060c030301080a051203040b0105091b030907030c120503030610030212090705100807050d0c03110a0504080111090105160215030403050c06010b130308 84
    0x5120070114160f0b002d000390365a0b40c2c80d00d000103040d0b2001d06651594003107c5c0003c9549020b620a13900310302c2001e0019110f5071814075500c032843e0808802c0c954042c00411902c80c80c080140b010314000d203d4a0001c1000164038945a400d00800400c0500b0b088410b00400008c960701140c1c2504460055562240d50b485000401c0c0b2488003a6000114021002052054081c030004040c400c1ba4041d5002805054075031454003581c0684900280185c0d0050002c6035071131400340b02d070030040c1c0340b5400d0051800c5000310103021025030850714205c080e041070300d0030005810107926280e00c4c4441481c2c00324040c0340c9210090954004d2417003002c0d005995000c010301c080e000345d000303000e04184112460303103900004d18000e10a9000b03000b0840594204800300045440c04400d540c50b902c8140c580300e040804000d8568200480c0000c1a81c0c030860305480f00f10038121001c0214052070195a40e00e41d9081d400f2105c6192000c1030f4005012804d082000c0580b0501401d030342d01c203582e0700000c8141e50300c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 260596654 1250 260595404 260595407
    0x1a09040609050313080c0f030313060503061c0302030c060c030403093c0302040b0f180912040303030c17040c120507090c180603050f13050307060504050c0111060c04031101 76
    0x5104130100100512030022484c00c500061000800e60100c802a424011100130316880c0c0c0100e01101407014100c007014403181e40150042e650041c1c020384a01d0303d5410388084d0a250030000342c8240c4c05a080001c03010300216081c0f02c0c41d584600104c03000c0749581041d68004000550f144900711a0407405480198111640040324201034846a44003100482862618036202038900c000c902c200e00d41000d058841c2440003140c8150000144480c0c0c65030340041c0f8003107080c6801007a40311640564400d1404000b00d180282c806940a96400a5059100b150103031045814516110713080f03050302c00304000500300700000e03005c0d2600c42d20130480c1041e8074600540782c5501c54001045040c14030204a02165010707c20280391921090390400c0e15580780b1041e01141c000f0340e60541c802c1c40e0000000d1080312551024901540b0a001301c0e4500704850f1107101c101c9400b640c0441c0e40e50030840c46104503603846801606c2c004a10b030060b0059003000384000105205500c1b006011540842c10112a603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 260597904 1250 260596654 260596657
    0x10170c0f040b040f061805220c030c08010b040509190611130e06040615140a050403150e101109040c030b0303040308030f15101d04060b07061a090406090503 69
    0x20031000d807042c45120681a901d102a0005001d0125681c403403e404406e0104030707020303050042d10010040c2008a90040b24448100034900741510304110f1240d0002c001492484800c0c02410020000140d21050004010a4400c007802c1107180b50700c4040e500740740c4102c2060212034982d015000040540c00b200c40f04040d8016070000c500400c40358079002603c0420071049600c140022102001103a440302c0050711141c030b02e0510840020501030440002c00740c5280100100c40007401c105007002d990f0b60b01d03001108108420340380029140c0011001c1c60804102e400e983c403c040c9024804140c0307510346640350303005078120548640c1e203412409101900030390000800e810042e06607680c40c0d88a0a045510354001c1e030b08d401500440000244200c03861030310f980c541c1d031002040b400ca8000700100c00c60f600750b40500c1d500303061682d040d001460740c0d40d5846040020300800503140d0700e07101c460600c842210070000d55648074420300d421001c1c0720340c0c4042c601c40d4030941c4020300041032845401c100d481c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 260599154 1250 260597904 260597921
    0x4051008070603060905160c0816080318070501050408190206090d030f170f0123041d0c0603040f0f03030e12040918020102120c0109081210170c0f04 66
    0x80d4090340902040c0c00b903150300b090b01940e079650310a10290701c4840d041a244060350340031100003043c00040e000015107c17402084100d090051070500500b241e00c03400555070050301d450407280f846020b100f07507040f014030a8070010708090030180d0400d80792080c540c0e140c4d440540804203c01d402070201c0110740d12201a01c0f00340401803c25801d808141c500038059466080d50f51000c2200c550302100d4100c00071020900c11031001d0104442c0e40d01c1c0c4422251402c4030307031156043c1050901500c2c051740e2254450f840c1000c006001d1025080e01600d005070402204403180c03030049808108000c04962541404223019610616012190800d42801c9008040c0c003004c41d9118060400402c10f20f021440142c002c0d05d8040008000c0c100401602141010020000030f0158110304502d09041042c0c6019100c40c004480021a003140d00d56070300700300c680c824600310032501c1312002401010060dd0b41214094680c800303c0c160b40e442030403032603175035404104103680c800c41c070398801d07010291155040881d0b03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 260600404 1250 260599154 260599169
    0x140d05030f0403140a020a1403010f0e06060a06110304170313030b0121020f01050d0902060c10060501090b070222090c0303020d0212040e1005030604030e10050c0c040510 75
    0x49a1107500c0c1c44504680c4688400d46190b4540f0300c80101d403580120f050680c1990081141c14210b1400c03103406c400c112070000c44e50340355590300c0309066010380303a00503e02803e488402401d8240750480c200310701d00c542c5800400030000c840c3c2280f0326648000085030107031361804040320503007030402e082e4501c2d40c8184450309a07200240c49000040010030030100381600c082003141000101da0707144c40e444007681c1010103940000c18194680b41d07540501c3c020052009104d4000c02d00e2031207a00410196401052101484d60140704030010740d031058410300340a02402d04e4002e4202e441e02c120380c1d89030301030000041c0c8a080d201c03040d4415200035074643c094005240500384486019410070186114292000394054003e10b110302e01c6d040d1005c43c00401c8001c98810b840d040c54184030025a9584004280e044100c0038603002190540c0c040014034840da2007aa5031880b06c0040e2028021800350300d0405105124050009403510000412541300c9100280d4001032555120005d80b2140a9298050f50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 260601654 1250 260600404 260600407
    0x7020607150905010f09050318120a0b09010b01020c150310050901080d080a02032802090904150605010c02010f0509031f0c0815060703080c0c011802010f0c0309140d0503 75
    0x41c0c4688403038201000c2d03103008600802000007441d584005680700034400901c1030b002004044031010134908403120511010700700705061900c0809062424201d008280c640040f09810841e090a00340111099000700784040c2c44124071840101d402c41040d0301c1060205440800000c41e4100a021080010180104844c80c43d50350380c0c652a8035404908004d1000500d2440043c1c00419035000b120b0080c0307400351015a00080c18801c403e20703810001c0c1c52004d8a60204000309980d07488080c4180180c0c055240441d400000840e288119811a03025030b0500881104510241c0e804c400021160512400d019a81d1f002420002703003441240002030054070184d071a03050300700301242d01a01d120886510340b004662202c092038030064802d103202980c440d40800130000001d200304425500f018403c0405401c1c44050403c090940b0025086590421f2180c40e0100956038401240c0350b031507450342402100d85042e031700c00400702d00e040d0240d00100550030a030607002d91140030001d445142c100c01581d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 260602904 1250 260601654 260601683
    0x3090a06090b0a1b0207090e10050f01180615050a230307020d030203090703170d02070b060117151c05030403110a150e090a02070501050a06030312091707020607 71
    0x1900781c020b881d5556450b152413440c11500d800c250741c114410310160010b0242c1864055902e01516641a0110403801890b580c007400f940301d406803078042d80034542242071a40c10306c85003803805c48450101036aa1420403800300404200700300c40700801c5125103802d55a4082502041c0c0300c02150500d00c456421070115202c001290080245000d26103e40c00c0d5075640c0b1a00c01c08030164001951a5001034008050410000309810f41d80050b8004201403182494000f629070801c83c0c010f81c0e01598801e00990400a89613442050031000013004540403100703040c2911100c191112256101d8000c4407a0310402d250b03c0994010034040300e60000c00c480c0c1d106d41324a41080c3c080041840140110108100031404030030284000c41c000989c2d50305d131b40011552804000d414030300035204c150000d03070800149010800a02555104903c060b40200d41c0b5803031460014212075038080303d6120b0340d00c0c1101ca10300107101d03560108420100e90fa00e840d20b9280c00d0000415610900c00700030144081009130 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 260604154 1250 260602904 260602913
    0x90907020d0e0a050a090504170301030c1404141321050d0c11280204061413020408030403030e060904020c06090c10050405060313080a020c130b01050a0503090a0609 73
    0x11940d5000d1680c1e602d00c514100c0418050815010701426a00500346401880b180b40e4070383c0300c0350307000303008083c0b5813615603a8000480003540203800582d080d82604000340510081c4443d5240c00380340c1a00c04120f414101c901b40f240504000c0c2440020302400841c0f1418802200c541943c0b190054a080710302034589040982150b0144091041190401601300030582c021810403d11100010107400704046e941010000d00b0561940000f01207282d480d0301000d40c0b610b2246c1c80241c81c44a105ca580b145854041000d500c03c026010044103004000c180701102707012090340c0c22a0343c9401d0100000700c0c3e0a0018101c1d004124a0981103840402e80404241000545a0068901105868120011006201c04080d48401d070801040c2e00700800c21187c1000e800842c3e0080600c1801001a90555030b000502e50029a4620060380460041c0060346055000450011030207035007004500d01010019015000711011403050282c04000242d101209022081a1581c004c804000d12717001c0f03150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 260605404 1250 260604154 260604163
    0xd02040f0503030705190c15050d0e0106300215130803070206160311010614040c0315060509061207021b09061806030709020310061716031109090702 66
    0x151406440c01003000100c6040c007004903220540c008002d452035110b120311100d100b03400e800c1d0444148510340e2002600c50a0706c5041002c051240ea240c0d5658001080b002c81552203840003c1e0040c1d14025003044054140307520b041406104440c0741a0b003202d100c00420080107180000ba400404038408023244003980300090200c1107100415134000c41c0c56881c01e5550740500100250490b07400c00c444105412105038001000380720f4a4007071003044000c250a801c1d209641d0124440c3e072403159804240307152900a8044142e11460100016410320b25900942911440343c3c00500c5000034010100341c8a64048684080030410244424184074000944d2072524000c2441c1d2405c1d0b802107509540fa201d10341601a03500145a2004d013454003008104401014240c070b0350620505100140c150b10340d001a61142d00c41690b00340c0014606403001d0710040038081d142060036100e0302004000c03042568444041c12051600107070390b104410019a45201d00c0d0921030b8811002810000e81650009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 260606654 1250 260605404 260605409
    0x7030204080a1101020d17040b15100806030607050901140c0f0312010602010f020903030306131d060f100e0112020621070e03010510060c0f0606080a29040303020a02120d0204 77
    0xb0300311442503246c1981214502a201c00ca03074840e954413400300303021940304446190455081e402489441c40a00001600108952800c501040c4600e040007401e00e4280802e075800b0380d803410328520b03010703007000001c048000f80402d1a02d130180c042100002450100440a0410400d10440e6a01c00c1001504840000d0900c00d07c8015030802d000100418094001e0311003050001c1c000b182140c4a441c100052034074200d82c4400f002d135030b602c0c1c802180c022072041040400c80881c0609540e003032485804002c000010120a418010309104100c510301261805044802900d0b501e10818514400640a40700d170340f848100b00120401c0f1100ba5580101d01d4900606440c6c4070384103c000d10005050980340d00316000b10012090a8042018034000c407003c1d031103148034500c0070708030701c3c429582d24044a2031074204050350f50000c42018100a1510200d0740c0030a414604100c6c2440104103d4403000c900a100604050b00441c03030080d44c0b8002c1103111b1040104600d22a183d4103c0d807040d1009401c0391 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 260607904 1250 260606654 260606657
    0x4c03050706030b15030403030b1c02030606030a050a02010f1b080306120a030e0f061303050a021302130302011419030e1504050a0605060a0308030106030203070807021b040507030204080a1101 84
    0x209001501d58003910641c85440005800051800e41c020007110340c0d80c000501c1903040c50b440713000c980207035a210240ca0500101c007201030050b540c1240103040c540381d40200074078001d0f4405201500414400211051944c0d42460003410703085a00c042102c2c00c06940ca45012040750042296042000c1d440255208081c1541c2085d01c0c04080c403803166403042d80c0302d0041c0100710201200c1c201401d107003000380c0e4540006401c80d03203440607405091910003041d034400e5480c1c0d041f468030b0390110b20b0440c101802c2a01001c070294240300510720260340325521880001e040c801214001003c944d200800e540c0c0c201c12210341e16220020020700034000d8400340e0620000c90080d002c00c00b00d4101890101e600968000d4002d090b03460842e030381d22008280c05443d80b544101000000800100001c0085003e80327250395000d0380300e040c8a10b000e098144064941d406640103801300d03030048103281e4003401c940346084070046104c0e1100c8600390024031658001c00580d0041c01118014170988882c05a21080e00f03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 260609154 1250 260607904 260607913
    0x160909020c06160c1218081b0108010b1e16120201050f0a0624031e1a0604051008040213060b040f060f020307060b0105090a06030516084c0305 63
    0xa03c5801c84681000040040a20b0007a51046080c18810007940c285103290700b8001e80c1c800d4035074005d00d03c1d22000e0b0020b80b0300c01d80c00000160842d41d1181c1d2690041c144000c5490a103401c014040f00c80b80c40c90302903050b0101000c02c0318441d1201c2c0c800c095070a1500f124070107085000489009018050840355400c20105180101c1c00441082c4900030445521548030070b90700182146c0840140c004821200400d522080500107203203a403904000d00d14941c41001440c258692034840d2030084117905144240b509200800c450b844c1e02e031425100701680c3c0740c401280c0c6e0b0f40303200090401e22442e03903d0560518101c00486c1b5142082c000f0000d0b00e241414031000d403681c03900304481031458010b43e100160024044440029043d0700281d504c8901410082c1c1800b43c0b81c0003145180ca12a8812000a41c445082c80060001688082c210511510307180d07229181c4200c2d07000c9000800748090a850180c4030b0000d40ea200a5108030f07043c2181c040c0c416400000c0688400c812a0b50b901054030103016 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 260610404 1250 260609154 260609191
    0x90c030601211407080627070308120712060602011a0613030b071e09230303030c0c10020c03130918080d0f0903120b030102070803160909020c06 64
    0x701144810104100e6260001242c541e52000c000c03107600d002c1510944140b15010030784070390900c0007610a60303014074a140c94117034039041e03404401001544040950001303001400441c0010f81140c044c0c840040b043c1148c0c1d150044100e030f12035174000032143c4003031901c0000b04002d075040d00030000c103008078100130101c5201401006450310a40400340d1002202a6003000040e5006824aa02031490300b408215241208025181008003041080004103a00c2080c05074400e080c0305c00c4074808505002e040451699400b1070794034440580000b030160408038a038200240104038680720344203409401d548521030444059501d81202d1281080200320140c0810300200a04c144042c9102e210750720200050140c40b60f0215901c407410805540e603c44901082d0700045005403c3e030701d8404e0303940001c0e4030700d2448030030203c50940c401c079486640100114030202c1c40c04020b481c3c20aa40c50158261ba00c04404c00344c1b036108056000030380007400070070084030012010607003510442c821003034280110b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 260611510 1106 260610404 260610419
    0x7021002040e0105120d0e011101020c10020405120303070e0f060d05130302121201180204050307060c0b0601080906070c1b0e04140c01090303051c05090c030601 71
    0x41c400c40041259051200c07150740d0695621001d403801b41896440109603108600d01181000884045600c54500030350442d00508004000c91342d140305001d4446020350024450684100c50025082c4d043d0b417400f0040b6481480c1554500e034101e00500100400340d501a404075400c03003414030803501e05640e40c2c0b240e24004c0981040f0b040b40c4070502d180c000d01c2d040d000b418682841a041c81503e001c1d10f440c1c604075044d01c0e0520312010009903400c01a07c001d0045501c00f580c07603c10f241c000218650002c0180d0070440c00b4a6006856503181c100649805005841c0d903072580c0d02c810f00040080303204441401c541440352950090307038180c083c402e80441c01c1980144002400c070300180810480c6107040c000744000f40d0000b070114040150000382004c81a0722018042c000d0000b4024a200810302c5042506c07000c8003c108800d00300803452940e12846000c13402d00034480c1800200f04030 = true := by decide +kernel

theorem cover : BRFrame.Cov 260431654 260611510 := by
  have h0 := BRFrame.cov_init 260431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 260431654 ≤ n) (h2 : n < 260611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
