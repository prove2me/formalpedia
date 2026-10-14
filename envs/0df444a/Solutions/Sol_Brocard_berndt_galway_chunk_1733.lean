-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1733
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:28:33.590473+00:00
-- url     : https://prove2.me/submissions/7feb3c1e-64a8-43fd-a4b4-befcac16a79e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 311510791 ≤ n < 311690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 311512041 1250 311510791 311510821
    0x80a080306010509042405190602031603170f1e07020a030825030501180903020a030f2f0616020c040504050a0c0609180b010804032607090815 63
    0x1d1410808005210107032035641e50000640175100041440700c14103504110001004940300310360103082003d510901c051000058441101c8480d005107150070114010f280c500c460304c003011800d02003110150b040c203049610583e40315464214010400b0b0403d0804086460101c0c410006108024002c0014a40e0701041c000c2c03605070f05050041c0da81d00c6a102c47c4011024002e000d81d001e10001d0001c01034664180c00c528104c444200d03280b00d003c0106482c0006a80c07004030007030701503440041b480300042c0c403070303ea00c3e0910700144c0790003400780c0400050a640c4104241040c42c181c064408900b09064041c0892034200010f06110b500c090841c69000e91100c604803610b03403040e0380d1340b4005014400c0a0115100d40d945c0092004201d0b0b8036241e001c0c00700d1046000d1b07219411003152090360340142d203114042c202c88050b1102c100c01d9440383c4d01180c0c41340d000360b08600030812203400d42021141226120740140c8058666002281c14414031920b800d501c41c1050841201c0e040900613541000e03031003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 311513291 1250 311512041 311512051
    0x3200a0501031a03120901080108060c1204050f0604061e060f18060302030613051c1d030a06060b03011e050604030303050912070b0106090b0310090218040f0203070306080a0803 78
    0x3000c00d69900016503c03a0703604440611a03010300a0540d40401d10070b00400038591100d09032150491a40c944104517034803c1c0032580d2040c0c1150806c60320030389281059240b40d12512820468847c4c568a622103820b156040e60216034a648904ca9450400310003891407014612000301085180e1a1000c4624800c2652041c1e81c5240400c40c0350721002d0087d50400e80245401170110dc0660070200d488005c61f00b481c0794140d40d507000e002080c801d280c080c56151010148550385291650300e4952610000b540c41e059500d0303051103074035a0440002c0e020300800b401401c00b079001649a41c0b40c0420500b08204d02050115148400c00040c030040ea101c0301a58240e940515000941e95260030105142c200c184080c00d120060118140080058001095040c1c0d4816510b119903240c3d0354414861600055038040b4101e10050028411043e09902400b80000c079172003642ea68611800226080700ca40400128211760004100000260140034000050041a0041045040640b00e0602030300020345 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 311514541 1250 311513291 311513297
    0x2040f050f180703080708030f010605030115080a0905191202010e03040905040309050603040803010801110306030c0d03020c1207050307050f0306042414070810150c0203070f0b0403200a0501 84
    0x150024802d041100c0005141d01050340b80c2d689a45050500603600110394010701c844c10600003244840c4200152070407101071040b50f90202000d0310060720104c00c01008c441001d9590095000452001c00c440c4440d82001040802601340b50b0030840d0780e03508014030312401c0d6811f01030300d012500000011142195403d400000f040d0b155071070f01700c0d100407241d440540c1c03000c1d0100621060011a03402541210b600400070400003400c10100002c0d400112600d0768588c024503082c0c2036a060a48a051909100f8415102c0c0303e090900083d10f039114106008199a00c4018144001c1c1800c001c00005040100c034140b5004202c240001d91380c2100510041030004c546170034a012030703107040e4818100c619074501032066200d00040100c0004003100c030440003400800200e14078407080b81c0c004098690a00c040c1005100c00b89064450788041c5000300d801d803007540d10003d00c2c100c0e401c01d080301502c02c3c2c00120307076900e01d9818129100e034000c0b101180100d08008030164103507604101041103d0303080c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 311515791 1250 311514541 311514571
    0x80a05060913140102120103031716170603121602040b03030c071511070603091e051b030312011214030c060106030e011404030906200304052b0f02040f050f 69
    0x210307941d40a8090850a007021546d4a00003008141e00101c0c09801001c07081e01260503a5200001210424004080039020600300401c8050040c40e0801c401d500c01005411220300c812032030341c0682143e01c11844004001e52842c3c0e00000c602d0715001d0314000700c00840085040074440c0404030380742c18441c86002c01108003c205088450f000d56a01c88480840200b42d420a5641e000c015016002d090400c50709181e07540214400d0300303030002e00c840c01c0c1c9400070002c1968076040d10210b0710440ca401c881030f034103110902c039408070390fa100c40000d4041d107000c0806101080341c9103070602000000c1c08101d2a82e4006004400d03400e040001e40b541114094036020626480e17628103680100409102c506005464104101c01d06802514000803640326556500140191503c40b02d0074421191500c19103410402c403c00507442c1221000d080b199084460702c6546a00c201c601c058040d40c10021659142c564014070190f280510034041103d144840034032452801c4500e9402d520001000e0341a042011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 311517041 1250 311515791 311515823
    0x2109030b1f0b030f040b0a022d0412050304050f01110d030b010c06020d1a0117011a09090f01030302060a090f0210140f030603070609182a080a05060913 67
    0xa403546400400036802c040356a401e2507070b281e40c18400d04403030580e5610702210120303140c0107881c0f086584003110010520009030032003070703148060041890701190a282c28040822820001c1104103142071150004554403031806013840aa081e406440354140140280303184010200803405031070041075883c0000b14000d04200503200581300341005407185201260400180100e98444a5a00102c00c0c252001b94401f00044417084040440c9a800d902c4002c010004030358250290001e48108801c014244000500401c40003070707084413800401c0e6400c1004009050301440a160008001340c4180301c1000c00b61928040809419002409000c2500d1041d0960388101360b070002e07034100180f015a50f0b00e0440030b0b0032206d400a641c0603200c1d000b000c00009000340282140703003c89001c03c1052121844180f400002401c1603031403c1d054000280210068044900160000803080e03194130b201818003c0400044840080c00d840c000e40c144420301000c91b1100d4030f0710303906941c080043c0c1c580c0440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 311518291 1250 311517041 311517091
    0x12080a0c060906020304020406050a0f0b090d02061c050114090412030b040204120203060105040e06061009030203030d051f05131a030f1f020406120221042109030b 72
    0x368603029014510744400c80042162030b400450049008035024040d40c2d03101d80c100000401c2c50311503144001c404c0d980070000f070b400030300181c584000300504420b01a600798010503c1503000b1406040c0084803540010b09242040c4100e50250070b140905807003034200440030800303203000580007400800070f010042c00100d209401071001c140c0c0103001076440d62f5680c485881d03d140701e00409c0744640501030010500382828880d000c2c10344170030302c0148142d031600f409104500341503000c144204981403d000c00941c40410051070304226004e4006042d181155248412087c843d1041e0000007480c0410002a07032070b00f00340d903a044206180001d8124001d1005848072000645942c0c140c01068520812884c001c983c4400175040399840d243d00c02c40d59064001203100300d00559010070718684406010802070741c05000307200c69036009200c00c0c22000c42c540030301e044200c0c1d00300c07010090075030807810310001c01000980707030582420000e4a0a055580d03400300950028645860813204100d9010343d005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 311519541 1250 311518291 311518307
    0x3010305030739090c0507050703020f130905210a120c0c02040608010912020303160806012c01021002070f0602030603030f07050c01020706090302030a061508010204270612080a 78
    0x810b400102c45200d424901d01c1d801060b241c410000078524002d41d4517a614001e8088840459225010f49800d40c20b41c1e081295600d61006070a403c0b41c25540c801100440d02d225102c4a01d006000410a456141c064030b610315848040b43d41c1018001d0086a0f1000e400c00180c10701c1c411510340c003140d00e00008004580401104a0184d071090914000080380e02c41075120400761380c060500900601c3c000300c0244c0c1d1340e00c8240d0350509103802d41c2d0b02045080f40f04003020754018005152580b551440010160329180f103070101e500841442c0e070400034030340da010000034180076050381e4150f0421f00703c1e482d0001c0304556030002030461500000002c400d5074060040fa0445050188607503252041c500b44035549980c0b042c1c0d4103000d841040303070225406000300c40380d004880d4020002d0801c01d10581d910b034090202030b03040e030192071440030000c100700d4403c0c000340c0090401d041d4041c2118404900d81e130b21075001c01e915620114909541400000c1c105058008101c2d0041c44182da2a18030030000c0318014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 311520791 1250 311519541 311519603
    0x102101d030f04090b09010503030a0e030a120f110106140103050a0204030b090d090909200109050306070c02130b090c0f040f0e040506071d130605090106081b030103050307 76
    0x300000803844000300c9040068025031307403401410000e42c007410b01403040703440c42801a01e6159200348020030f5058032811700d8100d460713805001e40d507200045070746088200c1410740031075002c64406580d51800940c0307c03148945407038440000b0302119150200f41000340c146910321504050700c60780060100750494049900555000000301407034908501c8444c3c54501592603000001d005000000c0c80301882c0c001c1541842e0050f03031800d96500e002c540c4006503881002401d0500c40f43e54000601641c0500600c1c2c841d07900740d19224640340d2a0310400050489180b254000140340894581e0350761210803681d0307070001c80c40c400c00d07554200c85189024280070340d610403c8100b130b4011011944c03040e010281c0d80030380e02c40c0f07040b0384803915030600940d248104c00f0200951841c120071203c07024948006014295015007500141944e02d40700800c406500c01d810000200710039034240b001011504507034001d200c41803e081c4c0d08650440e581c40d0307160700c0703201000b41c00c00303200d00007842d0a126200d100782206 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 311522041 1250 311520791 311520793
    0x60a030c02150406050108070f0f26060406020c10151413050c2106090606090d020418030206010510080c1312030201090203160605040506070812040507080c010507020102101d 77
    0x501c0d013858442d02800c024041c1c00c405000383e8400007039203c48540224160b610315084200b0090030100d06011210000028404c0d51900c1010319500c18003c1c0102806140100b0015944407012551b0601e0301201c0c5190a0165150484120030080902e01070002d0702c5c01e0301c184824210602c0e000681080c160344038140d0062402040c4110700c0b1604000f42507040e00e00c520800c65242c41001074070150b0048811640184443c00011250314026005288040009040200c1443d1940105080b100d0040c092200554001040c2c0c00f8142c04020250041204450781d99881c403800100908407039000d45024a92080031a42010801d11a20403a02400000360121030310591410001d01809000d0410b90090203989040011281d1340c1c02c22400ba1242511482c2c9843d1400c0e060120366404440280c44504050116030406e10700458990f0080d4000c40082041a04110100d82050081da52541c10b0260400c40f000050340c0120301c0701c000152000d400669515040341d03041b980c0408650003511 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 311523291 1250 311522041 311522083
    0x30903070b0a06060f0903030e1306080a03030f0b060306030a0305210702030310150c030c1e0b0108100c12020306010c0219080c09072c130501051c02060a030c02 71
    0x20b00d5803a8054000c032441603a403040c0d000c06940054420f082c0600020700043c041c0046102d0f6410181010301a510108100245086e0b60300c1e005424510300400840c0082e80361011600040041d0190081c3c04208440381442c500388000020b030394000241c00101804808030f1582811040d040c40159408960b840a561030300c1c00200003500ea038000c4902410654040d071012a03203020311a01da08440f80d564031560b14401e41e0741c40541f0380c000b10490841c0c078075034807a21901079030100718804207a6074420758180d000765060400103820150010503007007050749803c00f43d5500c41e40c0010b1380f05100c040b03488010380c6e94650324012180d40c010442c0180d009440d2002400000c10951202011070301c50f0b1041e82d10a150000403c1001e00342624200c0006d00b04c64070f01039401e180320034905003141400000b00e80210f5108080f809098004030000301c0300f030782c40d00100002d05010038900c111036004205624140010707030014074a4000e58401104141ea900800000f2034006c10480e0703164841044501c0c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 311524541 1250 311523291 311523301
    0x20613080903030406080106170906360a02130b060405010c050f01060b03100602060108060403032d060e013212010f020d06080f03070308130f0c0602060705090312030903070b 77
    0x6c0a51000c0c400d54001400d4840c0707060354101003030046401403600d44007408072515101551810f00c00d940300d2000d51003090703048890910440800e81407a1f2034284020381400700c034074010050803041c0c0d2034480003002d00f8107510055036540c0703104660644009003040305810140f41003081c6071155403244140c1541c6008804500d011414000c0c42c41940c15104c2100d026071601002c0380c4414080c41401e4260340480c000c03500080c00f0340c01441d0118080e480c0e682454010000450180110840703213400c186e504c0e0000d01c0412840c101650241000410440740c41d82c3d8140310200340103240841c034040081c00a03046511ba968030310b000011100c0c58000f07000409211003540c0c000d52109203100c40041c502440011103100109003000803560a1014500307240c040e0301c1c103584641c4010704042d101805290000c00280a40b00240304442c0a140e15080c070794208400a883c0070000341c42203090000a11803007440340d500181800650400c0540a41c50b41c680d00541072a50040c1c81e0004d2030002c801c030400c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 311525791 1250 311524541 311524547
    0x1202041d060901090c090e0601260106020d030b2206050303040e15040b06031807030b0a1b090b09010c02040b041103090706080f04020f1306080d120606020613080903030406 76
    0x10301528085078900402d90780c80002c0e5007205c84610080000c120440801c1080580508403954040e106045c02903800d01212140641503051101c1000059036210040c00856410003841503000940d04040202200f020005041d8010001a03684000c2801d1052a003154050f000700d0010034020b4200c0c0d4072151541350300c840c0e10404841c03100114001d9116205580f505000e0300d2112040030b40041e00e035880780d940104000700303064802074007485101d40020008101826140c45180745040006d0903004407115032429100440600040041c02e1000b80440f14428085840c030000074201903036440b02c14408140503003900409154040d244c000b000c0354014129008500c02c81c012016140419254030f0159108402a21030140813101403000400505111644000004c030051a9443c0303644107001500a561035900840400c0c1c01948130000b00a070803200d0202c1c03510a804040c042941085002507451000924080090152840540600c001030080340e13008900901034030395880e03c3e88005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 311527041 1250 311525791 311525849
    0x406030b0126190305071109040605150d0804090c020f07060c020a060507170c012406020c030a2d0804030303021201060c050601140f04060e06120a0b0106120204 71
    0xc400d002d407035940000c541e0b80c02142c1500344a806041194200d003458030304581581000781d04840741c00d0714900c4401c041d96142c4006c0d10032440307581e0114191504c440201d1308010040c64a81c0076011b0007011500045100040e501030761050f440010354501082c40491a001919a1015440c05032403c08101c46500c81c0490a420f4004e40d0210314051b0382d40c00484082c031076810003500c0d4451001c0100c14040c001c0c4000c00300c4031612000071400100281001c0c450400040d01c146e050002058100005038042c4001412008210080c19948005440d01d0008102c101e0300da019940120400801403281d6a0780c603150b041e0480c1d40542c940da10780c50094000e600861504e03d03c0d0560000004485102d80380340c00040703a0001c083d00040e460444102542c100e01c0301c92542c030410034801a003168541c0d1040b000103200300b5216440c00e04001050002051958001c101e25421459868000c111850f002c1c904680091400030a2403d0a045283c024019504000030699030040300ca002c2c2d00c00610340c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 311528291 1250 311527041 311527079
    0x3020a080f041d2703031611011a0f01020a0f2d05100b0604080318040204180203041703040804060f050706020a23040f0302090406060308040803040303031a010801140406030b01 78
    0x8590500700c04015010740101d401c00c20400d45d842000040d018503003801e17000c100e9488504100008030060f8031b00a003503607441e00e10007042560300090201c407450302c01100c203100340080c00030300030044241d1110303250303a10646005011081a00c481002104e1400280c080040719080004041210382c6001d0ba16650b0340ca159002003404c116450009151030001c407412101d440e00103600d40f0407050715091b80382c03e40d10203184c0d00ca64240070001e8400c0440488148000701004016130301d10f400d180180c3c020390702c007101000c07032041481080001418441280c090301c00b84d062810300049503000488840c8a0807030020401c90000c07a01200003604014261925002854012003c4d42c031030000540600446c82482e80611100504201504040544a410501500011444d141c89495106095001c4e074080d04455000080c10010326030b0504c01c2960104808000d52203200890300000c0c6600818000d00c40b102c04200004125aa100c1c0d00010003954020030000c015a59518072244010100f00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 311529541 1250 311528291 311528311
    0xf0302060702060f0718050415060206130201090b030c040909060b091303090b0f1902060603160f14030c031e0d050c19020d050105090a0c08010903020a080f041d 71
    0x1001c1203103a030001c90300f0b81c418400320202a0072603807600412696032400114030320501d51410004034103515103018548042c071a804c1c03405c1d20340e80307041070003403070140020700400030170903003d401c0720060380e2265010302101c80d101000c540741d848031407466800380f00d9907010098940c0781c40c154a0405c0705030b0f003091444400445200d205917441492b00040c030420b42c0c10040000d02d022800b030202203004030207800300c0403440700c03174a00f050f00028855104090b0800030300007590001d410040c40340350800840c04011400521440103601c3d00703208540302003082c042c030110403e06155006070b5442c00c0140c041c064400504449000e685505030007510240103c00d0501d50182990890b03416000d901241c282c20150300c0104006112400700003003031540726104070380c04007035049140007041b02405268068152003015105003129440d1814010401c0d5201d80100e90421038140003180e0041910349209411841c0c20396900a480c90745002840749800c00070520800c44140c2c141c1180901035070348a148051 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 311530791 1250 311529541 311529553
    0xc0a0212070609300f020f0f0a050601050102030f0d1a040906050106030509031305040b010215011401030b0d03171f0e060f0627060d11031b13030204020304110d0f0302 74
    0x1c2001c01401c0c00f81d24041c0c4102080c800c08283d103038494800120519218411f40b404200346003291400d00d01504d0b040313a5994009919034041c41014410280140000d0004501d4455000811045802200805041695902c050224040c2c0010408201120041c01080700050a1030580c004200070301806001a1030000014150b02001080799990600031070004500f91400c0100006841c0c04070725581113000782103c0c081f070b03001e080000601030150711021440000756640010122043d004510b8030a020413207c0c080801e4002018240f201042c0740c60b240243d42d40f03030801c5101d2541490520111082c01d0000a0004107a80b00c140034100c200c4c0c07081f481403508400c20545025800c1d003860b0b03500ca440101d5080020074080389080380750250040382061048011a0b04030b8121018002c0030160001c2006500f079486507500743c10303e4003405518209070811280d580103602e54080240200d600001180500c94040c1d94200404001011460403502074a04030800708051041200548108 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 311532041 1250 311530791 311530823
    0xe0a031101060528050910060f0c08030c0a020a0203030c1b1e100201090501050f060117040510020c0307020307150801080327040f0507020c031002120c0a0212070609 73
    0x1806614100c4000400304003051030b01c0080e400340d504001354454881c40d1840800243c40d140c1510f07a5201c0d10000f48035461803482d00c1000381039030285034410410448030044007000220030f0016079070421246191191207522141d02a4540541c103500030b507251001045d0140d6984000468002c42078002c0c15515902c0b0284052040509008042054018499030311149600341107940c0900b070001031002154501e1380741c1301c190840e40141c0300c084a01c2101d508005055800000f00e6103c00506820b4404518081d29040e4075080040581c2025a03000034210b1203980080082e103031181e400405507550700d5501d1020175504010307400c1e4040843c040074000540d100001c402d841040d0030648442e44182c0901074810000343c0b10351040780d405a0384014030700c0e406500d44601c40c40740700c42e40c008200000205d4101890305044001100741c5900400207000308910b104052500311000301c0301c00791903030900c81050b41050800c14135000508808504c01081c496281c104444d1980200c04040d010400d07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 311533291 1250 311532041 311532043
    0x170307090501030204080714010c060e030a08280e031308030c0601050a0b07030305131e030e0d050a02090c1903050103060c050c0c1306050607030e09180706110106090e0a0311 77
    0x145108101e036903041f008040155540060b01c00c6143c45051402101c1186243d0742c5804984c0461000c60b0705610109030502da49070043c0d80181c00c000d4610954034070100d80c40d419002c4002240c5c811b0240d0740c481d000b5103181c40c0c003002600c0300072003807801c8540079940700c80d486c9607a50452203204c2020320840d8000900c0c5d08065583c501500d0a54810390700c3c0a290340c41c1034001d4030001e09483d84081e10076000f440403a120b42c28001400361000080c041654581c00c0c002c20b180702882c0064828600d00394150006a00068101ca0965055508159a41c1d518600303204600850440c00d001d801c48203085d00c0c80c140c7c150302142c1601c1c45058100001c84042004881e04d014900110500e940100308003081c51810380c0c10405c9003901d1003c00314004e5200c1c004038000f90000c0b24200c000c40d4100958444034a441003035158402d01d0b01c540c0301c0d50300600d0400d4a5851140e4460300061140340038800c1c0503007000307400a0000d071080b1402030118040d54090942d84051220059000901800c000c14442c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 311534541 1250 311533291 311533297
    0xf0715060b09030703080306150d1509052205031911060703200304020d060219080603120a0f0210050124021b101b06050603070e040209040b040501091703070905010302 74
    0x400303070080001318116900d0b141d40780d02c00b038596039100714004010000b0540c081d0090440c440c1090020a406480004c81801d060254018180450070402004510074a910b0804410070021a1046441246050941c2035104000b1040700e020140c4140500e040c0d0440d21258002d0345032000c55100d80d407050f00031401c0301c05010f250411400441d0854040003546005141c2080c001172020401c40026a6800103ea001c0b14149858403902d50714a044150007098481c0c1c404400d40242500b01c3d0850f170044940c0c0b1a660840b02880f10510442400720b10800c4040c40e018100c1c3c904200d1940c60728810b01041d050301031595003c85041d4940c49800d0b101154001010421030310f2103101c2100070040104412803032610f43c0401c038a0124011441204540c404403850043d10000745905040c41403500700400b58004c400700c0e10028061000580720780030521390068000381440410303112440c00c1809040f040c070015184d140351203194000c1e42d81100046020b516035403590a541a500c40041d810b1740 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 311535791 1250 311534541 311534557
    0x9010e06010e0702100e100605010c051203070c060c08040212010b010e2112030a2a0e13020325090b1b0715020703030906030b0f0409080f0715060b 65
    0xd000140104650031550600540180090056800c802d5448101204603440007000f07945940c015491454809400c2c8218000307040e0030702e010340c2c0c24041901c540c2e07a00c0346100040f00c0300001c004006215544200511003100d80c0c014801d0050b43e840c04002400f01000b0358041c1e10030502c002c1d00b0071120405114042c40e004040e11400b240c00c0c0060300700300c0740c01000d010b809401034800c100d407001c0000500285010101d444585900c0707044c46017110040b140c1c1c403c40b6110101e0000d0700242c1d070350006080e403986802507250840c01811400c000c21003100b5161804c0d000580080184680c0c0301e1502e03c2003144540804618180e0703000d56034226a80c0e0598424003082040030403040c0c010170b03039070040e0901c030f600751030100d41500fa9070782650003200340641d4040e070040c1c000d840d00b80100f5600c059540c0041500b071905100314555080025003108005880600ca20360b600035803020410004242c5056417075010890303403114502d00b04121803484000f08154014076000d40410003062520590b40c0c06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 311537041 1250 311535791 311535793
    0x90504051315020c0114010e010806010e0117070e0901020d050a050c0901030908070f120f09151815030603111804080a02120a03020415030c0e010e060909010b0a0809010e 75
    0x1e458181c6580d035244112000444072a6020401400e03540003d010301148401c0310b41c0944480d40c580445e600b0400b4040e004000c95070172410040040001022916040d81c0c6101c01da683c2004c2c0408001d4a881541d0380b05445070a40d440810140030419400b8190039000c000052100e540d40302c400390100e92080b2484100c40c901400400459440f0781d2000c1201489064800e1500354991121034801f2908038003140e18209008180c92002c1d4044204203911500c0d090400d036050800140d00c41c0140c21800b484200151050000440700c211046203000b45102061208005c10846c8001c0c0a88aa40415600c607100c541d111b500c0f40c2840c0b140181d0000c1c2d00074803921281c0721907642c4465944242da03100110710480d8054405803417040024110000251001641e80b86441101541148100b180300285450514451800c0c5c0d000300d00415003040902e07202c500035241c43c2c0010480d000701840282c11042c4840082440c0d40e051000b014140c0198076010001d5070340410b41801d81c1c1002c802a942 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 311538291 1250 311537041 311537071
    0xf2c011a041e08012a0c0f06050a0b190f0b0307051b0f0c06030115260a09030306090506030a02040c090906090b0316030f1205040b1602011b0c1815080a0309050405 72
    0x3514840e042990001d840380700141fa00c001141c890406a603020f80d0070040b620355402000b1028a007019450160710022054503000718500107a1050500292180190000c0000b00082d00c0c51b20960031100ca4040300c51020800107003a5042c00d94400c0410403454240c4030300801100d1514100301502c2c120791030700c65600303440380c0035074011a21100f94217851141010882820320404140b000128030030f0720140c3c00001c00310000e040c020f00390380c165482210707520f00c0d140c1400820b48002c07404400fa03940542c0c021844001e026000c03100700800b6404800114500140414000c03900c2d00b00c81310b0420100e0440703813241d2013021810b08004841c80700078500c0c524680441d0001e00741c2003800202a07150f0074158105640c402080000d41c4c841f80e0685076044e1189034041c2103617003000350070307000c01c40a083c400c0c0045050340c1c51150303503a4940120403c8541c50315985400000c143c114524007218800d2046206984009c850f541d800706c541e08034003042200b80041507604091040c644555030300011405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 311539541 1250 311538291 311538371
    0x3061f0b13030b040303051f05090f09070911030f070905030307170904090320010c050a0503340f0c080703080a150f2c011a041e0801 59
    0xc065000c01c081e00101416101c0010203d1105000144210300035203012810f454011000380c0340c481e1401d03c1a0724602d1500042c00241c440d805415440b41d00482a0502504d41d116541d10f0000242d0040981d45e0800381458458a0032001640c02800680c0c3e2151050725036140503290b142c040c0c05866010380c0240320020100f1701528500014410b96050546000820720105096030710074441500410003035601d1b5940c800902c4240d0b42c1c00ca600b08020018034030b007094028020311510303400e601000300201c04a10380d41141e50b0500030720210f82410448600d4100c00002001840c0381c00072000c1503c001c2c0b01c480b024010f6a1455100da4052022482c1000c0e50341d0988c0e50a8000d0920703655503581d8405000150045188580a4841140b0032520306d440d02c094021144504048415010006d1400c4d45580110011150541721050b0b03000d0600d44100c1c46011090255a1100700303070800d4502c0d80d80080010080e004143d0b1034020007071248142410a00545641c222103140c141500c0c055401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 311540791 1250 311539541 311539559
    0x90203280b0a0207080a030911100905010e0609060706050612061512030c0f0c0f06130317210402010306060e091504020706141623072406030203061f 66
    0x580e0006002c4001030a2450301c2d01c0f8002c0c160844020310020990b140041c0041c0200080c8034a0780103c103c0707045150034001d0800520414592061505000070721503150859945c000c03c0d00c0c02c0b82d00203480e054440b0500d00342000601015941180942050603812040703410100b80d0a1107210072984507120343d0399000034842c0141c410b15031084140014016000c3c2c0080502c2542c80c00090381c0d00a280050b400c80c100040c3c400360300e0680d031081a042010309006283d800720070701203d03008000e410032803072444420300481c40354101041c0c800e000c494a40210f030703003c8100075020718004c6c0c0c1c0c20001c03941c40c2c18060354415610302c0baa6501409074000200c4c861840c2c9aa1000040e000d400035003404447c1e941c0b0801c0d02d01c4082c0c42c0450140781f10410240c41132182c81d24401244602d8094014104c00403813480d030070b8030f043e0000640600080ca000c184190950048540c05245c00c1820011581543d4a401049a400124440c0c00f6180209a10b800e107032108001d030122607016125641d142400f86 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 311542041 1250 311540791 311540813
    0x9010b03091b0a031212380f0d060204030c1211040c18080102190504230414010e09061518061c0819031a010507030e03030a020109020328 61
    0x1940007444843c007100095142c1c2e034401785040d464a85880074401c804043c025181401d1075402d40a0403204125403040308403846826840d49415000206982000841d60b44005210f005810005401d161020400540e0090007200c1c055207654040da5101c2e8141e10003100c5515010b00380094091051200c0e01c2c0640c0301040c3c040d01030502004143d4a410010a00007495021147c40c0c0d40c082140c4851419500c0d520b0f825000c01d19007185410304110b1030400c111010900424040c01e510082071683d15140d0100300a0703801d283c4080700c03035a5944000b85903a04203c3e030b440c585e80a00004542181c40241c2c065071101c0c0000e10006e0810407101c91001c1d6040d0007000389610503203c005140103c0b025043e000000c0d80900e003441d607200701c10b030201005c0c0d188403903036081058035104159004403ca40e41d0650030800902e443c03079070b442c4a07080490716084122042581404002444811a901548541300d031034426405e132411202d1000f03054040000c1c480300c4c0c000c0c0364045041000028103900030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 311543291 1250 311542041 311542093
    0x7080d0c020f1e030607030e06011a04060c0501020c030403080c010f06050a140a12080306011d010507150e0f07050102011811090414010903021e0d0e041107051b09010b0309 76
    0x1000883c92140001d00d080d50594540001c80e0707440c1b850009214007400001d0151100d9075560416408100f658140c0340304a1043c0410490a60303c2c09082120070b4044440c0212940111b036201c03612406c114996070b024414003003040d840d091407180689458040c0c070085070780040ca611b0f00d49242c0342d241305001c511101e5840c1c0c0b0002c403001c045482030700c840401c500c0e98001e110894503440c01400160020000d81d200032505a400c0c0c01c026203e80e0321908a80328207600c18440e98451b07046208607805090360b101ca5000c0e41c01401c01100c014100040c0c40310032200c00761700901542020700b0a5084c0d55501d440c020708501d14180c44016607041041481b034000e80300c2c0d01c1c102c0da80640403442c0d5007128802e42d0110b0058000c0000d5000000100010b040c00310910070140c02d1301c0412160180c0401c0841c00c0c0e960003075840310240803a0f01c8640094404054120301610320090b01002d0090000020b008024862040000003190705c0c0203480c04d992003180f42400800160b4480800200c840c104116 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 311544541 1250 311543291 311543329
    0xc1d1f0611150a0504060c0206040f060c0c0203030c0f0709060f09090512120a061a03070806030313030b011a0c060103030e240903010f1b230c07080d0c020f 69
    0xb0340c0c82c165120300e126440c4142c00301d4500203101d041c90325042050345d800e1411882190701002c248004a50020400040c06521402c005030071500320710181c2d020b48200e08080c1d418000892151904500491010320b000c1c01d03036041e9280d564981d04c0040880d4014002d02441c011724100902c844845a400b0f4190207014030120348003c43c20860305010742d401050079945240e220001e100385440c0c1c0c0d003e414051700a00404040c5405a0f00356141c607030000a2a403c20070003800301181c8551001c1c03040f00c513595104098840026143d003003c2c03003811800e105100400380c00c68a5210b04026210584201210000c09040c3c140d19581b0200c032802100d40f10b82c0c1d0b0200078628409003200c141d4041e550755110b020b40711911450000c0800d030031107030000e440c801c4646c00d1180c900c02440c01004003051880d0282060001c08800c40c0041c00070403441420980c0650f4009103030414940006212411902244200d604c158010b0804440d003511000c0000d41004d0280c000341c10618000384200c044100c891 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 311545791 1250 311544541 311544553
    0x80f1009020703020604110901080a081c05010308070c050105070b0406021c050a150b030601052d0d0915060302060904020f0d0c031b0201140a0b010e030604061a0d0804140307030c1d1f0611 83
    0x151000c44ee42032340125080b440004100003084136040c0928020082420101c0c10b2082d5901c0c1ca0410000040004015070750004030301c3e16540a00310200f1401089200410170b40c50100c0d5032030010543c07038111b0780354018203000c00140b142d88541200d00c603110603034400d4149215070032000c4114060491868925014161210381125040090903010501e5030002c94042028240134403a00160074043c0000b40c280390f028405a2603210441c0c1007020140c4005941e080142126a0f00f070045540390f40c117440c00c02041082c202d40c5600658413002000c450254810a5000203a0880f00055000710703442c00704e00002109800c0303941c0324081210045c101441c0c100060f10009007081c00c1118112a01c9540399688020320070500413a480c040015100c0d811214800d86811030b040c040c034416030a40c508200c40e0000c45841c18890003004541c446141c521103901c1748102e224841000c4240403624000000043c0d43e050b624070304600200108160a00460030000102c60b950154070506402d40700300303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 311547041 1250 311545791 311545837
    0x50a030e030f0a050105160e01090501050a170901090209010e09060403080c0f030405071a1608451c02090a0e0d0305090d050a080f1009020703020604110901080a08 72
    0x610143d0480781c0300d28000030301403030100300c461110341d00c1c0555075040202c03d580c42c40703840e600402c0c004140c803001d00346980c81d0800080c0c11160703906040c0d59002c0d603805400c148000090305422442500d03100f12081c1c0801e80e2107910707001140c1c0c01181d81c408c0300d03802500440d0100c0d002d400115003161541d90f10030700d09408241044429441554221400d90000808200e00b120b80017070079503014034540d030a6183c01d0034130001c2030021500c0c0c0b001400025000a64000031010482071004d03880b24040000017001c81081c500108541c2d11030704c1e40190101c2e03445401ca500c4c1504070440f0103140d4003940d60149485800740034141074010420b10f4007a0703544110ba02d40080410030960407080655011449151501c0300500303203c400e05000b01404403d00c440c04010360060304a50f8480000d0007070000790f82c1c0e41001c03552000e40d076500c80b68505100140c01c0c414142e000c280e1620460154003204103004a20041c405d84050034410074416030414908200011011001004050252034a46001c0458 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 311548291 1250 311547041 311547043
    0x8031c0504210c020a0b040f0b090f03011506030b09010312300605031c091703071e060b090c0415110616020609010c02030d180c06050322050a030e030f 67
    0x450b04203a01140b00b1032040411450034903807083c091702441d200541000e151181220b070180d07150049a401400c00b00b04460740740c0700c0e4410b42c04601c400070000d20000a414011401510b000d00503000043e0809044d44c0103410015401c3e4102e80e4800003070300303c02d11243d40480d410f5400d00b01c51240707a961040d0a482d4070000404c280003240d0380d800002040d5191030109864400d00d0225400d00c3e0113003908a640154008802104a545502802d02c03000103148075941140701d80c1d50003c04000c5a055884581c8900113080300f90740c0d1281c0400c2124016174820000e0b44042150b1008501c2400c0009000e4450210300454540c4800c1c2800a81c99030110401ca04000c0b088a4140808501401101030365504219883c2c0090110008200027590408000e417244190743c0c80d0400300381c58262001c21030003203002091410b500322800a0203c0e44829000304241c1c0150b6403c804244481c640e840c46004202084c004564014020721042080e5a030a59143c0c840c504403503810300520203070320b1038440c1c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 311549541 1250 311548291 311548343
    0x140a032c0303010603140405031206030a06050103120e04140c0a0e150705190c030f03050409050f1006140417030c0d02100515220b0a0305150108031c0504 68
    0xd81080a15102e6041450080c1100c2c101100d0010b100c8144091102140740401164030f4003001c0700c40305070f9668601020038070b0100a480000d003417074605000001400721090708091100010f0b610800c0b05d450010411050fa0f04020340c5071141e090402c045a070040007080200200c5540e0b041840300340c102e650019950303001344d210ba40080f07100022244100310040c490b030294600110640404640140c8400c01d0080b40c2c1d0000800d041c14012040d810b040c040c170180c1d002098004d0080c4013038a040320180111000030350348031141500004002c03859900485030348019041d40c10304e10307041503c0c0c6100051100b0f45540317034103942e020410024102140034090501c1e69501900100f07105204840700f1011079400604460b140c1d507403000b440c1816522052003898005110150b4110340c1d142c40e120800400f00804210751100800c4030010030440e02181200910014054600ca140c0e0b07030b00c207003d032284030f500358054061141113501a289032295001e182c00030301441045441c0404001801c1e4808 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 311550791 1250 311549541 311549621
    0x115110709090606080610182c0f0606220b0a0f230402030103030905040903121a010810060804120c05030d021c09050c060901030b09010b19140a03 65
    0xd80302e85051040c0031007005404c2c0c102194000404079a032500c1d03c4000b00c0d19008c030303031f503403850b921050340810401002030540f420002008158008140b10712000381d48401c1405402c10b00d01a800014480c0e142100030b548005203030007429407129140c05281002000c0e50780c0c2c4254000110700340420921188030111000e40b50340000603041d02c44540c0042c1c41040c100c0c0b52507228a00400040c4002a80305070010201d890a580108400c4003a14040e1042d403451504030100615000e601d4050444040740e0142c080030a0325500d015844075407600b55410307818018440404c1d4042c000c00c000801c01c1c416040207400a240c60a602c0e000b0359101402d41c0c0c01100c203580c1154000c1265046203180300c41c0600c4c1c410010320200082e045503030304c040c1c454006a524134030600e0302049080650340290442410404024070968042d0b0311000c2642d10303600003800c2c900c40e003407140320500061030084905804011068030054100344120780c040300a880c189803400c15000c1c4000302d044400740702c1da2280b041c40f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 311552041 1250 311550791 311550803
    0x7050f0601052d040504020d0f03030c030e030421080f0309011d030307120b060c010f050717100312110f070806070f12051003050d0c060b0108011511070909 69
    0x55450301040001c0040c0ca522034643d8030030703041081c00341881c40c407a00442200007942d0100d600e41d103030f0001030030000e40c05070090f100c031802d12040004c059042c0c0c0020819003a54408103d000320200aa0f542e034065805002c600005410348402140054600041d01c50300c80c0691514003440b11210914a41043d1100302c40d6a4503003442580c101154a0300711400d980002c001c41c21441c0a030341c010083d644580d00c4000050361158254140d0321114122955844400024881a030385800f84800500d030072207020002a030b420406580305028181581e000d000131b003e01c406080d05680703500c09800c150204007002e01201018806028a00344101c003921290034000e007400510b00400e407820400001c2280080000c0080325419494108004030321a00031007100040c5030b40d6400c1e6051b89002190009815445004c0308011025401600c55100612818090006031002d000550b0041401e000d4501d840b0b40c042544210300f84284030310140c80220f1400c443e91701d955060a00102c46a41e2000d440d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 311553291 1250 311552041 311552053
    0x22020c0f0705131b0c060b0d030513050607021f0e0904111002070b07151512152c1510140f030a03080405071a0d0c170a0e0307050f 58
    0xd61418414007160021140c0e02131102c4800c000c0108001222030501c0c13400c1c03244401a03403062000c01c0d4080c140e000400b4140c1401040c081c1805003103900041e8490840740403108020482d42408401e94a0241d4050000034615054070054010b16022092550402040121003d442c0d0707500b004140c025806628101c90300c1c12028203102c03081c2e4124202ea800d43d80b02c4841044a0102c02d01100c030b800b60021551849071004a5202c009098640c01c00c4071480c5080c040821030300038454076405064401d00514455820f210403c07000e0320603644403201000448ac4005594000682101c41545e01c0b0809803401c051642c04030150f0f0701c1c01500e0b10306100f681d401090101c0c101c40380304001c10010440300c8541c0e0a0703407100025070354110480e004080012020114042050400451000c3c00c2500b681d00c07000b03041c18001900503004460b460380d600c1d0522107180d400c903018401c004010912a25404c1d41e541d20070350060090031002c14490640c2c40300704140000300d0300c144121440e800d140006000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 311554541 1250 311553291 311553299
    0x906071b0e011508010e01170106090e0c1906020c06030c0d0f0b01090807081207050312090109021807080604110d140603210319060521100204030222020c0f07 70
    0x943d508010400701072160010050155417081894139044980c000741006000d001044e40501608069009052517410a04c131502c90030804240c120304401c058800e600f54420103000001103580d244103580c0580c05c8030fa82d1485c08d090683c029940550f41e441d1013450300c0310542910041383d080d640d85d030790160391702c02c0300058030340e44520860020f098031030040c220503080c6a172041d10f07a0013100c5485400c1c000004c000302040010310546200304011305241d209445c1030000c030b07030107018040412481400d0a03660b501c001481e8401f5240039500c42c0d500c05180d0b9131000117004c000e1440a805104458080c454001158454001c3c0070b0703801d00e1024080391506054042c0740ca040c8101c0c4030150034650700600740c3c94141180d03003960b1340301e0009842503030030080383c07000c0c50024aa940c04c15600407400382101002641d86014031a8007415080c21201929011040c000403405980002540441c024005004031003421644680d2646d080c440149011140c1200c9442e01c1010f160314034998001180800c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 311555791 1250 311554541 311554559
    0x1002011409010e030f070c03050d0c060c0f0c060b0609030307031112071203090303060e01030501091a07020a08071a0112060b030102030c04090e1c02010605150f0906071b0e01 77
    0x5900078007888000c3c803030003a007140b009440740078a0820000e003280210b4030f4010320004405160040d900322082d525400740354280105044002c42040c0c484604040340800349520584540300346001d15a5082c080c0c01345584c4113005440c00240090740300e0010301100115a1342480200b038054841c1c6c5401c09140e07240b600c9070341004610104840050024010500441c040b90038aa030350b9003051270000380348034207807030150010304e840e41000e20034090490000c020020150f000e8040c6502a82c100c5800c105100302401c09444111602d400607044120081c00150034400035114680c850900d4004900144494504890702680a101c0c500b40000010003800403a1059110780b6200380c000354a54900784c1010381607849144542d240706503540c02c06411461050141017034104804400b4026056000310080c040d0030640505071060303003c000003c136010042c1b0100ea00a05041d840103081042e04010401d0940003007000340c44080000002503502d1480f50b844038090141d07206294810350510f0810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 311557041 1250 311555791 311555831
    0x6020d030b090606090d1e12110607092304020a0207150309030e150c0109110f3708030406090e0718420f08011401120b100201 56
    0x3500848101e024041d43c1d480d840f04a4203030030000d4074860003a401a2400101e81100c807910800007200155410701084440d04003500b05d91040e64460207917560010042d81c407402c094407050040b41d10490200000d03040c1c160050508001240d866075910382e00380116059900000304440180c00102040c041640120084a410b11844c9020084c03442e040c1c0e005414403006c1450103218160400d401e00c506e104a81c1103d880d0142c0c04001c1c090b284061400161062a8072112882600d92411aa400341812050f0f0092600c26050309040c41180c4c0f90036210808121f20720311050700c44c1e100c01207990f00d030800043c03000303151036a51032255615045008040550192100d001c0116100704240c0e101c83d40c0d0560340542d14410031403100854150103035425120501940c052202c1840050403080b642c232007200310800420b4840f6000f440307843e202126000001d00406540407525000340a255100300386904141a02c2c07500000c07402800000a001c1c002880e40c00e0005039101c0301d0188000aa036114 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 311558291 1250 311557041 311557061
    0xc040f0e0906010f0608060105161b0302090c09090a0905070e04150506061612091a04030c0503060c030a0b0a0306050c1c0e030909060f1530010501050a02010e0706020d03 75
    0x140101301c50801400034a010341c0178015078108a0040350344032010302151211000154441e40c0d1510720382d0320030590b601e0300c5c0d00c40c0700503842075241c8800510f00101c1c450860300b540304010015000f59a030812030318014844004261403d12403804041003010491381d0f0b442c05580076613240c04e0100c0d002042d0300142c1300700034a00c074028102030013209000340706400030955241c0d02c040320901e100d105c14001c459000c0c036075010562510300341c2c3c0401700700480c50004000f52801080006460360300d50003415580d500036900d00301000b10410010b61501000c0d44202c0c0e64030401001e840d240340d56521400c056a009442c02d4820650010303807117a000e41c0e100811401105284001c0c440d4a4949409a40703038050340c40914054088a80019070b41e0345c0d4500d0f080c0c840d14004060440200f044460303141690000c0042141500002a181c002200e95007860000003500c0c1c155002c66a003030000440d1290800004481990340361000c00b06181006d0103160003a10079a4000c22420440040040940d00c0b4556 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 311559541 1250 311558291 311558309
    0x180a080c060a060515030a0b03030a0908010e030901050412050703080307080702010c0f0503070e0a0504090b01060906050903030711040b09040b07090608160507081204050a060e0102031005090c040f0e090601 91
    0x120401043c0c445c080c0101906200303051540c2c0343e03550fa803070120103425032484030355250000003001019503400444603c1914115070013044011183c40005a880c030500300c4882c0801e1082c80304002000b9230003205a02c151140003502c0100c9e5490b030355141c10b50816510b810101d01644100800c540e4244a4096100a2890b00c40f0705c45c502d183e406096484081c01040801c00b141c00c0b8202c0980b80d5840d10002003102030802c109070b02c01030903d2107105000b0701503074001409210001800303a1007082035410502009001d14074210786a03a8550050b918480466001a25100c1e01d00560307072600850ba10460007608041f5843c94000401000402c0c50f03040705091080d00c0c801d110041a146260003070001050a0155807400107040c100c14038064801d23400410801c81c01080204000450056a0203114200501805800e0100c8070b01741c0c082181c24014030a000b03a803c01c032038039050301d000b0f400c9160624510b00d01901c541d200c0f17480f10750715000011040400010f00031143e1040280c1c5004200d482 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 311560791 1250 311559541 311559551
    0x204021c020703260609060f03010b03030d0212010f180504150504050604020a0501030e0616020f030a020309040f09120e190807140409020108040f0501021c0905010b040e15180a080c060a 82
    0x85c00115014000b4181c07a0040032351080d14111518258016100074070700808490316030b0303070807003152002e584109240c040c040c03030007400041c0b40d5442c2e200321400d50b0a000c118400c03044d5903069960090100500564102d9460000d1548100017071107200d0055000c2c1d400703848076140500502c10580455403080d41010b2400b04091003e078400304401da044001030b0105800341048040c101c5c9003c014960b00040c0b030000250700303000150000010100108151401d00c42d10b1040a4004210b0701c1d11180605030322420380741d410380c0520034400d0300901d900003031010780d216880c0c4d181c080750304081c3d8122007816440a00207000301d1941c605152b80f41e1504503014019035000d40e00007000c1503030144c0003e10240f04111031a041008c00e40603110b041030f000c003018642c034000480f4080078000803541507406500e064225002420140140040f81c0303454801080c400c4448118444c01e62002040b041c02c1880711406810341e00030501c014140103000b0380e400d81e10b910340d94110f542000400742498154a1a02c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 311562041 1250 311560791 311560801
    0x212180c0f130b0f040c020d0206011a03070f0909060b04030b0a05060a06140909040b01030b0907060504290d02031f080c01030507120903120c0e0603040204021c02070326 75
    0xd0a950034859449001080c1011090f010401000c0500e12041c0d0203404d11620185d280e9001500844040d084e90803200c1990741c0c1c0c01914034108001c01c840704452000c20001d680103001e01862110701e11140350603060300d580d80c26407204440258000c02e1025000040800601c0000b0001e41d400000a00c0f007004141080000140c982c2d01520640c01400710041e100c1050340503102c15241c00c3c1d01d018089030464500ac0c41c3c81c0d5070220090004454500704e0300301003910300000103105000d50310681c6580f840c0c40e0400c494003c0ca040f001d2414100500050117030f462079415640500294600181d0145e01c0f03040051413031140c2e8407501c1e0507086e0400030a0b01040f0328800019050440c08007820b0000f080d4a03070701401c5401c0313600036034004100c0f0305006d001e00c01c050713110117100d010421140e0108805c00c80400101c81d00c0b40d85003c0035078040c2d410310200f005498550f0040c00004010404d00c81c06103503808034142680c001070f000380d012862149000b0f8240103142403901150803444208034440c584 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 311563291 1250 311562041 311562049
    0xc12030406030b032104031e0209180708010207080406110d080106081b070b07020c0d0c0b0904090c0b0d060b030402220b030102070813050a0302031e010212180c0f 72
    0x5501c600d004140c0ca03030f440f0300282d84040c03114101c0c507040c85000c00d80c04001601c817500140c4c45440103e5109081c00c0303034003042001c00f01804207a035034014061070054a8096410703070106800e078003440c40c501410781c000031424024401451040d01c6068030310b494074549400600701f0840202c0c0308502d0740004c000c18440a41c042c05441c1580c00380d0030410900d80b42c8450a60001111054203108100001000401d101070300e203080748540b002e5400c450259000105112002040040003000d481c6041000d00100050740050304c6004805040029503642c142c0302c0c401242c60741e40c00410600400510103800b0515401024041c06c10000d000e881e60820381d000c00c009003884200184002182c0324281100760940c0c12420803c0c034000d000759100d0210341043c51003a400000341a00c004015440006c003400c090b600d00f0100d0703400502800d043d1601000303040308030140009507022035500b0400025015420b095032805660706050403540d50070b0a005c054074000f0101582c034030480c252403031102d095071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 311564541 1250 311563291 311563297
    0x40b1c0b0906040504060b2112070302150a0b0402120a060902090f010516320a0b01051c02060d06140901030308061203040906120b070809120705070905041a0a020306031209030a0209010603050106020c1203 90
    0xc0400d063740800e81d1110f800d07200811070000e69950050000802c4030b0480d042c01c0c20365002c2c10008100308032059a07000c04000b00c1c820805665080785041245040c1ca6000f0300203420042d00600e04c2001c41e00c0a96207000310325800540329108800c0341d602ca00c0144c003507460b8054100c017034000100080c80f0180c03500c000800d0144581072152841c070648089032110200650300031540035218645921220681d040500403e0091070030007100a50345400e2460302c1029103040300d41580382e51a55890310b0060202442c02805c0750070292104004c0040c0e1112188075200c000c121241d4413050705100c038504802c888901924040800510605010381e10074042400c09200888101e11580c5045500e001400c0c6200d07a440403028601c0c00302040240400d2001d4641001780104004110f40c0d075980324501240070581d2000d816902480080b440340760100d006200e040b200400f04d5071440b005030300007204404242c20100000707480c1d07070040040d00e40402c150a0030100c200c031820440690f1801e0b5587d240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 311565791 1250 311564541 311564563
    0x50a0b01170a060b01050d090303020c12190503040c0f0e0f0c070506010501050306131109010f020f03030613021204030f08090703081e0f040b1c0b0906040504060b2112070302 77
    0x25544a800d13808070381c0600100c801e05602c062040c420700b03e075410050001d40010441c14524003520082101881d400b0088078210740b0001441292020040350489454000600c12108402d16000124100e10380030260b0300184180816208186061a410224110040d1003064a41000d015243c0050404111b10303040d600203181c15074690703950a001803003520240c480070801d1454010301400c800191001000c60700c5007038903909001c0c82c00640499030b4140140101c6861307003060011038124540962182d022036580030000d030030145000b0724001700d0507081d1f6007100445c40354034070348042c9a00703c000541d01074984400317080031a14548514001d40701c0d4001201d6400e5040c50a6140c01c0d0400c025a05120744454070b02d80c60f25210b64000096a00081002da85e48600d0031918484420034051040d1110000d80746079003645454050002401000d002156015100d500c550144c7c0c445020740e44050090b840710320600c1544000a40c10032107451000d4000b40301c1088a030b40480e400180b102c280c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 311567041 1250 311565791 311565803
    0x20a2006060d02040b0406090e070e010e13230d0e0901180207150507180b131203090b1314040b0f090a091509060e0105090d0f1b050a0b01170a 63
    0xe21490f20009000b045800000c40c1c3c4107151810203c0c82d400b0a038000072223000d440b02121042901c1c6c4074440e411fa0024400d00c80900146000030b010240b8045c114080903108070a440c403958a080030309940c01140e0882c21070540c1c04544601c0409a04c801c4003621908190752910265040001c001355045c0303064006402a600040c03103c040051b0100022904c0500e440100194100300000514984e18103001d901410311844000c1481c034140c0c42200c0301211300c4003a18258505c0c140440310710070410304041d020b01c2040700c80003030044003403401888072001d071400f00f22443d41491803030721240c0003c100d01406186410a4a1180d441d02e403050311030a8006c9031849020f9480b072055401511040400518814800a410303203028403a811103030006104610a10000b100c4e154070600300c030001c4900489560284052481c000d000310840c0482c41c4941c5810310540000c5041942000d88140040b2a294400c41c001400d0000c2c6013195030140660303171340c0184480c20744410b89a86032543d032009004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 311568291 1250 311567041 311567059
    0x9011b03020d180810241d0a14070e01091a070b04150f0b0f041802150c0304081b0907050904020a03060306090f020108070509010818030c030c01020a200606 69
    0x1c550f420340d503080010811001191030166542041001800c80d816299070561092107034050a402c4d19056101a20a00944800955110007101d440c000010301840d040da5900d0a24803a80194041d07650b2040c03aa0713490b4103584003050b900041c1212035a5200742c4a84000141c0f100004122001721020160014030807200c0d916141000001000d400d100448064504603804111480d5070b0000b105001d4111041542e0318038080500003902d440010b580da40e03030440d14141005252103078040d0b41007866402600d06142c481c074181b0346164880c1d00814810383c000d0007141006100c81101c01140001558075500b1428182c8000d402c5000b0f22003524400d40d008036202040714825840b80c0003e50700b0070000d2103400428141010703120b10071101680024a400005005540030f0b0040f5103200c80180e4503600159038a01d0821560303141d1a009001e540010030a12031040d030100054440e4000980c0016070340c0c4a2020041e058103850700c060000307481a0300c03803c09400c0c3c5c0800da40340d201d841560440c43d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 311569541 1250 311568291 311568317
    0x70b04211407021c11180601021c05091801031401020f031803070f081306050307050f090a030c082803050a0c020d08040807090b30030d0203010b09011b03020d 70
    0x71000480c1e6603130f844180061180c41441081110000c0d2081c1180450400c0c103544991011203680d030140e404030682c9200390007030305a4a443d142581c541541404104400500540600846c0d04907003a041d00050082c85000b1050481c90044880214900860140203940314040101040e2244d4003010f5044400712041c0210f80845a00035804046043c803071402c055180c0156080d0302055183d6080801c1d014018412203001e4115600d6841c10080400075180c0b0715440084020307080b480300b480c0000010045402c41018001c068003500b00060180702041d80c9654103080d446448425481410100381c01c00120343e250350316481d221100c03241034000f1034000d548000380100700000c00900012200c4011507001c003546c18020b01400080007081c204092545001b402c10103101049142202001c40540300c40c9042ca0281b090ba030071700050040b0801281c009074040d50015000180c442103541c0d02001d050f00791002c002c10000c490314a078800a649404500c544406d00002040070740e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 311570791 1250 311569541 311569549
    0x150901030b1c0f141f0b0108040201080109020c010621050d0c0305070b07020c030a110301060e371a120d0801090e0304180b0f060c03030a02070314070b0421140702 72
    0xc03041c4c2e820103080310b503001d0070050003d240220003180088160f1510580700e41ca90f10131258107000c3d9405035502000c40c4d003000f000800035445101c62030343c250360350b4030300150318444482c9020311903104403450300f00c041c8117080039401d1000f29000001000b4405c42d24600180c2c0003019161510f82101c1d0450190303640342d509915101c41030000319031510821243c0c504000f0139201d25484100190020b10a031907446d500300c2d04413901682c100c8244a10b02c52004810480d070030824503880c900304440c00d140002103956004403080c101c4400c4041120300c00114140c1042104090115a00340c000c1805039001100140004018024030300c0064642c03400d542440020000c1e278001d80040824840c01d4038440403060000c00c0c0103000716000341012548802c4502c1d02c10181d615114021020354650380e0f6641e4500001d6208420480500900d40c00c15000c01542c400984046845240000701c64141410080711240d000524030f1403d41800d40c1031040c0c1a80044039101110b260210240c48007243c0c4002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 311572041 1250 311570791 311570813
    0x150d02030a06080f060103050708011413110d030c1703010602060f150a08010f0c0905180a0f0906050405150903040e06150a08070f09030803190b150901030b1c0f 71
    0x1c0050f5100303044015019180101da0349040780e1084085a107160740c1c40f4602402d965116005190407110000081d002540844c4200b640c03074443e0a480c00e404017401c000a2907852101815400603d042030700c0801c02c100302c01d4441d404041850580d01715890881e0096076039200a058910201c811000b01314030442044c007072014150000c0c01103078165241e1099030300a01441c0003502c040d50030240c1800c9610b000300c000d1000d075140034049405d15000c40105480c041c01c040c1c0f626200596802c09809601080d1044000c854881c02c000704031800c0c81d0500c3c43c50100500080d042d0030501c03805110040038000219421207501a80040e43e6559000000c2c0d40d0740951202c0d0000120001000340c0d140f68002d180394441c03503e94543c4651039000070021a15010740e0f010040104104102181d030000c00300000b041c02e2521f081c80410402e000c1c0740407900203da8406a04514040490901180e40c0c01d40510f0302015000e6442c0c80103284e25402150104000144c05080c0941e01200801408070740780070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 311573291 1250 311572041 311572049
    0x90403030b03280203062406030403020705031209010f17190b04090c08060c0306010906030b0325212102031b06010513140705030c13180b150d02030a06 67
    0xa0fa00ca00004030403181c100d03041d000002c912a0240a001400d510711008002d100807010383c90f14a031a00312030050002e0303a440a8000c0d41984603800740083e03d941d00300304950010110003059910740900340005006288626600d40030b214600d403000380900044840c15520004a00e11442c0701ca00440f00000146104030301290000d041c00c05500c11b11184030071007005c990151048616a170340d00f940c0b20f80305010549429000600c40d4004009681c0300c6d070080310800e40c00030151081c02119020040100d54a000400000b88507030742c0402c03614040c0c1940400e440342c2401d080e400e01425903110502010102c3d810f01b60810000c0300361030242e10170000d80b80360a5075902c4c2c030003c00140102c4269a031400b44280da12610244516565401c07642c059000c18960700040146151117901d0145e641d500000c00700315151400380041012104950700900060641c4012503880d1100c082d4500d0660309200000c901a852400c0c00c0c42c61000458102d0b0040f0107401d0380140c40c0d44031310700f880024282d1680 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 311574541 1250 311573291 311573323
    0x30606040f020c01150e0105010f020307060906061701050f070201020c100c0203070c0f030b01090e0319110d0509030f0114130303150801021207020d0f0e040e160602011406090403030b03 82
    0x7030351850369842c00800c141c903400d010b07960050b230f81d44004459041400103590010b8205100700e00000d0303c80d4100c100a54400c00300410896294408000d0780074503c9a541c202d40e45800a0006d4a10000d4080b60420380600c029450315107090820343e503c525540c0102c85050750b884a004400f84244151403009a00ca00c00d14056695030312002010754043c081500e001024000024100e05948280da00300c1c5030074805503007442c1d00890040b181030a40ca42d00b1061240001da0108487d00502106000c4c20b0755440f01a02e514914043c903141404144500300d40d0303131400c1003415100c401d1840c407a41c0101d00a22105c1d040c0b4492608a02034401f21850303080c024116500495080019000303024152a00803040a60340d070b42001c200e07981d048150443d000318140c01c00e9050118403d49603d46903200151001c202c501c00c61400c103281c080440419141800c02110070f000240d170a01404030b030040c420701c5108030742c1010000503e080c50040c000600703240e5240003000c11902c0500070403402d940901 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 311575791 1250 311574541 311574551
    0x1d0a030302100c05160209061305100f12210c020a060839090301020c030a02010617030307020312060d060603080a11060c0301030f210905040c0806030606040f020c01 73
    0x100d406981c0d00303100741c03402d1003090402c048030f21a42c0c80307901038448207502c60800c4400b070401d40d02400b1084001820b002c0d084035034039001c0ea0040c07803580501b40c05901c41400d0310341c03101c1c9060201c410310f82940d001402c0e4600c0805c02c0e400032880ca001c8221025140c0941302035881c0c48114161b40d003d440f1000207400c03001c20000000c125412803c29031043d03a00c00c04c0302192503210840291100000580c1000b10304014000307000c650f2007d40600308041000d40014909407401310760320f103590041800c482c0181c0d1107580038000b0300528203c03050907140c0389000f035080d4107005a000e901e90080c0001b5031000703c00d1400140c85903507910b108020481c1c0000b0704110490700d80c200005244d1142c001034020650407a2190300e800c00020f481403003850200c010034110303429542e0780c285902d000003058804802880c44000c60b0140b000300ca042d038400607200c0705c94251a10040c803064030342101440043c40416001c12000f51008110035034040c5044800203000c140c00c21110000703008030704405031550b181c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 311577041 1250 311575791 311575793
    0x9070806180a09030e01051911070902070f02030c03030a090302010c0c0b270a050102060a0b1f0302040302130903081f08101e0216060b0a150804120e0d02011d0a03 72
    0x10b80c800f001c0d1a0082d82d460440446010040d1070f14400c10300148103803148030015100c00c074450740c3c2c1120341c0440002910f02d4181e0b5608420240d8000d98802e513036488411880c502146010071141024107001da0245090a01d582c0014000e4040f501c8003034140088039241d20b04000d8121280000707040c41180054885903100e210800c14142c2c3c0400c1704482034001801c02e040c2c50103e01250890780140e008100903640e2500a0015100202005820003007a9003000080c100c04802c00c1084205a80c00585880c0b0314010008540c844103410120075180040503800300e9400800c243c1c0c03040307280040c40f545071030f00c1001003418515a80810068065441e500d400140c2d913411110484841e00741c0040c48180c9044024100e100300d0b41f210407551404926040040d5441d00041d824507401810800070503554485d4104000c5202c03444000911030408010400c4810060682a0140c1d8500010034882400114014246000020b41404400960600c51000c003c0c0d11034094840908984049992 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 311578291 1250 311577041 311577061
    0x80702040207111005090a18181401050f010510030c20010b01080a0501211104060b031914130204020403051207020109140d03110a0501240602010b0907080618 70
    0x101c0800c52050b0700120031031138407a2042c4255441d1503802000c0c1078840f8545501d15605c80300b0401e200c0032643d10b62540b18014003480303030010b102a006801c4407040450690100d403c40e0f03001005c80c090103050b800184039075140c00442c19128051418001203501d00001c081c1e81e0721442c1c488016403072918280c1c03400d00340f0041d0040c20181000380c035500e54580b14000301c042942d4003401034800355074085d0201c0300a61000c645001d056400f428110b00040c05140108040c0c0e04039801003502600004140044c605031000c07102c0d01090004c1e03041050f82c00790126141040c02c007501107640680c6640900065590310340c1102e000710743c00002c8070558490b0980c0c1e5050f0b03800610050740400c01d000d100154045100000a02e2014000c000c0b190b5581c4690341903410003041d00038003440f4440d1540540006000b441449540f481c0102048015800c00c5240a07020000e50040411a4103015144450703866001025800c00b6840c03d00403041d5452002095195028990700c13200a00c620041c00001d500b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 311579541 1250 311578291 311578313
    0x5010e0f0a03050c1002240c0d050406272103060b0408010603110108090705130603120309020a0f050306010b030a0b030a080904050a091e0312060b0d0c03050103020913080702040207 80
    0x10013a51903140307440b03a05c0030a9848108494844043d4640c049810344203c802141980d8001c40805a580c1080ea00320b6060080761000c4500311461035940721b1a221401c1d00010041c2d030036212a60200386880c1d66030344d9448040c540101902913042522064240500a4000b40701070401410002e880e40d99845010f40680490b1006076070180040740c020050394440e1032442e100e101940010a1420b18040c280302c02c801170940100103203556482c000c80003c02c45240c810600040c1e070350200300c1d401c6500420000c81c1c0c5941c000003040003006000c0100391004105c0504488100c4402601c0780da071a4400e101800c400302106900d07005071841c600400080001070725020b01c00352030410161742d07480300030000c4038450000600482160380498000f0100c400f402c8010900c030789004100c0f004035503128000d0303412540001c2504040803921800c1e8416600c1045030500a0f1b24040c082945542c000c070b074510001402c0818a17540b02d020039010b1144000031a154680c4c0580215610101d600308949251 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 311580791 1250 311579541 311579563
    0x14040b070516090219260934180e0601030803011805010303090b03151909051014120a0506010f0509060427060b18090d090f05010e0f0a0305 62
    0x21005201240c0f410403882175500f03260f4071403207560030b41d40d07250000d4401116007003100b602020b2203641e02c4d000500c0f180314035000702c01c942c000300000b0b402e4000700458190f008801c0c0301c1c4510604040b50300341c20589000011110007480003641c0303051182450019203045409001a885800000010060760500841c1200c1001201c0f8059280c403040e800309a034070a11024001402c00d0b54240908881d140c011a000400034001c580030102080106030203030383c002c03014a100014403170100440c0c1c050b401402d9002080200f41c034a054104803260307201c0700400c00664040d03a0340c8212190307902d00400114200740d401108540c80d56944038203294044141e800743c039004500e418082829418a0700400803040250700e0150701640240e00c00c02030010f00340c401621341d079464036084015500c42200009640c5460300c9000c0ca1854110b07070040c640340c980000d0004000600c84100711444d032801d0398070b00341d81007440c05480b0850600c0000d400f0030248005a688031596140000420000040100300a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 311582041 1250 311580791 311580823
    0x1051c0b1e0703020c0303040b0601200606030c04020c1903020f0316060f0c0c0209130c03050a0c0806150103020f1b0f01110f1c090b16090509040f0314040b0705 71
    0x2d9941c00411401d9005540344520705501c00d1000c500000c4450320b0040e4483c030185080e54024080c01c1a4068124a6641007030054200e0340c00d016070307800c0c188204002c058050701c0c258031b440204001190b80e00524a07040d0541200090010200342c42804003000c264081011251206a41100c00a100440c15000ca45181c07130504c0305454030026001e062803841d01342c0c90344a01000140c007800300141000300003d030b104d24007807200000200b4468450002e9070064000304400c403003902c1d010800d03070340344d400101c2c4aa02040402407411741c030a1000c0b04009080c0b07030140c1c82e1440f281a5103002d006900c025200180c08900000f183c61000510380410740d00e50700244810510024041442d00c14401c0504449404000703041101d433111050903001840c001d4006100e0002d616035010f0000f0548080d0910408485180e4042d0b91041140015000c129480c1000c0e0405540d401c1e00c80f20b0240c002800d04c1451858041e440c025081030301c00138500302012582d580100d00e052a1690400e40c940710b08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 311583291 1250 311582041 311582101
    0x60501080f0c03060114090d050303041a09070303050d02070605040b2a0d0213030501050f09070f15030c0309050d0c05060c0903030f030c0412080319050f01051c0b 72
    0x1038a4020703030507140078201c20702d10249507890360001117568010070490740c00820010014000d0b80c0d1100d84192a03030070b0060014549078109850a41e0014170031b014141800355180041c010000c4020400301c00710383e89414960350318040c402030071003c2d00074414040c101c185408204010b2210098080b8401c441c41c4004404005407580082d4400046800340401d031801800413490450b82a40240400280e00480c41c6403550740f580d801e82941c0048500d41001c200100034090a81000c00406e4040c060b0501503924050600e0100d0401030902000c190825859260000d40980254082d180060304201601c1842c0b041140140100314409400c40300341c0719400001da0301e080d600041d204c01e05801006103142c042d1001c0f2542c502c0d04003411000481000300400550b00d101d09000442031885495115160f1501521f80c046045090446041c1c2d142404200281408543c8586047d1101210a11440548840312811500c4441802011041c3ca41c05001d210610b80c0e103030620400000c040840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 311584541 1250 311583291 311583301
    0x4060e0103050121061506230415050313120e030d0e030307080a0504090515010836070b07050606040c021615031b180506090f0f03031c06050108 64
    0x7048400920551070300c0426203801c440b2031075140b184c81c52070b940501d6010035214000e41a10700404d40c1540700c5804902415540b081030003c1441410a640401000c141014a4188108981c00f90180e60310208880000080e0100b440d846802282c207810600031b1000440d6100058844103609014071302c41e00c60061001001032181c2c1c45801000c9018001c1e41c1000d91070b51b1107071100e401800c00f02090000c140800b0400400f184206442f80344401008aa01c0f2100300014110401c05008108209130b0800d24102c05030300c82440081e000d18650100c0449580c4036981ca00b4a9102c0e085400d005000140b01d5040c0a400030b6802d0144c0130885040020f003128140981e0f517401074507018003a01c0c2c106d6100b0411104140140740481019040110703082d03044160395941c0c014014a5a00455508040600022107843c1038801402003615a64908181100000c1e6204160401103100c0c2c84c4c0a0340c0c8408684050050b29140600c44019003003240491100d41e0141c2081e00580c0e00196560b0700060f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 311585791 1250 311584541 311584547
    0xe09010209010914030705030a050a1a0f04110112020a030603050f010b090a0c0201060302060c03030a0506060405010e0f0a03020409380103231e0609030a080619090c0504060e01 78
    0x800d03209050f181c06149900d03229405401e080040d868517850300407070f540000c03e52000e21244902501c194042d202850303241c5054008011102008407000d07241004004103490711020190304241c1042080d8515501c900040300c200601400003030340079002090801c00c0c182c140d04101d05881c803960654880200d03080b0700500700e903040703d0b10540c401c3c01d400c082a482c0070194414042d020551002203041130300d94022420680c4201c40c903d44941c00001045410304c0103200e500c1e00050111071242c6050300d03043c00241001c5620f226075200d42c00341040600c00e603440801203001103034054401e01c540c0030300307080124800b04825074030310310560701d0141805c0313a07075400b1020144c1890f00340c510040e590850329402c01c5504c10450000e90400240c00c001d903003007000c110100071140e03414110035a11090800c03090412a025240c1c13061940180a16550b16820405144c0c3c001d000b03039aa0303540f64a182c500032104100503130103184585c0c6801c80f1803080c0b540c000d008200b560690b80304e812103032803910011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 311587041 1250 311585791 311585797
    0x807050f090105060d0204080316210905040c0e030613031d060d02030a090614090d050702060403260705010506210604030807140301090e210d0c1101050f010e090102 73
    0x1050307000d02404014401d07481e000300503042e240c02c09600141001c3c0c03281c851525540c000004c0040041c0d14002c03e104000c4410108000c203440075614020b081340a0070040c14486a07805030300e105648502c401070f5401c1c482d9086840c0c021004044600c18144003080079940c880401c8160300041840c2c200031a40d10841045649001000d0441440d0241d22401c1c90004d40004d002c000402d07403502001c6001c50340501500784044000f0b54032040344d080103241030389003603130000b00103051100510401000d60f4030b070030555045a4100d420b03c5204031004a951986804409950102600100b9403400707000e415845148640c1c0180d410400c85010742403200c042c80b151041c9206190f00c1080010b00091040869a03004601c1e4142413504070741407010080c07250000d030840300e01a0b9607904041d000c44d808110a0268010b8501d640c00d04407801904080503108844200d0b910702c0c1c0300c0f550030301107500c64510303000601c1444000700301a0400010389114148280301e250051030703050011805904046c421 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 311588291 1250 311587041 311587069
    0x12100f170a0f03030e100b03010b0f0603220506011508070801050d11060412050c0306160206071416150b03011109040f0b0301020301030506070216031e0f080c07080705 74
    0x2060481c06a03540c6030b1103520704540803001c045e122003081044880812203040c0300b07821641d010032243d044a00341070071070307408241141c81034402228035405c68072440c04894003d40e0070f051200f802c2c0c0300400d8103414540f400f00014094840c0302e000240c4c0c100701d0303150800e10014555544015031075088044032264420300807998864103003910500042c3e2486400340f64804080c08041c1802c0c1d80314810380c2d26182c0321005481030b0304641469441c44c17a06028036079019800c400183c840b403407030f1a0000e5842c03800418110510007127004803204200400b040c1d60084002d2000900d0071441c901c1d02c400000b0581c03100780801d40c18244419207030310b818050031205141740302c015418852144204000381060038603a8845540d104c0c01d442e0b05072070a000a5020318080c42c01803810b070070000e900a01e481c04403240100d045194140c140000f400c07140d41149a40702905100b240d811032810070b20300c84001d4010050992900145c16a1980404203050084400368003da50700c5c02d40d00d809001c40c81405841e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 311589541 1250 311588291 311588293
    0x10b0904110d03092408090105010303050f0307020a0b041109060d020916120c030504021810050d030201020c060114030709270519081e0c0d0f0512100f17 68
    0x229001e107041001000c89038600078600000c1203641c1d2180d07a9505407240c205110200c820712905812203400042e42c0e030700003820200030890396146031001421405144521140c50000001290b4810b20070071100c1c4480790420411507603410701c0e140020151900080b180d0281c099038002800310b20341000f9801c2090b0300640b01c0240e940d6140c580e0a844034210381c07900705005031000c40b107809461901c521400e03042140c5000840d0308081c0104182640346210400c01c0324510410409401402032100084610648108007041040e20f41a070281c040d104031072626104603400000c49103842c8040407400e0000b034069521864513031400205039000d104c0d03242090001e6456030181c44900b05061000d6a003d0800c0c1c0e2004201001c0c0c41c80c904681c90015214010045440c00312408041d0038900c21518000301c25141040c0c03070707148507140c01915102400b408945052100c02e42c1c02340d000c5804800001e40400050714140310b503c24003056501a00429860400011800c08032003d1146041e0840c5c0e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 311590791 1250 311589541 311589563
    0x31602010318050610030c0b03010b07032a0507050f030102070327080706020106060206130308060f040f15031103010c0c080a120c02031b120a0c141e010b0904 70
    0x280055016003149202046401c1c0c090300c0140c08910140503007405120500341ca00380f44ca00d141402c04c2d5004c100e03004500015402c00c010042c100780101110070030780d41800d03e599500d400200305852800640440103d4a881a8501040020108080c002e07500100c40e4901c0004802c0c003410700b00d00900500601040700302401040c0d044500801c01c51843c11404044212500e03075078000e09020607030f445040980e449010500030103806000107070781b110188140090003c07503a10000c103031039000b42c00c01d4010302581400c100640c8564108421000780b020701882000715425205907603e80344d200980306150301b03400b071001a180601401c11040000c0c0e03600c050602144c0c4490700300f03903c002000003d0000c00510a5050703002401043c00b030a8160b0003854036440041c9982c24a00e054009011044d0400c7c0545c1f50461044410380c4c4040555140004a031901454114080c2c2d440b2000308110341710f01598200303240e008014552141180000030b00c030020f800c0050044002c02560000d02d180481c2d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 311592041 1250 311590791 311590793
    0x204050d020f0f0301020a05070c05030a0b0f15041a2107170115090618050c040603020a27051206040314090112090b0115021209040b1503010603021b0316 68
    0x7949840402d1000030114183c240403180040c1c00c80e444100038002207800412030340e0900c14002817510090106170f019192034120759860f0071514a00814a8028102c0b079000706100403502010444041009042081180310030398000401e115542c6440e84603006104008045429807100c0203102c9180c0300003004007a06065a41c0e8a40010004146040d96a60f5a55a1041005201c40014100c44d400003407168100714062807954181c04460301c150b0f0601091000c1d40d81070008a5048a08902e070068884140203411950949100440c004424100301038690461601c5c1d2110b040711800c42e440551742e4901141551070b800704480242c04216024807001079010400300409440e08149800c050180c02c0103103000c101c4400f044113903000c10000300140107454501c3c000d13011000c001d00040020300340700700c020351042c81200c00341e078000c0b81c0314690541c403601d840004007117841c04021b0755916903850b088010006e4008036844003080a20700714034242844080110348161112620804019540e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 311593291 1250 311592041 311592049
    0x706020c031207032732040b01051606270c030b04020d080a0206061c3801060f02010b04060503060a0e241008060105010f080901140103050c0109090204050d02 70
    0xb0041d000c1c2d0030305c1400254040b01c400b0716001d44820464000c145050682014150a4094036007140d1807080219040c0c8561a001001880c00805c58120b0300800c01c1d05c68400120f4460050088040c0d1000c40d850030b40c41001056002540f1440c8407000000844030f0b40c141d1080313448070b418409015012101d1081c00490741040d80240c0c0540013808211100c4002e60700c0c011150f0040400100580242050041a1400d5081d2885060f800070100c903c03010305841c0d02c0380490740e1414040b4456202d03405602c03d0070f500d003250402d2906901807940d556a48000107003180c428200180010751824040c00c0b0a442c2621070401601c1c006070042a0130b940700400034006001d100f10b280b4442c41020015800420146406034110b040501c9488803800d042c140000320305642c0d08803021070380010340140b2007a41e020803a003881643c5490300030056120400b910b8010511104158000902400040203001c00001d012494460a90350101c615658010074000c0340618014203510000e018298005458 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 311594541 1250 311593291 311593297
    0xc03030203061504060c0b060108100b0304020d050109051b0307181802031b0112020c1510090527070602032710090e01060e0102062e0602010e0706020c0312 69
    0x7005820a103c001e0340c1e50320080c0c140c0050f4403004c0021071000b041801c00c0501d60035150402c80a0070126083d040c908003101902026014903448020080006070965a80c00a081910390f0440002c1203461807600b40b41e40c80c0c0640c0400d0745d44031041ca000003816810000350310f03c1101c0c2080c0c100d0300303016402e000c910058600055800c0180b40b010034000050790301440100760110220130040c0000703001c100007419407821440528003161050011080030b440100d0907000200441d2200b031010350319100f60038648012a00b0007403a0501d05001c11903400000c0400107404440e4500d81c0040b404044100365807204180603240c01600140210340d00c950a05107071482c04210103030701d20700815916010034000a1030008150003d0030b1151300304225104010503501400c0c541c46c110640400c210f00103943c58078080c040d60b0300c03040880001641c918003a03524000d24403110481010b11a030f0707118000e010b84449007402c3c800d802a01e200240305800054403440403031024016040c0c2152140d00502550 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 311595791 1250 311594541 311594551
    0x7030506010e090a050604180809010e060705030c01140c0309070e2809030f020703050309091003060e0a1209062003120a0903090501030b0d140c03030703111209010c03030203 77
    0x50703090282d0b065a500c3c0003549100d18081140050a4a001710411059440f03005003101c0700c40c2c030046c0c2040403a0819040300c1c0e02000038280b686a032840040414410b1090f001d01400364000450b44441c400819007102000c00040a600d640f40d460307525210110f40b006072740140ea10703807008204008042d21103815691241c90b10000c0300210400d0410b01d4400161144012a0955186015401c02d40c103e1004c000010351172006055039821595169543c1c070444161510416031000010340b040e549041e10405907a1001080c407219504004060303482622010449007060308889440301648109001d20032a01150f03141490340c15040d0840c00c041d6405135814540340410010400c02400c6140d10314004d2882a1300080c6000c21400c00030080350b121b40000c0e04250405084c41130b25501c1400860f11180c10440e440500c42e2034031003440c9044600711200c0d82500010038a00c060640101d4907021520110007910701a80b590040d04070a881620b00d01808a00400c0b90600070034401da025503404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 311597041 1250 311595791 311595797
    0xd02070309060519031e061410020d1205060a0923180309060306030c0904080408010c021504020f0102010905072d080a0b040c08060c0301090b030601030c12030905041a100f080703050601 82
    0x1204a101c4101910381a4102c600e02d80702008692303040703040440060040c1030040c8060301c4501120b10008184055100c550a51241c540e00454401d07565003e240d001040075500402142841c207554500c41e40780350803040d450442080004c0d40002e40b020458040d49400c0000c1e41c540701e40042000001d4002400c00c64052007142d40e4082144c403000a014004ea00070000c40303884918124001d801c3d200900741c070a0440d041400003003882010988800c3e00990304940c41e2070740c1002000100c0c01401102d00c00340a03446403040001f0380c0c0001060440051091540a0540443c5051910035984441c801c40c446e540c00f403a0402c002c501105403854005100d05154125169114031b040e1a0140650780c180f02c04100100400c040c1d0f1083c81807220080d815070241015601d90744900c14030aa0b907200b1884c188415101201c101071081c40c07640f01900c0010720400101025000c0c10103c10341d00d040c4903005080201c0d06500103030248400e40307050f40103139941604079030300d4000841c0503100241920303044c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 311598291 1250 311597041 311597081
    0x210703110304090b030f0c030c12030d05010b1b0316030507050a0606031203060e040308060105131701020702030f0a080702040c09080f1011040f140a0b0d0207030906051903 76
    0x3440d0018001000203200800003c90380075003243c200342c2403540d40c0d104816140c3c005202c520090710049509180c0d40c0b0120390104403240540c1031181540300e4100c1e5900074034600400440ca1250510281c44d89241c1c55903080c2505010410541c0d40303100b050081c1c41228201d02820340040c0c490303802000414828801d45030f00d10542e944400c1507817203a40003103901164406070080360f03540c1485180d00411010313404007003900302614080e0281d1806460319040000000e6103801108849500070024080b007230361884010310f42c000c154000e401250081307129000307481078403417480d0b4001061442550000c030b410f07107403901d00c0c5d080100400050003008103104150314005025407040c00138841200d03280c0d0240c9800fa170119610030407945412821f5160000903c001e10020140710031440941344400800c41d0912100340006a124519034800d0080ca4000205007004a0346034025040c454480d8681603184c80d00c4eaa4265080d004a03003d40c02d0b400044041c20284e00d109400800301d520000d141200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 311599541 1250 311598291 311598317
    0x30c0b1608031504050a09030509010f0e0a0e06090711031902010902060d0f270209041a0c0a02010b06040515095b08180714090702210703 61
    0x103290001c440c0f0f11105084015081c0080c102030041c42d51110200c1003c102d5002c0e0350750060040d000d103045443c1040480705200503d00d000d502c501d03503203801c001d00003901c43d65a102e1041103441d007181d442d0b014040714004200f10601401e146c415513a5040041d40c2000e6000003610026021018210215900c1e12501800358803420018000391781c4080c40170441d1522280d0007010781e11240100315012180e83d11005c4c1c0c0c441c007221454605981160fa9500a4840b414005644506055000c01081d0a141805a00100b01000f401440ca0702c0c1c000f0301c4950420307030400506000300e100d01c64100445807144003000081500900c0d0581004050520344a5203014140210020401d0311000c40d0f0044035801c0342c81d6403100041c102109940e0800503940130b001108026a03c840c0d100000d10404c040420f003001d007540103600e98045000100c0c0d803020b0381c640d008514040c00c041110301030611100425440703440400c000c00404074041c0440089d003105150002e083d80840c0d016810456040d107214 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 311600791 1250 311599541 311599553
    0x6080a0204090212180a02030303071b0501020301121a0708060909100903030605040f0b0d02090414030a0201050703111315020c0303160209010e01030b0a230403020105041506030c0b16 81
    0x11142da400034040c0117191145040603020b0380301709a002161311501d00d110050341c000044981c00b144c3e6182480014041c3c00d2050240c443c441401012540088008076400845e1a000d50b4424090b4040318002ea100140241c080e0505680303040004402e507001406074104110080c1e000a440412614500450314191080f01c20182c8110002606d6560400c9980f41600801d14209151f2000f04503003000c44002820356005d00100901070350355480080c0c10f2145440d018060f001209058a9030b0348110500280240000c0700d50306c0c00f1a141203164901880b581094800f0813502144051045051111801e0040801d05200045224102c0d0f444a19241800549801c64072102c00c0700300340410b0b104001c254441600102e0300240600010400b14290b403801070741224480600040f200004107035a60055601c0d1104005101c2d07400c248001c0503415800b00d48180c1c02110f4019041c010b545114055520710712000e0804251500700b8020441800d0040100d0181203500d40d1980c07401e80d07120 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 311602041 1250 311600791 311600797
    0x50403050a1506080c0303070611120a0504170301060c03030911031e010c0e0d030c1a090c0112050c0901030e03070501111803011b050703170114040f020403020a06080a02040902 78
    0x48031402d1022a09076014242405000054000074010300381802c12480425a01d0081000c05000c00751200c071400c01100a0904640207010800a90303113484c548150700c080503000594045680991310606080052200300c1070781c0c142d85107556201012010b81d10308031b028103030883c0103035000300c114040e41d4801c0d5002c001064407031200c00114044046880440c0e404c42d1030b482d8140c82808800d420b58035240d43d03030500710440103a043c10242ca0721441c030b003400c000c40000e050115514208060074419443d200284a5013030f07003000d0f0b1790748000c0d51018001d002034400c00e440848049100f0301485100e98060780006034080e000754200c0e410030105031101401d40704150a8040756050018400d00344d45001c868031286658107800078000416400e22410fa03440d0008400420814045050030415200c0e00345040400c90385801c1c28290350b11035051300301a01c40c559070f1500c1113107000e0200b15004018020b8408032900249401901840d0200c103860b00f030001003419108a50800000c505000c641c0f001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 311603291 1250 311602041 311602043
    0x1118150c01090618240e1207060c020a0b0606070503120f0103140706120c11100e07050405010e060904020319120f031401090b0d0804080d140307080c0703050403050a 73
    0x205200d0360324204003013118100040c1ca10b2209150680c82c020032800d609140c01c480801c3c01a0380b26880407880f0100a1085c040c416207580556070581400703000500c082c040403030240300d041104900031071082ea5919035240c80100002c441c1c01c0061041c1ca4580c000d0240a4043c0c002d680c50200104601d17100f0780011200d84102c5c2c4004001801071114039030111070460b0b450401880c07110304051024000c01c865109051010b901c450f0080c1c0381612500310040d0302072829080390701d0601c0402c10000904140d07103034244148210329000500349428003a4034100c82c503024901000c1d403140c9040c0140c40358014402d907054860b14148043e1022100000d84009004162441e480703840180000d220040b001ca84c0c2c801c045c2000035540702055145041411250303101400200c00607001e012031182018080d016284d81c00116001420500120300303000c80d80c44a40ea640e80c1242d944044c0300c0c20b03010540e6407500040603007000030f0a4041e00c00042c80160f000381400b0341015035950315145402041d01c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 311604541 1250 311603291 311603293
    0x3070506010f14060301030807020418021f110a08070b0717040f0302060a2c0f070b03190e0d0f1e020c030f0340080618011118150c 58
    0x202c1005071808011071089200c8040303a0040c65540b458644003020300802001910460395210001803207001480d200f00708a0b0301506c8001d00c41e0141900040254406600d0004911303030603030802c4031500103c0c0301c42d0038980c442c2a0600b845802e84511800c1d220050005090140041c90052001c00c2500c0543c8200d00c11180d410981d1080d18009040c000040d00c146299400c0070300170f07105250440c480b000402104101a00b4050b4600c65582c58110300d050312044030302a040b4041880e0b40c0c00e0005610541d4003c85d001e83c441c52030f001d0703002110f151111160aa0700281c000b0808d01c1c1c411881e0307009000c1e07d071410702480210000075007818080200c0210240c0e00240e061000ba040510030300300c0740340c62903000c3d5080100c0249c207000c041c1c18800070190510464805c648207840c0b107408020394442c01e6200041100d80351039007141e07140c00641e00c070b8140c2c049140d0102c2c80c3c10414000d005031117124680d1141801010804000200005070a60798041c090b100c00110700b03c88940582040380c0300030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 311605791 1250 311604541 311604569
    0x405061911060105150c15070f0207140307061409030312060102100504050d0e03030c06040501090c240e01121e06050406050d020607020307170d080a0e100e0307050601 74
    0x480c028003015a514510241e0740c0040c00100401d83d00d010919010003036102030559991070110f8540d0420810a00b0850f01c07100c800d060050080e4030800400b200220b41d004c403003041e03854031249102c54207100445c2d64960b00901051002900c0ba200300c4d4101203040d5641c908160180000074119049121100d6545c0d5183c4104101c48d1381c10000b500c02203205020070040c5041603204c440d03e413141503100106001194024100544040007203807402c2c3c01400a41d01c3d513040030729005e4040c003060881038076600c0110801040110700040054200b030902d602d002c010b0100040c0a442040c180c8000c9818480c615030403141803021401580caa000940c00c032107141c1c1d1032b956500d004807030054011501640c86c00750188210303111a461941c200e42c0448503e42c03261014400603181c103c080d0000e8201200c02c20560fa40100001065441d2450f0b42c0c803101d80b40d80c0d5201540381107440c11808950340e42d02c80040c030100a40d0591004200030003040940e0314001c0d041c6c0304c86191100a92240352400010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 311607041 1250 311605791 311605837
    0x3030c0b060d020109090c09050909030903010b01050c0d03201815040608040213020c03040e160e030a1101020f1614040c02100509030403060504150c09050303040317040506 76
    0x1010041d4801002ca8201d0620805600000d140900038001c020206548000030701046000d81d001000400c4020080b20380ba2070500e13141030300c0f07800828000e8025030170500e48030f2256014600360341c1240b501000a05421075040d6045015014441e450840754030010740c1c200c04201e000b001419910030359000008901c0941082c00200050844141640702080c08144603035603005030940c1d0071a4044403014000219840719000a2041242d000600d1000050000e00001d01e01101840381e8139110600564441103c400e40e0100e11400840d585904084401c500082c041d1507203008448040c81100c0a01080c0e58020340b8000c1040d0410000f0310511b0300401c900c01c10041140803109041d0350501c800b0300b855038003a5031600c1c001d1101303002c01e0303c1d480001e4000c50200305840c01160401ca040c800742c01c041c10401020700d60a01e41104250522500300f0590713008192050031540050015031405107191600e0b44440580700e81c035032a0303400c1000009034aa680710050f02402281038080100b50000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 311608291 1250 311607041 311607053
    0x41109090c1c0203090316030801080607090506120411060d060f1502120a03020d05010609140909030f360a14130f0e1501081002040302090606210103030c 68
    0x4020a50032502104001800b400708071641c0100d40101429409a26515070503141e84c1540140d60440d02009003490030801416801616103040302d02c058240d906a445100c0300301c50102d001e0080701d400c04410070815010400084260313500902412040c551004800c000030500c0d844500e816090540300c0c0400d00607a4040408070300100241c0865200f10041260042d49501d0100c090010700c080210342510f0850080d01103810b01d185152040046607110305020300300007200d000d03802e50054102030024090809101c064050f010700d40c011070428052840f20443d990212906003480128911402446144404001c1c407084400d40b001d44e0010149c414460900001d034410445556009039000c020380720980300c0d02414040030000702e04000d1452584000d0f0500c04148a1a40700b00c040c001441b00f100d1107000d050f5000c00f801d80781c0d524014640f481c240d0069000c0607611550b508c001c0340c4180303001801440070003e007246148482d4403410003049007681c00d900990101d03490002d12010002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 311609541 1250 311608291 311608309
    0xd05030310050d02100c0311030301080d09080d090b03061504081b19181e05060f040b01090506071a04060212070c050c040f18030905030708010504020616030e041109 73
    0x4420341d43d80c640305000780c000034102455201450b0074803111444100c2418810b00e42c00141030825801c890745c03940d40c1c040480d90380c2190148800060184c280c04110000e01040211030b450f020341c0c1d204c0480b0705000c05613409620140502e940001080045041c1c4a0210054002005a003002e0000600d81a080d25081842000b11500c42c4618220904994004042c20025140d0806002a8460907680540e0042016020050250302c0d84d2500100d06d0301ca68202c0b13032040030191002941401e402080c842a1030308a10103d0108009900c2407240d41802c402408000303000b01004880110009280c2500b4070301070f10b081d9000c075000942002901d5094540c07a41040040c80d1103ca15580d50301c1d0152140d100c450fa8a22464580c0e26160f5021965040705042415410f6121006040c40ca80548114054490b6500a0040007c0011003203070620840e3302c602e0300585011300d08107540130a1090640d0590085013403150810140c1c1482d1a107201c2c2d0408a40440c46065880032102d08200c1c4c00c0c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 311610791 1250 311609541 311609549
    0x9141204080601230904060e0c01080106050d0906021902030706140403080a0507030e010c0203130b090d1401021312150506301212010801052a090d05030310 69
    0x100104010403411a0005401c1e044814003000c0e0701d043c07024071804513503504805103599840b910840501c07050044550103120000c1500d406c03034005000c0c80005407000740702489404040345003031001043c060310a0f00100c400394413640006141012031031481e484406d00080d2800143d00104a0000304140d901c111246501c0d020082040b038a41036030300911447d801010600142d84440118075144e001e50004070000700c41c40001d100040ba02c0c08002d5482d008000d600d0301002d108400055400118822103810200c003604140080c42c0c07540710400d000f4198158200387c0d65081107001803c45c00c600d0006c000c5c055440030340c00c0c00780150034021004504051a203d2191802d01484a569951400400350506c3c7d1107030140b241c0d00280090741c01c4482c940c00c1803924055280315000101c0d003000141800d90364408041043c0c0d8854403040c0c200c1c1c1c0c2c12620303c0e00c0488010f1a0b030034015071040c034241c0c0b03080d4082501403505410001203080d0070052a003c03503d5030b00100c140302001d04603c400c1c030050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 311612041 1250 311610791 311610823
    0x112107020615060403080f0705100c030c08040b0408090d0b0106020109060b0910060806031218031c02030913061211100201151a04080312090d0806130f020405040914 73
    0xb00b804800050b08520843c80014240ca800240c40c2844109400035680407507000802c0c3c4040007110007034100079181c6440500c0000c2d24110012a040f03000ba01440d00540e000040300070f041d600d41d40d9407041544441903655021308240e450100007a0b0580d07419000c0c10956002080c00140c2d0310300300041d280705a81041c820b512903401c0103c1141040350020032100c1900e4690300c81c1e112440130a0800700d03030b111a11000e082c00100030020380b806a07542c4440c01c0c410b804896219108690004504800480c0720005800c204040d0282d0f191901c00d9100c1505840000200c2503680c00204001000d115022105920742c0c950004131454400030010881045000034045d080103030850810b891303117034000c2d00b0000c1040c1d41d18110a0207490180c4001d464100c04503507407962961202c450701c030005c0f81c158465200700710785001c2c3e85101d0780c441381c00b8810240c82c1d086004c980599400c0030300145040518080d502340800186503465000759400180508152034500e4000781c245410200840c64210324 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 311613291 1250 311612041 311612071
    0x2e0908060f0408090f01140c03030402090901090503030a02090f0a06021609020306130905150708101d040623010603060303020f0705100c0510090b160810091121070206 74
    0x403900d0401207400c841800c85d12030300903007480001658114925204036024400c0840d4024400710004000d40c0103e008031484180381d640e1079074083c01d8801260000380071350010320115501c030004e900542001100101038550310389020000c9056014543c3c0b042005a10004000c5201c2d00e45035180c030040c00140505520794034190001c140e550000001100d03080381e070b4280c4501406070a02c8900e25541070a40d00c504142003905004000310800c0e10030381e02100c0d00110001341c60a080c85000c502002d036080415080c0c1d00d03901c1d80c8004101750032680090740181d00302a15032000021945011700000d490025502c0d040d420000e1519500081e07468540c0e01031a024051039907600300d4480c6503a03041c0740c5071344440301da881d04030300f0140c4110035046c84500b040510341c20003c164031a544210403003a120141950420401c03600c1110965030141d9940041109201500380b03500480f0f42485004075541c94140502d400d542ca007111070302c1d44031030030b0218800c2c484080d6050007402e4100b9205507000c09 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 311614541 1250 311613291 311613293
    0x409020a140a09020f0307020708010203060d0f051e010f0e0c030a17040b03151203072a03050f06040c0e010602061f091b09050103020c0604022e0908060f04 69
    0x140c08101409012040c400c900040070041d40c07800c0001000c1c1c40b10711019911303000c079072028900d541c20035a030a8016006040d000705900780c0500c01e580c413910f07000303100e80684015511124090b5540200c181c130203005841640380c2c00b4a040001c40c0929001400018204402d400c070b040465030400604c04040d0414501c10001c0d03540040c0100c1c449411103850290b12055540103512445550b101c01c80356074000c01081114015190008114541501e02040c024807205003e5164411340c8801031000203d2100c1e400704240308104d08044184209140d1105e40c2c59480c1d00d45000c407031030126061039000307034100002c10803452810b000078141c404501c889541880c07006502e640c401014040100c1d001814038041c050386501d404d00030610b0540420008510344150040d5000e9042c0040c0071842041000030207502c2403003140c0c02000c0e61006001e42e5100d40e0700b0000309403405d07003100b03034401c245403084204a00030130250715804010361a104844d07458070751f045003407440080000e5102d16156007000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 311615791 1250 311614541 311614549
    0x3090705091006120e0a140706261303020106050604032010050a05090328110109060e040e010f0e160803090105090907020f010204082506020a021c0501050f06040b040902 75
    0x11440a60b940c01090a54070a5150b40c07801410113009008004041c40c2840447c4000c907251080e41c41582c1c5070720b10000300111040c00e042c00140e0142240d0424000201d0020f02e05000c1c210b4144644004541e5507a140c000540720b4225800689001c0f64040e89412901880d107140080c118054850403022010044080c00e0b50040d03003c070350248400080c510116550038030141602c8030303840307050404030a0340312046007440340302d500100d8040c140d21058940d158000c402035012114642e4808484001900510016240010070107401e5900d41c2c001411f12980790140d1007250652a00405101d16500c1e00c1368a48015a401f40701c072034108010000e22642d1010442c3c0000307105440281964507070ba041249040042d010f4102e130395101080100707050b08085a101d12280d41c0407481d10071200c2000208039103103c148034070000b603880212400018109078000740c0e12102000c20b001803028080e04d8803400c4d61707022603590700d0124100c0200700c01454148900040204140d0381007043d92030030380c007203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 311617041 1250 311615791 311615807
    0x9040f0b1005073201050702060606031602031e0c070e0609040807020627030c0303032401110d030501062c0913021c050d02030c0c060306041103090705091006 70
    0x2a10401074000f8407601030000307030100d40f5281d10320030703038455864902101041c0f04181d031600750b0440365080c000494911440051440d01440d4000d0502d031540c0c954010a84100ca0060b5040f8154001844920700342039480c5c40e05010100c0d4038541c0340d43c0781030601105013001d00e250490582e00302520180501ca40302c1641c0c00741d102d58440c014560b101000d00005070300d40900d8044000503800f0040000c0c0d013448100000c40080020f030100c5550400c0ca0007019102c6c00f04440c0c481e4489094140e40000c12010403a0005040c0181041c0107032040a000103818100240c41e4000030940b00c5004009c0e03540e20a072408401c0765221141d40c10040a400120500d00191440911800864020030606861005441507582d4000e082801042c80740082039607490603140180d406004140005140c90700110480d602c070742d1848090f00e03102d20850100940c42d08041c20031030700203559041140340c203c0882d00550061a90500910b541c0c0d14040401001100040c4020303410081c001d800c005040d042400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 311618291 1250 311617041 311617069
    0x806100f14010c080a09080c01090e06090a06080303010b03010612020702010c141e061005030303070206011a04090905061005040b1c08070203120a031802100503040c0801060b09040f0b 81
    0x42800c241d40800d00481e04107120320300c040e2030b0b00e4001854140b070030342240c0748008031040034080c1c940030009040191450300c00c922649000790035020018040e1319011542c65803082100360009100398687d04500e00e035070000d03004419400f000000502c1a1504001015126602070342c0c25450b180d22680020014020000010a070f42c440500012649500384849100748440982c1c2c0f8500c0c0001e52a820760328201921440c40f000c038640c401090342d05020088034450700311600100b00d1a444c00b0001f2024074140200001c0c4284140700c08544c4070014007545c0b0402d40600014949401c0100f05604456180e40c0100e1141e440c0041108a0380c5035030498051500581e00707413811110076410204000e11510100a41c1400740242da03210701e100f460301410f550000d5540404c1440d1000c12520703c0390030101d41c0a0340c00305014050b600c070b00d4403a400442e48944110b04075502690759a80745400d4403c1904030301d41100d00892116aa07050a00ca05002c500034018103011484681012460070800c5c408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 311619541 1250 311618291 311618309
    0x1b09110f0c0106050405090304030b090c18090c03010c0f0318030915050405030f0105041e0f0b04020616140c0105270a18060603111201051210150806100f 68
    0x1d507141240d1001c0d030210b0700400024006020038a8403680103501d9500902045500100e14400b00d6183c80740040d100405600c050a540070000c04900e00701e01c200c800604116041c4904081c6003442d0700d0030f01400002303484a840303154280007018006025141480c0a086540c0b44c084e40301e40100340c0c4501c3d00e1040303c100521f50b01001003080c10440312442103820058140c0302d10080030005c50815401a8800c90085402d01c0480e000307a03105007000c2d002c009001e400340b0182c1d505040442e07a076121941d049440140301070b1403e8415100500c0c4451910019036003201022002c214062081c041041189000d00c0d0141c41c03c0030480b10725802c42c1098043e100010503903030410b20b1a440301c0d00302c500a0400c000c207200c0202c40450f0103801400c51030040c100060305004114001180200071385540480042501c05983e08000a028002131018421031039445420740e40c2d0580a00d40c8100d003440b081c02c0350b01361851401c0c800c1c0d00b4601a00580952080d4407144803c02900390b44189590944180030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 311620791 1250 311619541 311619547
    0x402010c20030601030f0c0e04030f0509040204210c210f0201020a0510200909071206170304172a0117011403010f050601021902150301031b09110f 65
    0x10081c00c80070090000c200e82c15105060000c0b003840710b18051055064841e1000031150760b03d540c000541004141c0d002000302e08005070050085004101030640302c000500010b08041c2e41d040c08003250080081032070015140c030303c050700134414480700340c5000e40a030349206002000561a0340300411150003018180080d0305850b5000c5a1003030224061542e0082d04484450000350595030090a2000c0100008051043e43d400608140015102528401001d90b8041c0d51a000300799524036401c1182c0a010383d450001061a52040b5980c1c061818000300075900d840c28503480f6041400e12100c0450070341c1c0211450444c2580d1032030700c3d0b282c54000070000000c02d5450340050310301a002c80045034000d545036001142119440c1142e103d00c140840083c40080c1142e0102c5003120800e544803401a000f0102040b0000021124a02e101e840a4810071100d40203452090940d0001c0c0c104640e5240907004000c5260001c01c041c0303000d0000c030b0703c00b00048080000e40d00312038442c1c1c25403480e48803c04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 311622041 1250 311620791 311620823
    0x1d030102120403080106081b040e10090e03091305090303010b07170304033b010e0f030105070c0b1807261b0a1e410a06080402010c 58
    0xc0d0169400081c45038440105800c0c50318002e000c0740070900a400c0015403c40c0081d0540b4030004011303003807130203620700a483c06052418000c04d4030001041c005003603a121100094007072030740c410a034403401c0400245844e20400410400c20b4040d10340321004c59802c02080c07120407000401140c0c1100c4d0611541c0d5507480c0e0320b1801d44004901581e260901d030030040100401d00d50446210130000024141c6010503903100500b9030082d00300c8110270020000980100f01942d4003c603180300b05120000c12501140b10003500003401c3d6003044410400140703074050351404200e80c00b14100c2d00404020b026061030011001e083da5560039503c1003c400348031145400c401351a1720702e04013149007104019540850f680496020b012595100b009005400c201380000fa81b15204c4014844202c0110113002124580520355140118400140050b8101200d050791403003004464060754044280b604d1428040c2c1108000c03a00c0304641c0a0814040c5000800005030390005000045a5000c1052030620a50f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 311623291 1250 311622041 311622043
    0x503032a2509050a0e0a0b18060a15050102030406140a0e040c020705010210060e040b0a06150306080106050108040f0320010e0604020f01030b01090905090c06040b13090209011d03 79
    0x59500d41d05100107044401051111440c1101000d5550001d028001034480000740d0b4125501c100d43c4c500d680e0442d82c1c11710001803200369100c0d0481041d10310411000b500155240c2480810b503080d50450344c4d00c1c0328885141d407100ca80500103143c24000345040a28013030020b0181c0310000e44540e14580300054103d886409a03102c07490510000e001080366021819000c0d6032450180561070151160302140401006076010361020b03034807082072800d140e44841c1d580c0088000060900300c41c07aa00c80c180821646549036042c42401d904e640c021803400d00d001d5645003190030766013101d4100043c103810030010032a95180c3c10040380c0c1c10326045505480782880640420a8034108c540103500b8500402c07031007940060b802e805a4000c03511024491220301c0150100c0f12419a4140440c00c102d40420400e40c09501c00ca50025055066841e020b0606d400140260b0141d0000c3c0b07100c44e004905401942101d41c0307040050228403508614248101c80040d2000e000200c0c00000020003c43e601c050f614 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 311624541 1250 311623291 311623303
    0x1707050c030409020f12060f0d03210e0d170c04051309140a030e03070509040b040f1205030405060702061b0711040603030c1203020a08070e30070503032a 68
    0x890f4483c03c40d15442d44000e00e50181e407150a03440d041c11a8040440c00c02c0ca0054a02181200020405225803030142d60944820b6001d031850000120410005040f15449000c3c681000741e031040549004241d000000d03043c0c0080c2849204914800350400c5450b03e0804201c0303060b681704440f280403175024500307000c2c00b0700081000200511203580d9401a20000020028441c0b4440d841e0340250303004c1e800506039200060302c40c941e4000d101ca404140402e0114498075001402800f00c052070b01c5440d02c5111000240300e21407000a1800020030082c00000c3c0200c58109400340b002d013005013032022041c0c0e04084004000c601e400c0000500740e081000d1409003017607126020740f00b8801d081d601d00b4003801e6118445001c2d0f03590300d8040c2900d05041d21a2085501f01d543d1529000c0c0c0c01d45581c03104890016501c501c148e081720180a5481c1c0c61340e444040610744000226600000303001d003054083c10301c7c845500c05030190b0b00c140030b000d03541108406001c01d2452002d1581204840c450740342341c5800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 311625791 1250 311624541 311624549
    0x807020f1911040c03050105011407020906042304050606010f0309020f01050a21091e050a110a0803070b09070909020105190216090917030f0a0f061a0301151707050c0304 75
    0x80c0741140c1d8400300303601760300018100d0b03000b40c0f0f4481c403581c0d00d065244c15610038640e0007980500d16800050080c9000c1d8800c1e10408691600820f0072020b004100c0300a010645054909a0000d020402d180d070703001010400c103a08914040c4400003c1e41c1c080b42c0c1c007445025007581409000b01d40388449904c10f0003442185565100b010030100780800440000740205501a280c8070b02040000aa50301d4001041220540c01802007100b00141d849903c004046000c0265112507003450015080c0e2040014120f89402026490000d0a24003800d030719081a9034020040c00d820209048050303a0000c043d68035109000b11a0386800140700340403814100c0481c03008100c91307610f020100303411120398003038640c540c030500505607000780312207480b200c074002110281c000c0605500080c2c10b407070043d0460250001c1c1c01c01c0100b0700f640c4460004002c18a00b00394030402ca000800100300d48524900e840e40d640c0703120309000c411020048100d010f030f0300000306400c050110000c2c94425603102002228020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 311627041 1250 311625791 311625799
    0x3030a090e0603031213081306030209040608010c0203040b0904140709030c0b131403011103011e2108071119060f110c010f09030c0906060807020f1911 67
    0x14080100020301548090302607150004020400126142000422503029038211240c803c41c907542c50402c000d075010001c60817a0320810900450a07051440380a0001600e240d442c0982c8800132032042c0702c1100c4144d40010410323030500c2c054044207900802100c0590710ad0b10900f80d0b0341c1004102107405041107003011150441c1c6c0408100b4081d90007003045060301d104040500c0c0a664840c04003045004182080301e0000303041404102643c08900203600c12800640080340c01019049042c0c51508260b20903142c1e09186854410403c160b006000c01506003e07139040080b0011003c200000244044c00412946002501d4402e0040f081030b40f05e502c0100a290500c202d407a00310345c2a512206114803c0032454a44600d502c65008000010b004918031008003034118090004440d01c0e041c00107503006000c10341c00c5c08000700d425a00d000c0c2c058849448041a01c501d803c80082c48090000c2400003103400c2032480003030420300841c8150081e54212020701e1540c0c41030800110003c9401481c03988 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 311628291 1250 311627041 311627047
    0x6101b0803070f050304232104090b03030c060402010c08130b18030a0b04020103021c150608070813020d0c09090501090c0807030c0b1305030d0201090b0612061501020c0303 76
    0x10000858021031007414a580c0d02c00401c1000c0c001a9024001a60001c051089100d2061000901001e80885491254080b50301e000094060140b2102d0000500c1680704230014050000700458040c9045142047e4020762a06a0070710a064955034054002410010030780088014002001d0544030342c98039071598008440e82c1e481504040794010781440202000c0c182c00c40250385008500c05201caa0428905a802c0d5281c4d40110000d41c0a020040760080c006107d48661036031601c1903404a09515492408560610310090140c090051000b801c00c4508820440212908040c4000b26a815a82c40c1014080c0745407494241c005904005016403400e9060760501805410400205016140b441e00d169218a08181c1781c0483e4080175140c1801c0800c00c01c8a09802c0005000412000c0c00708290340da00c0e21700003400c040261201c040181e450f12040c0c400d0100c103c5119030850011501040c94849403924503490f61310082c294515041c1c14518144944d00034400d40300000c0d401001c0d640c2e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 311629541 1250 311628291 311628293
    0x7032105010303230d0e03041703071e0b15190e0105090a06150315030b0a1d0c1503101d091c0c08030406060e0a0c02120703020a02091e0a02090316060806101b 70
    0x1030307250030401041c3d440078cc4500c805d151898010880300406a00060150002d03558024080518450342408035080601c01851410102c02d54004001410312a121504e03254504420015801c0c00901a04000d6140c10020049201030418484c40282d09090101d001400c0021030782c07808100d58805400041711400300205d140490303014010505540c807501c1c0b4100c1c11118401d80da041440056500009103c485000a421342805580c0c03240c621400c01450329140c00c10400e0450b0703000e0074101030080840521040510500c0b0040d071401842e8242010000441402803080021403005042d495001000c0340a018542c0c02c0308025000710300300700c09a0704040c94003100810031120300c20014020107922000c102da0200c00c40d100c00343c160b4021701110320a9020000c49038000381816401e80010300d0080b24138008154024410070709c8090042c2c98159460034542014901441c02081c007502d401b051081980005034070f5000782c0c00352406140240d50f031a094450a4020005100044a00035020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 311630791 1250 311629541 311629543
    0x315020403061506081306180b07120506060901030504031101050c040503070812182101021206030d120e03160605221707032105010303230d0e030417 66
    0x80724030510382081801e0032000b1006950320a4082d510010f0005d60100d8241e061101040222134003442001400790500f24886440f03000450341240c0c2c0000300002c2000c0300d50880d034035603205610684d041c0564030340800087c01e103101d001caa00e030505543c0c50100b018140315000d41034592003180c2c0200708a003030103104059660010310407503100c1d1141c0c0c40b010402c11408034804001d61214072203d414402003514074009450044116a0050f000400494141007104d00c044a80c000540005036602c81602485854074402000729000b580b04107031415200c2c1d40400c803120200c8025000141c0c1c00c0e110700005055100d0020121003803d1115071007010700003140e000b503005041094503000002035403151004e40680c100d4010f000d02c0d094183c10030921010030000c1c41e80b0792103490100d1402d2003003285203a1001da1280f07403081460381c4030018020075411070580000b04410007419a014200018894a1485032110a0302d2098031600207110000c000c000361000740c0043c400c54514a10384400d41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 311632041 1250 311630791 311630797
    0x3070f1e1e020f0622170304060b0405010b0d0509160b19110d08070309020d060506090903090a031b030203030301080f0c010c0f060b0a050405070302070615080a0b10031502 76
    0x116001d070103980098075a203800007952a00040b0a080a001943c0d643c2d0361011040c0f10311400b0455024540c440400010741c400c00c050048000001c0c92512810941064011111380c0c2d00185c0c001d0703160400500000c06c0d001d00f0b842c0c0800c840342011440c2e80d02c074180107007818040d0203c0441808c0114000c100c088840c0007804507200030422413a030050168030210340340340501d080f9600c07907002071b00d50710740c1244989803072640107020f070030041144407855003c620b008140b2402628155500c001303000c100e1400019142d04406030800441c10000d030140021070820300d91100901d088a40700780382c00c03521f8402140c200115001029281c4942e9504034564480c9510039192040f40203030004003c20750701134440b4000050f00f0842603500d0155aa54980003043d880c400550b00c2960030000144550f80d82c02158400d81280d6400360b1100c60740d20b80348080e00c060004c07444000751500c03c14055601d0008413407126940092403141c017a00c8603811010100c00540004d00a841c5440c4800040c03c40e507001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 311633291 1250 311632041 311632067
    0x609051b03010e010603080405010503041e080d15050a14030109020d05010203040b070504030f06240b090f0a030f110d060903020c0a120c09050a1d0105011a03040803070f1e 76
    0x81c4294507281c5545800c0345c40c0d60000034290310080c80300344100d52080c1c001d164400d00c240ca2a00406107007042d400f100120700a012078524100094125100c1024023a8040c07101c02101c3c1103c9041c20100041d048003a180500b0510000c002a542030943d02500050007041d0040c1482c0501c14031410818042e601c2203a003621123601c51804103891038030039405c94080325046603811121030910744d134800107448085841207001102e00c1c64030400031240350481e070003004040d0409a40d840088140018501c0c0d2140740380c412010b00600708040384815032080b44256200d1000104074080d04001404060441000b410301031502d48101c0c10140c00180410492200f00d8140d94441d03502c2185000500003014000c2c100d15070000c04201942e610b800140c1c2010b007904012600d1007524160b4a07251110115584041c0c2d1118010080d11404042004004580078942c43c65440c242d00d43c039038148006040c081c208542000c1c0d0030301403803007606407005001c0d0071032002c000314400140041c140d0110f041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 311634541 1250 311633291 311633293
    0x5040f06030215180105030411010c020a080619112b24050102060a020c150417120f090703030f050a0e090a0b0102060c0306030a02010c050f01020a02030c0f03030f060d0609051b03 79
    0x100c544e41503014000380c07441207500c00001c0d01076800b400300451f4140d00c0c8200c201d801c01c6040c0804140858103100d041e1040069000348074400500d00d002c807082d1050190408041c107010070030701742c50545600e203030030031300755859040c4080002d0126a440148001c1402c01603010043c003a40b0380707009440d1007581c2101c4099080b01c2468070f0300c8002400724802c1c03580b9842c0c103500909901241181440140c0d40c0180540c0011022000b200500301035684444807044000c69840f080004907418621401c2e0085401030007031121030304540c1d000d4881000b00078500e05008020601110316407044540c6111688090f29003075180c01c10040f04000340c20141d4a07240036001e036000061000314424140ea1048100500a001d17541e09a00150f0312081c02d960240d900d40956500e402407400c1c00d00080004030010750096580341c41e41c400c4103080c4030a0354140265a04100240322403443c1410343c90342c0000c021103444408040f6413500000515403030b83d0042003802103040448000e0101507202c10489001d1b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 311635791 1250 311634541 311634577
    0x2070c15091502060708130f06050c0c240f0c090a030803160806060a120e0304060f02100e0c01030e03130902040f050a0305100e070e1611010e0705040f06030215 71
    0x19000f6030321340604407a54400600c9410001e10300b5510340021107090707405103840081202281d00c94600740d4108440d2180740d41d00004042c4014070003008081049007800c1c10305181c000315840000307000d15014003a04107113000500866a4000850100c9241100041003026411742d42c3c9884901d940003282c41c411090381e0100140b02860041c1001c611070400189014601225030000761002482452700c0c03202c250707940034521200d01040009001400c0345860340f4a40004440c0003c2c035148624500c08055824503c00d80005100040c50124140003420f000c500788040041c05865030041c520f07060003800c4a080005851009a40140140c0c0c0c52104c0c50380700d1540701c90510940b0192480014a55400074079081d241502c154440514049901e040e181c14551320482c82c0102a02030b0b80c1100201414a42078613003d03084101c258103802280e00900c501c41c4015a180e4440881d031103082d0042d500c1d90713100820002e9684c01900034550060030a45880c0c02243d54000c44d4100c003040600f02c01e40c01e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 311637041 1250 311635791 311635829
    0x80618041406040c06031a0a051003021c02090a0519030215090904031e0e01090b030408090d0311010b0d02221508031804090c06030e03040b0708030901050105011e0302070c1509 78
    0xc210021025180509030051041c9801c2c144100b2b1080400b01004160b4203216600f204400e6070131508000301d4030540540c0300c070001400c0180c0301d200795021512840e400c2c4500c00d40a41a000007404898044800c81100e00720008042d0007841148400e076401400001080200344c1c01c40c529640a00c202c196500c09890f070f81c0f00980d103861200302c0807400708513814420400b50002100a40c5c0c4148030320b00b100e0401c45c440e0f021403641442d2141c110080388102c00d10650340c0c0c80074801d04c20403010440710700921003500c0d00820182d07040040d8010004c50100340f06014605176401ca0b2104014850070b500c0c20907541e048081d140d4029002d41c80040c0380f0070100180d00e2606000d0703100080c1e045103203520f0396132800c20294000c0885000041c03550006010006800030498054045680200c08061f07691620141d01c3d82100d1058111905000d010112070800b040c544040380d010088900300140e880860b8245680140c1d0a94000e88114442c9441c80903040e80c0a10010204d84460300301c0f580403054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 311638291 1250 311637041 311637071
    0x20d270b0115091d1f0518090109050a0b090105070e1005180613030201020c04060f0e0907050303071a1f091a0d080702010801060212071205120114030d080618041406040c0603 77
    0x20906c5015840b190051000d490b0301c0600d07902c1504407050400003d82403c042c0c3d00d940c1002c00f402e03001e9400148240401100010078000d03241c0c071507120300e040c40d45101c41ca8009800d101010310100200f060100303021810307840c800075501151100618858840900148000740790005010881c0140200d10724801581800d024a40c2643c4203442c3da03156403418940071181094004000c00120310605200264540b01071004240c02d90154417464442d0400d00c01721590080050051002c1c140720720480b003030036000e00031204e013603822609005c18104d499901d0340c14840c0000d070300d142e442030003801c032352003003000000050204034400c0c0c90705103040e030380c4034826a02c55641841c640a201e40800401e00007822080b0050030309007180c20110700704a104a1041c4a080090b0025039480c001580040501c0c541001178207160006441d12b402e41d4500b440200300040c022001c0d50408040c2000400c0401c5070800b5514000c50102048503ca40351604045100302118482d00300843c2c500f141d000c0c40440c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 311639541 1250 311638291 311638351
    0x50c0f0405040f12021608030d110901020705010f030e010509100506010504080c09060607050d09090e0708030909040c05063009030318070801020d270b0115091d 71
    0x90007141d116940f00441e15125124007407400c1120841c010007500e01e9142c0d00180030301c4041c20000c1c00464680312a14003810844a6220690000c000c040c0a0002c40d6a0b0014014044e80d0081c42e0000c07034145e482030145c01801348001038190075400c0104100a080000841d1000802c55810600040e220b01c0010b450074410740c00b408101d6041030075070940d02c0c104041015004180a004107240c50510b854407403d05e00e0b800700c0e90001500000040141d04000e004d00050a655000580000d0f85001480c566030312800c5801400359008200050a0181d030414100080101906083e662040d5003030102c0e03010040710703000c220300c0c3c0d00701100902400b41d171903110320411100c40110700c1c2d500e4400700c81080b031200c1181c079400c600c038080c1c0110b0700d802e003030000d0843c5a241d07003c0411070034041382d6400d40c24900106013401036034024812902080312400040d04488c242c141c031041c00350415000316620b070400e8004007072200c001074076001e0318002c141a1a200300c900a1101e00685031614480388440c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 311640791 1250 311639541 311639543
    0xb0a0e0a170a1a0f2a0705010c1e170907050402070503070b090303070909050402030c043b06070c0f021c02090603070e070f03090c0602061e060303070314070f050c0f040504 76
    0x1080200015901c1c0001154003032586a000f05c1c41040260aa40c03c1602d5442594111102c0e5103c820700701c42540c20100d0541010b104170040c5103030b0600c40c1e80003804031080d04110b021088030309020038180301003072044c81d01070300c1e0240082d50360700100e00700b1030303520751010100302d411620000008009507004025030380940c41aa6441600c28503010030440a0308014005aa05004495000030035035100e10035410300e00d42e00b035407000003080070f00200c3c103912100e50481c0804031032032110611040300c081001c5d981302c903442c205018410b4103030802c8030003040c111800941149813141c09030641e8020701c2c0140503461080380c5032035280ea40d00e418076440303503241c0c07090b900e10b0004e150100307003000d028078070303000c00d0001d940303400227815030f003a2180d08020301c2641c40341001d40c00c000c0c184164140c7e00e01040c101ca81001440400c6410024042a0343c0e11903d913028082000b1201c0c03030b441e182d01440171200034542140c0488825161810002c0d2031b0340c02c501005210314a000040040d03420603000c0c0512031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 311642041 1250 311640791 311640811
    0xf09140610051201090501090b0f0a0324020a030b0f031506011202090916170907090c031e0e06010614030a020a030b060318060601090b0a0e0a170a1a 66
    0x580c031100306200d24030005120000500400348021a80d200c418040c0900902c0809808100c0d1751500e0880d0b4100c6031911200c2d8016480501f00c1b51461700d600300070304c0c00c4903480b00900300d4601c7d4032603400400654510b16559080e00008000c680c2ca40d06811900b151700301110086502c01051080564803103840951804585281c03002960540c02503020b00c015100783c04001d894601c0b048001413211004980140054030b06144054105900400c0c01c041140101000050760400b0901d00d0f43d1030265128440d80301d500d505821035410f100340c000010b0004419103440c22100071410f400c01600d0038054011031881080c0000a280d4820f280b034030201c24110b101e262560f2142070300000a076128640100034103456004c0400c46484042c0218410007400341d81998103000240c1450422002824a41c10450000800d005034200c0e03104583c6562803e007440c1c0c17034500300c541c080b440f400110350010889601a5554410111020440c5681188640004215440d009007209030800701541c92100c0303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 311643291 1250 311642041 311642081
    0x1605060105220e030c10061d070203040e040503120103031112131701271a060619110d030c022505010c05210403060b0f0306130206160b010f09 63
    0x40c429030b444003c0b1807440c101a41d00d04103141030031741d14260b0f0307403010004d01d240e6070901085000300b00d80b982207020141201d00e0506003410000255240074901a401d40402940080780401a040045030040400c020f141c01ca0396a6a0074082c001082c00ca000003054000c080411401100040407921002c032410300680c0b4860500d41f810308043c0300490039040035035075090301d0003003000300c509054595060703405003203400c150364601700402c0130080300002e1076a030442d401c0c0300c401d99908041d1a541880c9011540c1002007441d801c803607000103481c00c0e00382c90140000c801c1d0450341c1600000d0904004e0303021500900040034103003500119800600b10034402c3c44105100c6503101d83c1d0404030141c041d00449210a044221200041d41001c900c55105040001c0030070400100340200d400000341203c130345905030700308030109413102d0009210340420040300c6086811962072009603051503001c41400b00300f00c8040d02d45500120f2080c0210840180200c030300040501441c01248110080092136802c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 311644541 1250 311643291 311643349
    0x21005061c1a0907030507080303010602101107020904030206180c090105010f18060e0f182205010f1a0d080a05090604090f0917040b040e07050c031605060105 70
    0x440d401581108030b036440140c0c14201420070503600407a00038481000505109491403400d0707480c141c4150301180036500300b03000400041d40c020034620352040950001003540c90400d440507000344a03801c4000d44c00349180c4148010b0503800105180700c2d070300103a41050100481c0e0312065070340800b82c2490307070f014000c000103004039486044000c0303800c695070800d103003c1e0100008004c0b111001c3c1d001900050f8078035044566078601155080c0104106980d000b11071050010302010001f0000c0c105150500444c07024145c81040b115a031107480c0e00200200030310341c060540400640b0048041201d0003070303003014080a41ca0400740218030749a003c6e8402d464914001420b485641012200a03803280e000d000000c1c141449016050501000042c0003600e00c505146c0f04d444003812009990941100344014031038284035004580a43e14030211078401680eaa880481d028840d000806e1680e020108800c501c0943d1013014500541c0b0803c00d46035580e8039032040c84080502c0f4600c504d444909a40000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 311645791 1250 311644541 311644579
    0xe041505130b0d20150f0a03110c01020a03060806070806180a1d030a0f0201020f0702040510051207090c2a1b06230703050324091602100506 62
    0x2d86000c0d000f52090b41d100403e80c441240380a4070503100c2c580908511503550080c500740500c5180801c40650107806c0c500510003804550048901e0380d070030b0594601c894a0f400c40c3c5101030301c6071007030003100955a81d5403c20008014045520841e1420320a00c4003050300e0a00a4040038801c01c4058501000d10191503e040d0041d0005082042c229035540308000c0b0300b80d10201e0307440e40700d20750000665940c40e5090004050042008000d011a4410300107804140040022a0000b50301182d001c01c0075250900f8a035200d000c80d611181d40007000384240c0b0140c2201007080d02c2100c0b01c45400300944c10000100313443d140d0306010b403410801d42150818034600c01c4071000307107955800741100c806003410000749925186a00d41160000ca404d0300c090358102c2141041008800000d87c50041c14022145d0b40640980800760800c590701d56099950840c0070244018100c846030000c00e00390903030811000150b4281210b800b00801401070740b0a10300d01950a000e098014940502010700c456808000c80f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 311647041 1250 311645791 311645801
    0x91e0302030906162f0a051324060207050a150504030209040f02040509010b040c0c08031501180b0d06090b030705040b12160807060804110910030b070e04150513 71
    0x1841380300d15407280f28400f00b00021311248103e5101800c2e030240c000e0100442e5103005146050511071640e0080074481500c1d8040300c0c0400c0c203030b880808561440801c01d00700c49240182154500007048000004000742e0005000d03040f1402640c0404103161a017050600200400f148400810340c1004104018207000e040e80b640701c2e000710f070103150004040d400101912419a0007410580d100c010048183c9814400c810b487d031518200324034061b03125643c80300103005c01420007031034440300c4503a140c959000b45088030f0329052030780740051840d440d2207203007550350400303c00015102c1c6003210205107caa0307440b8001030040024014040d0b2860042000302816203038143c95003201c02d00b1340113007011303c1c03c100781e141521286540d40302c010300381041c0310f10740383c883e0b070200c0f04002c19501404003107403e81c2100b40210909a030441200c2d943c100025920111aa00c001c041c80c04071400c004d240755002c3d680c03e24091b000c8400740001c42e107640e0b040c1101160b50142c0c50b07114541030b02d2260f01c00495800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 311648291 1250 311647041 311647057
    0x1b0405090d0203070f0f06091104060801021c150e040c08061305100e0c1903050c041e0c050912100b010518220c0203041419050609030703080d091e0302030906 70
    0x142404260305647d1300040d583e000d6801c451942075145003d030140b61070300800c030103402000d008600b0208080c5289100840807501c804032240d841980d80c00fa00981c008041c0034081e18411340c0300da0f0030320740b60900c038100403031054505501036140030a12281e488000c407204240c000008003100d4080003040c4c1e0060080e0019001c40348544042c81d000c07616060031403100b2003c081101a101491400d1503402c01a04000c2c80740f00e6464902e120080c0030700d5030140c18450b0b0311420000740c490307a413040588a9100f200e01c01a032000040703410501c207584c00500c03030070400f810070001c1c400c030b2000034015521406000900c46140588040d02006800c102c0c134282c40d4407182c2c0040ba040f10744000090b030100c030180214200103801c005803d10040b8403031484c204c04000191220111540d071541c0040c1006030324003490707104800000d003d80840c1d608100304005503401806890790b8030680e51481006000c850b50858803084590502d003031a40301c160417100016095005036240940302001c0044652180305 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 311649541 1250 311648291 311648303
    0x7090b010504180e0607020a0b010515220902030a05071d0102210d020c0a0c1409011401020f0607030b100201050421050f0309010b01090e1603110c1b0405090d0203070f 74
    0x38824655013010031155001d000b258001e400f0380403a5040600321000b050300201d0154071aa000c1e2441e1000d40e03411078440c0c2440400500d040700080040c3c1071103110030752241c0202c2d070012041c401098407640c8040c2c00b9000d56110703641040a110588140302c0307400d500707650142c0c0100340c185040c100100039030390074401c45841c1949440980a003800403a0460707041c58500b68031903001b010400c00e2580c004030240825809510040141d000098000e480501442c603110400c80610f40c2c19034003c004191014044c1002d03103480e8541003400800078900315001511408501003416420b900610800340035542283e40c2520a040d1050541c00484480c0010340801804000d08295a5085409903010302107142c0040340448035000010f02440c080c0e003205a140d140300c404d010312041279164115840c103450801260004902c41802d0b0b0740d000380711005400d80240940388158441c40d00b840c5000300811101004603442e20304419989421159584d805030b40b00f046060040781e01101b194844a108031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 311650791 1250 311649541 311649551
    0x102105180a0302060a2309070906061b060b0d060e06090c010e01090504110c0304171c02150403051c02040e090a050d1b080f03100e06010c06090804050a08030304030207090b01050418 80
    0x2034241186c0c0403c5424810b41c0d0008042030002c60610f0084a0041086240200d002d0304e4a0000c201d141803c000300030300d0030340d8403c0648802d0700d6550b000c4140d903030006403c02000807001d40f1303a911401c04441c9403900740074800c0c1c609aa58014001450703040010380d0b0310030070603040c581800f00030b0585110000741204180510512180304000420242c640521103020030510103000510307100c01c459501c010004403064140c85298000752042e0a900325072030002080c0c54034101514907101d02542c0030000030340103411200d08681c1b50020b00c02c8508600200125690b03070304000e51134152546004255420510710345004901c21030f104400741c3d00740300d400c5a1f000b0555480050700c0d440f402c190309550501004224511001400c003500415136241d1244403450b242c0002010000341ea0b41c0100a181e64094445c140300000d002c3d0780150102030040c20443c1c4d182c030000c0d0340d250002c5404400510600e003000c00d0415083c05100c0c07031401d040c0c5419007002c0c04d012511041500c038560801c002c0e40cad60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 311652041 1250 311650791 311650841
    0x1060b041e03020d03120c020c0904080313171309090f03050304080d020310080609060403020c1309021017100609090b1f08010501030e06011202102105180a0302060a 73
    0x318000829030303110f40c0719041180d126203c1042920b1075400c87c141590881030110034107484450300303d980a548100026a030f5a00d02d036076580c0c140c81600d4040c0890701e072001211100e01001005240891030045e81c0b01d11b5690300d0842c0c1c1c0542d01a43c2000b45050510100480068081c00c041e50704a0300c246100d84c213013007001075140100d0b00126104c1c00d0070450200c040000c0142803080d59082038102c8094451450320380c40103580c0d600401c625030700488000c0300580a0b0240d07907004902749030713004201c03644200c0100001071000da010803e40d111058084089001c000300c0030341d030408580c42a2107400f4550310b040030000080101c3d00015410440b0880200c110a1120494030320243d12600c8480903541010001003c840b1800b144454580c8804014011105080d001c802100c0d811a43c921007400c20010403121118026900032a030ba200004825081e4102c0e04014420b800e200009001c0b020b54519460f03490f0480503001d03000da0041c4000c903040041940041000d03030b11241c84e040380c0401d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 311653291 1250 311652041 311652049
    0x213030b0405010f0e010c0f1103130311010201050c1918080105090109120e09010b0706140c071509030e0906030106150c0204050106110715030b1c030305060301060b041e0302 77
    0x320740032507560355580b6000003035816074401c460341d5924090003000004030070800075013160f10f4214000c09001070ba50195501850420440d030700300c2d2501414500307559881c90040844408242d10501650810b00011007124844080c0c9000c0101c00501994041c2121401c4e81c401414030211400d00c011050082040d0b08240503840c0075007403d10000400703200ca42040780750740c08109080010001d011001070101d5035101d8030f1a065403041c1d800070b0782d80c09061400d10001c02e48007080d0940701000c0c030b00300b03d06c0000c62006400464003c074958416030100030090300884401c0800100498842018000b82c0d06041a00c0d5074440c001600018596884007031892016a4400b684400502c981c141002181040d000d0349006203c1c81c10858804000300c0c514075111901802641d88228101c0c0130003007858801e030450361314801c0291580c1c00060328141040c04400c403c2c442a00070a04241c00f0900e2814140708040480385064003250402d811710341290702c00d411010340004040200b18000c400b581e9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 311654541 1250 311653291 311653313
    0x90c0a03320f0a02090303070212010f0905150106090e1501020f011b110d02121c05070905190f12080706050c030f0a0606021209011b050105101a070204021303 70
    0x400c070181d04001e0314081d2040004241d00500c00107060340107001c542c02684001040d60021541200c8004117030000906c41070042c0360707180901180504100c840c10a109000c1822310210b04500020032135030313803640e07801d680600c683d00c5444031140d01840011702e820055001e0070b5010340148192180c07030440f0b1520a09407a58015000c0c402e0141c11940c40e80e054000d400c034100d00d000c8402812461141c0d22000c2d4854070111480e01047d40006104910403401d00e0304010800c1100c1c0e8200301ca400c14801c018020180e034010580117440b0440e04200115655440c03400b2a903ea5020400180c1044120018002c0007403088825950500c0554000703001409403078403070b048485983d40c41c1e2400400d4240c0043d00078011404a500d8084240700c80b81d8040340460f40340d40541956503407080d10b400120781e44040b248140100001c401074171810810103402150080d0540704040424584a0003280d104e03880c148000d6100d4081001000014103154000d002f002d0140740c0032825041e980c1c0c5850144d05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 311655791 1250 311654541 311654621
    0x8040515150109050111100213120c030b0c070b012106060e04020301240515160b0a1b2f032d03060f0f030309060c06010302040605090c0a03 62
    0x1200c1c60310160800d50b0301121441c0245001d103440c00400700b07040e4690340c03505004018800107940025058443c20380540c050001001c900f00602006017940c2040501d00103140012206c843d0b800300402c902a00d10804d448000d0307000880900903901e1720019000380000d0ba00045420301c1e11584100104010f0302c2050024840c00044980c18601441010b00311a1000c0c20303001d24468803c0303a4507124100c0002501a514240da0300c1c403503020702143c10f02490160503500803000000008100400846130042405103400b000306114400390800340000208500c2c0a2400107901c805882001071210301100f07440e80e024800780c00744147c100c1021411540401d5008001500000c9034000300004200c2400c0300c1c01c10301000900b14101240043c040c96038000000d4482c01ca01000d014042d80d09008403110110b00030201a0398400002c8240d4444000f440142e12840ca0410001000c0c00c0032807641d0310a0880500091070000c465200ba80105004005002e154030b51007021020b008241c1c0728032280c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 311657041 1250 311655791 311655811
    0x50a170106170c01350402150705060a0902040212071d04050115080c070f050d11011107030309060e1009020f0f0108060d032a060506031b01030c02150a0915091208040515 75
    0x283c541401440100a2601208c00e5100340802c41c0c9030100d0004202c842d040324400c079000c5903904072400000c01034050303100803080400c00007042c0140b540c0c005626040310040c3c030300701c4040c02040404000032294240305540088440c10f170b13180401481180c1c09540305030219270b11820018140c65441100840f0782c01101c0c02e03408002c58040043e04030b01182000c002800080c465490446015141c5001d00a0010113164440070703020b040007030700d4001c0071480707982c1e074100c82c050410241072070040c103480b141c184d02403162a0004151420040c0307102d1001c42e01a100e0101d0703521143c0a2082d1082c200030158200302e8811250103d40715144807400080741c4c07040f0224921001400c0075802c80b000600307014801e506c5120703680060125141513628608007400c0001d000844141d0aa040c4240b4201d2130248208081c100000503c00703510550f0a103014055540d200304525040a040322500c2c0700c01741940c007003514040942442100d4240d03015102d00c00b520180b11401181c01c542c0c010564041d107003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 311658291 1250 311657041 311657147
    0xf020a05120901021305122b0e030c151c020d05060f030d08042402030c1201050d0b040204020a170a09051b0a03060510050a170106170c01 61
    0x41070740404125002800d0200840c0350400d011503200c01000a8402c0c0c4d4041c00348442d44000400c0140030074038440c401c803034143c20041c4030388600c20402c1d5003480011021031100d40c2004500d0500050020007540e01820099215440e040c203840c1d283c112901134051015039143c44200c04c640307030000d061400003408010031181000303401c000c08855105d45541c0640d0002880d02c0786158050f06072500b140e000030315603d036000c1d8400e180041c020060f880c5c0081c14000818000400712140c02401003441d003003026051641c03180c08000702030591000c083c0210707000402103009890b0a50090040c080c00381401c1c04266004100c1c90a0294110b81c540207050b07441c45684240a82480f103407035081040c100410410240c480001c00c1603982d800701810300c80e682d00001d84131031244000301c0003500c0c00500e520100c0340d43e8078051808420400f0700360440c2d401c06a001401c801e5812502810804850160250708a0180115500041090104d5a901030a00c47c26803601e40c5e42c048500801030b001040074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 311659541 1250 311658291 311658307
    0xf031e11060714160c030f0b100b07052d010603030c05010c0302040510050a03020702210c0f060a121103040807170f0906030a0f0203010f090e0303060d0209070e09070e090a1416030f020a05 83
    0x83c00710303503101c00c0581c4010040700000a2001c0340401450f0802e121068000e0304000850301d43c2005803441c3740043d880d1100210a054202020705800b510500091200d040402800c800b0b902452142903045501c01500d10700c0c050083c0090071000f481490018186000c03600000d080700d82410520109201400e02c4d0504264140f040c03488000081d1410030420380d8190220342c05103d5901d061007000030700314484010140503000700755007076841c00010782c41b8200350900c414168850501103441160a480c40f01d64140c081c02902c0d40e0b60045c403030702030400030700030700307208003588003d01043c212691000195403201492024502030314081c0c1d041ca440d80d08042d40c1c0002c64950b0405090258020b02c20009255141030600d40d40f02d0713040c0c170240c0b03982c0c48603001542c1494a0102080d1302203800d1b01004089940480300282c03076502101c0c00300640e203d405841040391004040249140c413240e00251050703001303103040407080c03815280008006110340c5800040360422512240016800644e08c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 311660791 1250 311659541 311659561
    0x90b0a21050a0f1506050705070b0307020c1801060801182c01060807031e05030c01020a052502031c090b040815010e0f040f031e11060714160c030f0b 66
    0x1002d154000c03c00c000600380020140300802d00d512684041040002d802c40400c0005d003c080020207440304003c0e01d80c01d04090203500c0c1d654130640180160300c1c110154202500b40d00340f080c102d40b1291100031181e400c04207100c03000202001600049600c0d102c0710a020300340c2c450465498012031030060415000400c2c19801c3d40c41c150722104003684802c40c1840860394007518031104450305054454039110529202c0c2c1540240d8403c5c008951002c03c54240306500b10004000300800c00007240d061502c0e81e240d0881c10640000c010703405a00031400281e28000e8204680c0800f2114100142c03c45c1c1c0d900781c402280d5006800c0000701e50042c0903051000d00c80354514a0140c1540446907406250002030401100002031001d00203200f00c1e00c0e11402e0500800300b00702d480c420b1300038442c2001420840507000c50418015500305110b04400141c44505c034500403d803010081d030300d2902c0c0a245564840e1074490510041c2e80c000c200240000005940c14140b0001c1486569241264030700744d8980 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 311662041 1250 311660791 311660801
    0x70e040b04230709050c0405090a02070201020c060412020406171005060a270e030c0307062003010e0610030e15191d1b090408030403120204080703050c060406090b0a21050a 76
    0xf06c030900500062006640720086103034491080000181c0721102400103d240802d030030425038208070300040c013260701250b00c0d206000040c02a80e00340309207581c4800740e405018000e0911400d5401c00020841c5103680c540205070080c000605404145484510040c5900140c0501081c1d00c91411403003107400360207004811032150751102640c10042001446a140c3c410f25000800441d601c80541030020100340e0a4404095a4211075480b903840329400650983e054402c10b02c150750a0030102441440780c001d00020100d41c20244c0b14840684031110007034180941400c0c0002d001c1e05c10040e413082544100f8030000e14400308110040c0890a100d03040003401d0380400b60304070008035490407a40700e034042030f45c01681c0484c16982e217917103d0a00701d504d1841250040310007400060300041d14940054038200780d03402101900c0380c0d9001c100c1040020b10a40c81004040b401742c00007004048488005030050203120b0410f12880e141c1c00700180e01c0070f00c01d007500051050b070f900180191400207200e1f03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 311663291 1250 311662041 311662051
    0x1050a090c08010504330c030906050906060a120201020109051c0809030f04030b060303160302070f0902030f0609040213020a1805120c12070b040b0417070e040b0423070905 76
    0x200914100b5480780721030300320150300750306415025000801b0f0b1071094210f409500b41e83c0d24810400c1503c5114014050450120295140d904240108030f0300d0b0808500d482c001c103002416462103e16000006004c20300141003641555a0f94032035402064060203140408094800e04940600060740b018160050140a0000940c018041404550002c41c103c5041d170360458460441a5900070000e4a0752090f04000c1c040040012003403010950001904029200a10441b61005884604460490200300e440e5000031030048045502c07802e010071055003240c005003803401d103104070101c440283d070700c083c04040026140e2201d0100041281e203c100180c03a00712060003031401c5814216649580000c0308070f102e203002100a014034101042031900601d0120000d60700d4035941c110120040e00188104940441c068607400500704002c074401003583d00c1e070070700c010a603141d6032a0340b42074000003001210340707801011640c41c04d562091281040018070a004002640c00c045ea140c0030f07038a01600f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 311664541 1250 311663291 311663293
    0xb0907060804050c01080a061e0e0a0b010c110114070503030703110702031024080c032506030908040f080c1003180803040501110310291b01060801050a090c08 70
    0x709000010f140440d40440c041c4007443e0018080c0c0340c0b203a40700000d22140c0e01644400700341811014110344102540412103000d401207681c19980e0f901b440c5c2c150382e00380c501c190025082c008000300103401018108001141858840c1c00100c0392500c1401560001c0425105540301008001c0c0c00343c1c0c94018072010220a5041600700b01d161b80c0460b60700d00120105590468962490013175440500720310005040c400d00b80c8a0102d541c03000d003241c58003030020325176000c1d000301d1b400b016060407041410320b000b504021484503010f00e0312104500804090790129214442004006010304040c402d203005040b103400508408903c20003041902c0c00c014659000341801d020500d0311800c0c2e007558214040d42c00072a003540c0c0c0c0e60307180352890041036203020b460240000802030214000145a41c50103032142c1856450b262054401800604a1520400c1c0d0151504005c802e002883d030401c61070249030000004601c89458040007429158202d502c00340c203a03a10100781050280c1d649410008010800c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 311665791 1250 311664541 311664557
    0x3020c034f12150c0507110307030b16020118030e030c040533040f090b0c0c030414060706050115120212010b03090313030b040b01060215070315120b090706 69
    0x211031003001c00d018491401410344030301e419018092202e1515614154a000c200407a1000040c058440e0f0003400e01501c1108180928545a040014442058a81040d010a51a40c0d403070348070301c13088142d030071100115521007220100f0303407603202001c1c001c2502c2501d40c000c0440b140f50502d40b41901c0b80800702d12640c10281886490900602d111802c07840d0090410000f541c5201549040d42c03005c1001504130b49402d8000c01c607080741c0d42c400200e407440381e00b030000e060b00c40c0a01c801c00d5000c0e0800a000c15081084200181088210b14a09a034409081142002e200752a0303641121803d900030b801c9901d0410f407206545134028103040e000c43c0100421824060100c000d120780d250140114454008004003040c0540b00410644000103c070b4440c408030142c60b441c26031247d00050b1402c80e900000c0307400102e0198008105451803600d8401c403054aaa10036030214040d103601c0f0702001404032480d00101b040219000f51a007040c0c095540c000c21342c244422114036000d282c0e4000300c2089015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 311667041 1250 311665791 311665927
    0xc030c031802100e2119030206010519051e190e0103081b060a0903031b02150c04080f160501050309060114061306030c1701060f03020c03 61
    0x1d14010660107030180c0b4844440d166810080d00d03950780c6450700541c4410200000324031800b00f01010010510100300b61000031080406a80c200861120000c0168021b040180030a050000d03009416036203640c10203004546d10b50100310f901d500d0300f0269084441a00d45c21711181498400815950b40592601108a1905200d0140f001d010f010080503203100090302c0031203030352400c90700d0040440c18080da00c1900300341d0300c01d2008062118044011074200745440301c1e003200164103101d9a07616500500382c070b84901d038400d40c4803400c010039150a0306014080807510320070402040b40c5400040d0000e00d840360340c0081c4c9865440c0654410340c1008810420010a5000480d089045951880005450030200b01c00503010380140c502d2040100b21415000035129415042030f079003100161580f0010450309031a0441440c000d000d00e01c0806e10f508002114207109070700600d4012072640950341000313a260111101105000064030129418100341e40b1031550903d86900c1802d0380c520000300301021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 311668291 1250 311667041 311667071
    0x4030b0c07080d0b120c061c0e0706120b0a03020609091806281a060304050c030d1205061e0f0f041103040203070906140d1b06050310050109260703080304060c030c03 73
    0x4042044c030309031042c3c2240500c0a8441e410a400102c015022b591509480e14001083c0309604104000b44d54245546100302e41419085401903d8014012915103407440051160320180a09600f103600240c90501460302e9040c01000c1c0100b46240e041200d1003060303c03c603141c060355a0000c58280740340403000250300340711030300408500000f81e680548940e0707581005c80c200150807401503094040c0d40b103882444d80d4010005c01602d4000c1c10100301d5034903050f0511000c2030340116045500d8000f042c090540c2d00d881c1d20740f420000c070014140110a0048004141514071038999655412004010b02c0110b240501015000e07146d0894100b14051400b16030740312103148803404a001d01c00640c1c40c142030142085c41038001000320000542903c2c0d50386001420b0b54001c468054000035040c201246c5503105d10f0403042190140301540310007a59904007003914001181c1c000c074640c45641c3c40040003940c0340c07002d18402d901a82e00091200c030040b40190954007804000010035203860800003d11074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 311669541 1250 311668291 311668297
    0x17010b0d110604080703121409010804081605100603020103140708010b09010c050f0c030706090602120903030903060708151503190b04060f05100203040b04030b0c07080d0b120c06 79
    0x2400001c509404099a00421058810781c1c1181035140a80c2c0d0700841402101c040c0040440080c0e5a00c1d843c0ca441180e1030281400b44100042c00181d001c03001c140403950f1070026152070340315103c03180c000e40300b1a03480524000d404c44159a100b07451790000c1080d1768040c4544000c065100304011000e00e00a10028144a8140920008440c010aa400d010303440b03881c40031030782540441243c40c0c04d261529025554040010380038840c2c421900c0100300c2e148101000422100b07950010f21000111861301a0160000f00d00c02c0c0c5c040c80103004902c166541004014090602d5841da82c0060804148e141015170f0700080d078a0080c08103651492200019a00302c0781d0100c6051003044e504498450104060030109901d25842400e007600480d840082c1e26500741140d000701c80d50a00011101c02c142d0701c0c1e00862117800c0445200380010030100c0c0d20f600d5016031107107a14401518284465441c4e40f0540c00c01d8152010856840d10000c001c0d0820603140340c0d40c03c1803040141107100c0c9010005030700b44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 311670791 1250 311669541 311669543
    0x5030606070b07031e051005240d0b030111070c090204121202010e0d020c0901080c0307150203160c0e09150c0a09030203070e0403090b03310c0306020417010b0d 71
    0xb550000049010b40b0075402180310641d0700f0403150480705d1810070b0401415050311030a00000303440c1c1c0c00003a40d141c032000110400501e58018441043c00000d100c041d40c20041100f01c01c243c0f2001c01011981c1d0a01c81c41d0312184106003031544941c0305050040840301c10f1713080710300c0c0d1a00c10031061158000c86c540c01e1206c10b61002e040d418503040c80200701e01600a1800303d81c214405c0d60505000d03940c0100d1000154103041d02d08a02c107031b995642d0190782d40c041e6042250150828042130040340b0908204807420046401240d00d0040c100141c41e46460280b001941c00c150792400c24060003284d1300c0210341000082004003803010740d06c17802c1c1c0035541010b08103400b1001c000400729481801090018001c40d0014150f5164a0381d03920b2000c2c0c1c0f9002240d044001500c0c011001c664041081e0a5034010000d044c0c08a030424030f0079034500100c0301000ca4098081c17001c40024000503150000c4003014502c105000742c0c07038a10b0720141504044220b40821456418405d0700e03000c60300c1d0000c24100715 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 311672041 1250 311670791 311670803
    0xc0a021003021605030405130902150a1830030806011101110403060c0224160e03030309011a030a030c1b120309081516031a0402041d070503060607 65
    0x40394200400350001e200e0403079805000038840908a007480780c044091300c1150019603000310703028030030340d151411554000d100a51091126514010002010010740b884000c10304201c02142c905e001e03a602c08000a81c00040041c15400715024403841440a181c80c6118444c6d100d0180d8172155409040960001c05207810040c4001a03044011000d403ca81e1061041d4585140d5031616424110b0281c818448020054803e2100800f02081c004103542100300107802264015103a006982d0381d8180d0742c01c0c600d03041283e900b55200956400348011800f84007010000900d6419031024907241c100e46000d8507110742c1102030000e02180d0030000c0d0304800c0d030b032003800f144044400e80410210543c0640144103c040600d900104054000e81d400056680035400c40308146041d05401000303400442e00c801c0d452020401c0f4030344041c0660000d40d503120b01c40c0040010051084041012a0442d5000d4002d141070035040d501d4040714847d45a401a406141441c610b06e0000003150b164401c9020003420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 311673291 1250 311672041 311672059
    0x115030e15040213020403060b1503040206041505090a0b07060c111207060e1f0e1b0f22090c0f1401050304080d050c2511150f0703050a080a020c0a02 66
    0xf1565108401801541c03040011501c80340c0300e0500c8402855940c030454014002e41c40c08002d17581015044d82e101f6a40200034500e402d0800075200c4080340101100005d120080c050700ba800d560720f80c4030310050540b00b43da980e1a1540b50602e201610404414241800701107601194442804501441d201404030b031840e9940c0010700d841001003075080010b003114050003800c81c4d1003000440c80b1810400084109025008141403042d41b2100c9003080c02c4510312110007000e54500704100e08a400c09402482c1102ca1040f00c002e000d0103120011050466541d0340710300e03c00300000048001c1c0a008886003240101341407035420715051600442c098113104000c00002d0402080808440f40040f102c0c80912550500d140325001c590020010b44820000004513034154603010100c01c10f103a50440d034090003005100d0f00b07128031030300780031b100d076422034010418159098100740c024110700c0e01c40d039640d540e100d2001100070b08510010307095000e9140100501d040060000502500c1c2c5a011039031042c2c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 311674541 1250 311673291 311673293
    0x11130606080723030c1914090114071a1021020d0507090e030a0f02031303060b0102010902090414060906090a03050906070f030f0201230c09270115030e1504 69
    0x4600f9607030b00010704030700d03200004104440042901801d00800b40d00d58005031020b8070601a0782000c00e4206540000b08180005866584034948040c00780c140018064580200d5407280ba904a80300340c203042c00305d4880414020440028010301d401045941e0404508016034125100d40f5030f0144c201078890b440729541d010600c06c0605c40d150013003003048000c1104c0070112602c0c5403241c0140071000c022800c0c4901c60101c0c18008000c0b43c031001074a095091800d421a83d0f03103001061183e87c2c0754119981e804200c40180c5030102110b0260f406042d40f819902548070203540f4040c4010100102c0c0c1d08020140410a40c000602e518a82c1d8507003852030f2501d640d00e01288c8680074400c0003070f104044c0c80c1c0c0448149034005114844101d50b560003031007415001528080680401a0000e040c40c0c0c0100010b9442c1c0002c074090204d6035402130420b071011500421100420350484680041a94548010056100229055100c0c06020309040c032054016071445515480d0401c1880e010b4014880014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 311675791 1250 311674541 311674577
    0x703060f141501020d1b2a0e091c050a08071e110c0402040501020a030305090115030c081506060405010c1a24180c0d18111306060807 59
    0xa03441c1d20704001000649014800302c0209580c500c142c038054040c01144020151082005030703014a000c10400200b00c81e40c0c0d4400302d0051440100110f40d0480d0b08041d8560812214118000c00540d00300020509181260306c0c14202001c40044440104403411190103030808261409183c0605140b0b0325960341600070395100a07008010105280e80e49035084046401c90155400c02c004002161704401000b4244000c91089000d040e0150740300030483d000080c403903000700380d00805000010801c1035100780d202e8005100703030f00211084c03a100001030000310001c12440201b5140080c481445003030841c081000345c8280e0103130394100602d0500c4807007404010300c01d140c0314072011007050025282060000801c0412030038801c00030744407030004484605e000d45505442200740004000790b5110a881e010b12907000100d04100c89880d01c101400d10700d9003900d0308110314003c0300e480702d103032211030204601c0040c0e0030030704280319280031030520020b070f8003842c110703844000d90401002d04001c2d00d4443d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 311677041 1250 311675791 311675801
    0x30a02070507090c030507110303011a1c09030f020316020d140a0309050307080c10030203090f010c02031e0711010f050c03041d0f2e030b13170c0703060f 68
    0x150081c4551100000c403c101907200504081c0301e40c1d002c11031521040070444501800c2d0811448a52080c030050103d044088494014500c0c403c59551601c4001d0341b26180c180e4a00c3c5c1200303034403a9076102c00d2090681011111030b190001c0d00c041d51504200030104c5070700350008030010b80221101c07400c600421103400101c0300400229801c03900c200007103140c020554403460203054020702550400055004000824038000c100c001c20507580c0c002c82d504110021341000349008400d220705c501c0062542d4083c4603600301c407880c66010b59503902141107400b440c800170901d0404400010801440402d48030310658407000c03400d207404500140c000104a810740506040d10f185400f0014000441200c141d22001110403e00350042d0180c1c0e403108801c51081c07040341c1d10486500501880440c151240f100c01e02807046d482c80328910640c588d1603241e051601111001390aa030300306242e400b4400d502040310944900881228a0104c1803164107440c2c4419200007800e0544481001120034038503000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 311678291 1250 311677041 311677043
    0x201110303040c0302120a030e091b0726030601021506041e1401060c0309172418030405011d04020d020f04030312180f150204140a0905011208030a0207 67
    0x2103940340e04241c10050740c80030f103500c412441204034140d003510803c00481c1c203080b00343e09611070701d01c410055410310414a0000301344140342d580ba49108516030300480c001e0305006000d54495440c00b0010065051150419030f0300c012422003d008001041c2c1c0d002456140c480d6807500e03143c40302e071550310115001d0b0205903145040c9400c000c0c20000c64440740d83c04890021680c0d0036040c840d03681ca59003950141094107001c0d00050540209020035000b0400c414000e048840440340300a1003070f40441221102d031103103544885034150520011318241c890751504010b008001e14601483c04c0300180410751000c2190220941a02042007140d949078161491882c01d0b00307095540d4294080d409070250300c0b60108a02060018082819000302407103007030444c0c80003001c6911010304988414841c0091040126805d4000c0ca14428851040b40083c02c0102040b4140349100340320070042013440c6201d03800c0881c1c25403900d00104244146840240c0040303401052a960381c0d120340b000d40c800b030312400c08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 311679541 1250 311678291 311678293
    0x3190f02100921230c010b06030c090603130204050a020721020d030b15040602010b010f0c0b0402060304051c08160804080301060c0c031209051e030601061803060908120f07020712020111 82
    0x1003414214402c10003405a4a41d980080242e128501f040100d540002e94070054400d000303102c0045c11b410071000458001714804054002d011a550000d0705548040320300c40501600422410100128050718402d1270100c24002d00c45c0400b5607400035602c85082a9160415445052b00340f07060b2030322a443c20003002450b12069445403603800107400780000184a0340008c8002c00020004c034410400c18522035031002e040851034403141c0070045141c10150090340d0700d00030701c00340fa0780903401e00c214a0140700305500c0e0040c42d8a40a01381c1c50501c3c9440c0310400512035440b0400000840c850100c905441960401a82404042c02c0440c080301d0310303800003001403550f400d10030211900310b2480812580200e5020407a51000e0301d0000d295200c074401190194042d200510200340124480c408854800803100d007280d90303949071203060325416802900e406800040788200103403000c5d031050b480a01c0c500c11011078140782d0b40080d1744001c18810a454000e28244881c21688a01c03507124850303600350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 311680791 1250 311679541 311679587
    0x18010305131e0507151b060b0603100e0912031f12060f0515010c02040b150d02030f060117070f140c032115060c03190f02100921 57
    0x40c2c4102c0c00c481c18250165020720640d0b100142c018903610f80090b81d26129501c142d040349048582481c0140c000c001202e860307460356800e170115152080690710803024582000c25035851300708894074158026010060070b40049520407001c070251011241c03c081e80c0680307018940e441a801c2442804030b500036140316012201c4240a03c225504003860041031401d00b000a6110390f14410300e018020b0300340c00c0c0401d5040240e18054506035000061250000c0d041c07250080300c1b025031024581c0641c0481d0191359002c07080c031a64200d44003500303034849800c1c2803040340b021510750107442500c0c0c00ac0ca6002005466807400c500e0307511814241c3c418484a42d074a54860f07607030320360681c5c41e07800400907480d0341c00540014a540d502709200c0d8900400b502c192000f000f21500c01401050350200213040e09500c4200244500d02900c80a4134488200c0f80c0c2c1c80e6202c0000d003c400030b08010351b00b5107a006180c200036414000c103a00b00180407070440d0a0a501c102e001d003001055445400e0801d02d024110849 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 311682041 1250 311680791 311680823
    0x702071a07060b100503180a0b150d06020d0c021e03040e0c0705011508192f060301080c120a0503041815060801060210050c07021c050115090f021801030513 69
    0xc84099405407812887e94284080c03190394066031400312600151050440b540814580045241011a0303100080c041000456194448405990020309100c5203540e4031100e05401e15810b101035100400c80c00403a4107820851005a07030349005034024500c80c682c4581c00f00d8207003c20031044540c6a030348003000b403024820903907007408040310300d204003452402090121500f81d40b440018a140560212850f490079500d044504a4240c1d5440d0168100148049187d000d1340c5410165000b4040e02d801070100d00000028003412034444240f41c645580103210740e40c0001c602005540942d24051340b200034903e60b6007a803d010309a80c0d40c031250069480f030320100d46580e0141000f4141d520503000c680e58403080d1400d440c1110011600100c50a04c01d00503c8010320709100603801222150240004414550315218210b403c0f402e0450391954421104204800e01c0b40210554003508004c21403c01e00401181c0828a55006056041599480029007060f0302d5904161800f0341244445e2001094 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 311683291 1250 311682041 311682047
    0x2103030609010902030709031704090608011d030708040e040809040518010c0e030c060306010315060f090e01120605190f090203061501090e040302010f0e030904050702071a07060b10 80
    0xd5404900540080001081c000007034021217006414503a10045000d00c1c41e2105031181d0440100011050750411000440003010301408014002d1780d40001080d0340c000c04034581c2041084018030343c9400611401020034210000c0e94110b9520054402007a507076032800c01d25a02c00e10300c4590f806841c01c03040c0207591200c0c000340b506908040700200710b0844440001d03180f404628810560640c070100040f201030920b0750103940c0251043c103002c91901c11b00150034074200f400ea0081400119100f881102842d8451303540c00090508103a0149294100a04054003407038140c0054800b6071503102081c00618509980404410860300401104640c08000f501404070f6000982c0b0900c5148042107180b20071100d04031410030145c4031104031503c0d102507580d038110300800903815075603240704400d8400ca042c0140c240100303102c800341d6640c031500020001141c00c042c1903401194014002407180104801c0c16042007440700321042e48840861400030094001d079000c1d20307040440c8569172030781c00350 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 311684541 1250 311683291 311683297
    0xe10030b010f0810171005042001091d06011707020d08010509060303040302010c0804050d0c0603050709050a0902090a0503120903071202010e09040302160b0a1206140f2103 76
    0x9996260502d0302c5a18111207114050302e0300400b109003410100207542d1041400c141c0104803400f9240c44110f0341c038940c000c8030300c03c48055914030755401403d0394031940f4920300a034480d02400c0200b101402c0c100d01c1001840e0f60140341c070b10300e4422800304103d83c0c05a400040c0c49030748400080000c0c134100318004d4446001980c00e2000c602030000114440c6480001a07100701005002981014915001160180d000400681e1101d01c00c10022030703203403280756246101038001d8110344840780c9000700041c125200140400100011248284216680c50300b44d00202c031004100962500320318000281e403503115512166041c45080b074092014040301014009142084003aa001c082d5600800240074580500003400100c0742c0821104514052025980041c0070340704481004080600d032810b84007240d04424005000811412407195000303001c044041001c060034000ea61a00c4400301c0c0081054020038072400720340d0404030a540b941400c0600d51541099013040c807050b0040919100d41c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 311685791 1250 311684541 311684561
    0x40f0c02010c02010e1b12060f18011a0609010908030d09021203030c090904060f021c06061d04050702010b06041220061b010e0f0609010509060402100e010e1003 71
    0x5420a03884840b4280103101301e030510008038000c4e15140f031428000d56920b043c2c61001c5070340082d40385202d0714080780411220703214141207940040740e8200103442180c1000300505c6101c02da81050700c001c40d10306200350208a082c000f51104c0f900c0320250001681c500c41e441e004940355210104403501a2640e0340c200c1d0011078000d0314500344d4180d0b410380064603403100304e4040710b41410402c03501010b07007882e40303807564000c0c0280c5c400105401100c03900010399001075401508030461800b16100b8500030700c00c4200a00349070030008282c050310380700441c0ca4408821558881d6030b850700010710680c000e401803102204010440c6958946070b03c00c44d08101c80a002c01d03505c0d00744205000703a0f021402d905110b00160001e124604254104420000b960100403a115065413224103402e440502006100b80c1c0c481c011000d86840d203030040b502e500f11400242403103e254003100901004d6110030690107044081840d001124280402c0140c49024091504c01d80043c4010b5900d44510f5243c1e000607912 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 311687041 1250 311685791 311685793
    0x151e050612030a08070503090a141b030f07060c020303070b040c1502010b09040f0512030a0209090a09170d0603080a11061503030f0d24050901150f030515040f0c02 72
    0x4251042041d52030003443c41043c00302d01408046680310340110302856000031880d00700c42100380d0f2503490009402c01e80501d41400d900807001140480f14691641e840c0100950081c1915100c0c508203d41d9001188210018080214001e40541d1014000c49480e2074101206590a061600d40290505800d01c61075401c4142e845015080303038810300428892400041c05260b1540391915151040701c901300040300e0610402d000c088003490484003071849418010b0006803586015020310448400c01003803400303101e141118034000101c802000195000d041088071361544000c4e000e00e0028840e90300041c08604c004502e25003016405548000c1040c1e8200544050783c591656000452105104c0d82d0f9043d002403000d102500c07541d0000e088580c2143c0300100f9040e101c0c00ca10350300c3c4104161600400403c80c00700340300c42d0411164050043c00c07800a9000041d480807002030900d8003076a40d900815803143c0101e40010700b01c4514110b03025000700300300044810000600000e00c0a24021405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 311688291 1250 311687041 311687059
    0x203120c030103050604030e03030c0609010c09050307050d0303110f0403080d140610080c042714150d030e100f081008070308090109120b0f060d0f151e0506 69
    0x80100031500380ca0490703502c00c004000c036440720f907010b0350b03501544450b41750144070a100401040d14204038540c060468500000340704a4001d00040c14485a40c11541c00b0354090321040146031175000c10500c1c080d406142c00502c060761100c003000fa83c070414084900c800c0c0045804010b100c803420007030201e41400b00c030402800109400c0a0040c1c4000c03550141c2c000f032070840c28403005000c0c41c200e6512010b940d00d01e81c44e041e00c411101200141040711510b51074103030340b2040b40051542c03054091800c04030401906a15280080d0025a2449150381f80a00f002082500406002d20100c16110800800ac0711b01c0d1225104000e2550801d034200786c0000c1c42c0704000c56500e400d20714450b001c1d941c5000250889504644030702c441ca0348035014a6042007a0001c0000f8134185900400701f80a2240708114890f060182c0001e104180103044c6a20a0f036010404500145120045804496000501c038010070100002c59000b0908a0280c141c44020318212202c0d6030890b40c030462258a045a40c044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 311689541 1250 311688291 311688301
    0x80a03021e1c0203040f052b080c07080f0601090b060a05090a0e1306050703060b0d090c0803030f0405120a0e1207091e050a110a180306020d02030609070c0c05060f090907020312 78
    0x16002042003a00e00b11264194106034580c48200c9030591814081d0030007a14020b04140d005142845a81c016001c81d0400143760302d103076400b804034074010000c1c91401d2100e00108400960a44284103450082c04400581100c480e1030300e02c010b0300100342c9520603510928112a41441d01280d180c01250f80c58941400540002d000f889030805540b0610f20080c1000300741501c02004220844003070315465640d10000a0b424401c00040d84111901c40d03144499040602d003161824080c4c08044041950501c054a0b0303030ba41c006607500c0c0c95401154450b0740c2855a0050b5428110180c0020a905042c92088a14140340c107000b40700207030b0030010402803550740801490032110400d010406c001000c104111201344203001c013140703800c1d101c0300e04034000b0b07940d41c0d44a0480c0d10600070040425004030030000340703280003503049500800034240400603520b00d5441c042034810500590703106680210318602c1c1072122505581480c50040c1050403641040d80f006503603904a8490710248100a00001d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 311690647 1106 311689541 311689549
    0x91205030c0d321c0e0d020304080c0103060e01140307080f061b030702120c01090f0503030906070504031a2d040c080a03021e1c0203040f05 62
    0x19001040d4640401d0301d4558601280103c03c07000810700010390001412a400d191059407155441c00315401290014405c10f100c1150358810380ea11500e01c1c1d5000030051003503401060458410050b02801101030f00d5107806241e120040013030040110101548029080d940000d003551000c40c0caa03217140d0b10d80f07610080780d942298402d00c2441416144542c2814040380840041c5140d49090b601c06907590144180040c0540340028903600510401e5000040c03ca9000d907049062401e00d082c401c3d41c0780c10680c1c14005500a40c004540f405002b041104d08a079407020190b20340841114101c40f1400d00104503001c048400c030f1030010004241d00f41380740f261a140001c8281c1d0304040c103204200100a8009041c9035003c9400c240120b6000101100c00c1603480c42c1c0040a06410041203081499030b8948446885000121850a07074011003d40107841002e50001c03c001c0e0345500300 = true := by decide +kernel

theorem cover : BRFrame.Cov 311510791 311690647 := by
  have h0 := BRFrame.cov_init 311510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 311510791 ≤ n) (h2 : n < 311690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
