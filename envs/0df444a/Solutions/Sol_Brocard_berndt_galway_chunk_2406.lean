-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2406
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:37:12.370272+00:00
-- url     : https://prove2.me/submissions/93fee6f4-bc77-4c82-8a4d-3b5f9ac2cdf9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 432553956 ≤ n < 432733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 432555206 1250 432553956 432553969
    0xf0f06060d1b030f0e0a15090204320f010b0304150501091505030106080d11030c0601030b0a1b0806060717070b1b070f060906090506070203040f092a09030f0602070204050c09 77
    0x204002c1c14a940704031f0509404c03e294100d0060290024000c104003403210081c086c0c420340d1661080003d1900c0b000c441d584040c04490540145001802481c0030f1b030138010a01e0040d400500140c3da01103904011040c0001e450050502034100e00c40042200031040388000d80070710749608002e1082e4104030080c044244002608501004903181100c0610f05101000d030662144810052007805000c00120070301c146500c0140c01203000640804c0035680700c91403000444c0400010b08001b40d92440480c840b80b4000e030103000c10074058082e004d0611283d0f100b029082d44140001c079441c81c01101000412404000202d030003445079882d50380f903c40990b65102c20f0844544000f058141ea6440344014000258440208664014200c0310035080081001e50340f0b400c907100345c110014019a001c1441050b07409101c07200b6854820402c5011080c5845c5401000288445000c000310020000003042d0000d072030000e12401414016070b61030301c1d401808150791000300180c030b040e18100400340071503c915 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 432556456 1250 432555206 432555223
    0x1e0b090105070f06110405090906070c0b09030c070f0305010c0c030f12090b18060717040224041502150105060d05090c060d0615080f0f06060d1b030f0e 67
    0x92800540d0b407400d9140800d6400b500c54800703001c0f075140c03224405400039540018400c1c0c600407184003031580c3d0383c000d49941d41c01c03045500d0300000701030f40d200300300103074080b034203240c01c1110442a2410080468040d92910000340c0c08050084d10720b440402c00d0220a1080c0394520304203107050b250415160b01c02a10000080e4034040400603000a00d002881d059400450030650044286851b410800810300d541c0070300301030b001640c3c007e84000c5200280031300700b54041d000c521030740c03950b06a4803a0200242c0c0c4905010301c2c20620002d03d001591509210000c02c090078403a410035850701c0044000070300d4032075885c00310f0115000c40700050026942c0c0c01c0a60b142d0f1140040081341d240d0340c0c07001d8a4148030794102035a030000004101d40d02054029000319084c3c07003d02400000503c243c00084900c25806e440c099208121032000c10b4801040708000c2c4c2d44102e002d4606840d11024209600460702413420201101501e80140b00e0300c0b60b0b250241600500a8030320602c0010903075030440d078444904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 432557706 1250 432556456 432556459
    0x609060804020418060902090f2e08070b0d050a050606070f031809060315050402090f0703091209060e01030908090618060309010501030c171e031207091e0b09 70
    0xa0100141c215900c035080610000130420380c0308001d0205262040160840e440304a205244400004001104c0c80644034465404107a0506406601620503800d5160340201486686280140819120000c010100040c881618003503520000c613a03113402203c02c0500300844543c1000c06000c1d1a0b51007100b070782e240b1508196a001004c60502c0c2c103403203010034101c4e004052010b201d000115010a6404002202d01841c400051452030042510459404490085d8040c4560b008201d16220100420794007200380c0c200002c1c000781c680c032175078603030309000c240100003c101317180a0240c83e91114a01c1c20403202820709000304045a6201c400c02e00608200394024080800c4c1c801040010040341508240b016141c02c0c2c0d07d003004441c15001c2c0501740401d0f184011a0b00000818850000e41c1d00d010460300000b4142080400b0003801c1d80d507079442c60496051000b400031305071138070b4540e55160140c034540d19594403940c43e0643e4954140c1411204113804c4442c0d075400c220314030000c012182c10000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 432558956 1250 432557706 432557717
    0x52a070e0a09060f020a09060302070b2206090501020d0f0e10151e050301060b0304032a02091015110615031608010b090105040219030c0509180f010b0301060906 71
    0xa4080003a40100341c8014003802050034601e0401c11044d00b68001e24511055035200e1a0450720f58800340e0a038840c0c031500402203102c07140082c10004014010b0180105052080080030a29417541e40c20b60f119020240d803a42d5000808119201d42c922548440010b1100c050041c3c41508409640780c64400d03800e03803e082d03220318549060a040310320101c042d00036120031072442c80201d061070740d00300308a01480d07000b9840c001000c601c448403c415079110310703403542d035400c0c08200328195003102003480c05010410400c8282018010380c2c6400145c0d04c1881c0306e8040484481c603041400f061071691701e100100384508002e004d20381580201c0e0099000e25a000402d0030070b031514020078070304011900f055008108002c1c2c046404941904165494401280c0351005641c96000300003c038495040160b4180e0340c443e4507204064002d41043d031705020f20b0700784541010182008079035178640d900c1000c41d11009039010042013013103039103000d800740400c003514509543c10108090030561840c006d801c00d215 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 432560206 1250 432558956 432558961
    0x30d0b0a052d1e04140c04030f0203030409060605130611030d09111f0f0219110f21100e071e0b040b03010608074803052a070e 56
    0x100c40010701e000c2c11a010301081c41c00c0221900d8004200703182440d1500c20307410085900c1c2252016034a07035000307070702400c64145410b01d9540e0360320800c1d00400c41203030103004c02e201c0010805064440c640c01000c8580342c156070340c1005a10f200c00d03040c0980105042c0405900807031040f41002094030b08540b0002c600048281c0d06092840c88810007040e1180d000e074550401c48602041e01b40d0446980c2d0301c40d159425103c6a400d4185d80700d1060700400881084801012808109418840c08c41c000025240c4407045103580080396285080000440c1055045010000e200c14104920801e40806034003c105030f40841500c50f4403002c0d94402c1d1010714008001d2103070010b12001c6800b0090000708401644c55503950407084180d04244649008100000300003841a801400e04000c8a084520350b0468201c403503030080310070201c801c01540c00281c4152080680c2c103202c0c50349620320740aa141d0540b64070303805078090f0800c0c00c0c4c120880c02211a880300d0282c40d00000888205490000b80d910704c465 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 432561456 1250 432560206 432560269
    0x1030902031507020f07060e010c02011218120f0306050f0625050c01140910030e030702030313051014070b0a1103040f050f0f0312040201020c0901030302030d0b0a05 73
    0x1010b04880d00303410803001051046154000426140020154003699045540c4903170583d04284030f29580c80c0031031400358044005601c20b088100c41c50420200003d0200120710001c4500e2802c86800c030350414000105031210703500800d84003045142407900784140707400c00c0040307029901460318643c0164008103003030060700210303042180c50b10303404031114005120a080c01e60b40e5030011102140030a660460203001d0f5040c0d0411122450009005c090301d0305901c02080340201001040c2c509240003e100110047c1d5042c001040c80310540b07840c8103504d038201020826132000c0c03914060184040541400e6100c160081510015500580444060765806816001074500241d03c600ca5101c00400c000c02c005c442960181600d004604035040210b140005a070382e9681000002115401882491402c0c003095110981c820f03c107106440d40f1a2035040131540c01c5000b030300b044025810102d24009050101d00c1041301c041070460f5450340076854000031500440c480d0008080305040d104629418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 432562706 1250 432561456 432561463
    0x121803070308030a0204030605010e040320010e070f09060611070623070f06050901050c040302090c070f0b180102040f18140717060d031704030903061505010f080708060103090203 79
    0x45812420b91941c1e850301141d000000d51141c041252424a00b400100d008000028100c1c8542d906444001501942a040119043e01a840745285641f901e1468581c2c403001c0c00f0103801425500309510511703080220384025170750181c00140c10401c031000c0c403140384400000d590b002c071281806c040c4a4106032031201141d4807891545c4040a1100160103010414034015a40c8051300511042109407242c1c03070160300303036401503031242036400007031001344007615100e500b440c1c00c0403404c1d10319480d0156603901c1d40000e02c3d05040035240c6001510400c04015101012100c0c3c040c08100210720341420f0981c000e6070494a0b000e1004d0407030b104142c04d040095990312070460561300e889030500514103603030024100280c10845c0605640700c8004510306040800801c0300441c0d00d43c5803c41500203c041c080000f280040050781041010100040800c0e400e01c15801c0c501c011705c0742d94492606003000500242c914201d5041005000001c004000381e0080816800800900e00494210a40d0000a28 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 432563956 1250 432562706 432562709
    0x306090111070b150301110d0c0801230112090c03053903010917090a0605070c060f1b03230309280c080c1c0b040b07031410030308010812180307 64
    0x8041d032829094034147d40c03d10002e07220051107210280149401d1203c1290801000c3c840d0a0007890055444010401098900b02c070b2004185021000e0b0201c40242e8419180050070588015025400520902005002210445c00c510090504105000c034000c0441c980fa0050101e091640c1c181e2144c0c950b90030340100c204103801149149100b0003101510216074081c018042c800c0316207000c00100c0300e01030416541d10700d421241d910805860315034243e40104240d903004c0200507140380704070204260f00c0c10103d101c6000b40d0f40c56064030747d02070003013401e945500103860b0740100502c00c0140c0c5420020303284c00c03c0c8204944000107a00d06c00c54552074007007921801800c0c002060804039041800050720501c845085558502d40c15a40b10512105068204050a002041c00c00203010481800d507040e08004c044c80d001601d13482c07444070552441c005555002031b072405014100245644400100d0141c9034034400f520007100340110344c602c540b150003140b002d4440c220515018030382d020320a060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 432565206 1250 432563956 432563959
    0x1e0d060f0311041a12100c030606020c0d030302120108010903090909020907030c02070b0d02120a091a04020a0e16080a0c020d110106170708010f020a0c02040b0310020d0b0306090111070b15 83
    0x80240e03079004178190f195105480b1101e2864030342120011078520030300980c1c0c1110355907000350501e840540244000303203c03e04002d50a0640030015107264141c0407050f24000e004050000400308503502d4000e080c2441a84040c00c0d15040c00f5020b00541d0b1810a5290000014240055030400ca40c005034200483e5903c64048800080303401c0c402c480c8540c004100081d49000c80c0400e50b03440c40c030030404030b0302d10310b00c06800c220352071100c005246502622aa0424002060b1251080d503036652559068000c561000c1d0024030b1f0050a10065002400545c028041c0d88041c440c40818030310080d03031444a649950104149254203990014003940407101030000c4101c44842c14641e00f0005075140f186c1d10030400c035903182080070807100045200b610a0940c00340e440494402ca66001c11001c4c1c40e01614090313141c0a4080c205c4c1c484000391000f08a0030100860201b446e601c480c003090b050450040a01e401d40e41040a03d40103070128400300c7d146503910100344900f680710303841d9100044400303100c2c29 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 432566456 1250 432565206 432565219
    0x130b01020708120403030e0d260702030106121a090c060703031415010f11070b03060310060e0601030b03060c090d1e1b090e060a0e031e0d060f0311041a 67
    0x3443c460844500500a503402929058004410728042c001245140c00d8003901400c101113006902c0030107040c110201150200d680750030004140c000030300311a401c0d4400389196554034203100800c10b100d04030180780b4007166900c46984c544980000d40300e01c00400010303c10140000c01804160181c5c2c000b0740401115181c00300a032400c1e990f070031000078004203158042000c809580700551b12481c03010085218147c05005200e14100300715803160409010a80d150084040800918400d4401d1130b00809110401c1b4101c0d051041c0003508880303074082c04500a0f00714404200b0b1441c001c0302180c540f842d01b920f50720145045801c1846103051014144455030f0b8904178007205201501c0c000c2520590105084020309544800b95801c543c160600c0c110290040b0f0000360040044d94040c42140d21404140c038030f0503100e9200c0114003181031507101004c030000f040405100c201d5201e07810182101100c450305903403c1da05d9182080200040f00c61055845001d04044100381d800007420f441c4025111 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 432567706 1250 432566456 432566473
    0x30c0d050f01240915090b030702010b0a171504080c0303040b07021002270415080102030a0f020c070b0f090a1d060f06041a16032309130b01020708 65
    0x418a8614207105044202000d900c03481190044500c2c03401180d14140c5804d500185024100203442000c070450b001804089000054111030300c074000c512520f402d0740002024159801005034041300764204050805685032030030f41340040001c50075480c0f10041520340d540da03103524110f40e6900c10b041644420380404030070f1104105443c2040390040465400303545a4000240080e42240110701c0e10b00300c0c3e0074105510700f401121041d40300c0c00f9101c003c1d0011868411043c09600c145900e68089001e0360360020410031448220301ca076030216040b05505503d402000c00c00240d40306502d000e8200c21180015810f501d680300c00d03040342c0c262003010b00001c64280d55030b0810005a0f03100c52009401c0d00301c031000100c0500c1c0800c1121101d0b500105040d0616080031846101034100c44210018040f0401c4a1010030030785048082c45184250342e803400000306603650181740c0c00b4442e40100c3d008420702510035560768031001407440400160340003403012100d100407072030192180c0c0018442c1c00348416 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 432568956 1250 432567706 432567721
    0x9171c0608060106140c1e0d090501050306060a080a0f05090a0c15020303160201090c0905040b1807060c03111603170f040b0f091306080d020304230a2d05060702010f0302030c0d05 79
    0x1250b000140250311000272041da940d005440300e00c0116410365000c0010042c9024041c0036400041c0c2016a00c0f00020700f0007601180e6404a84083d516964560b0101c0441c5c0c2c2081031403607006010303252180000c05d1807032015401035664040030f802d020344c0403518241c49031031620035441140341d203030406864000c0d295903085240041c50f0907101aa50b0809460026900515802042944008850040001624040c022514116449400c9082042d000400e05004008001106580c041040d24451292079882d03c489130b403060318164210742170700340680d1041004180944089074909044203949800d4008400d880d8400c1041680d0f2007201c219603402e035103080764406015a002501100c680307101c0d1050983c3c0e240150710400744414044158604a121103501c0d0780a1804080c00c00181107840e041180100910b01c00c4400d0074216101d00038070b002e00542420002040140c5040b03140c0001500005c00212580341807000345500000441d1510150001320f810441da0741c0702c100600e091501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 432570206 1250 432568956 432568963
    0x717040603050109090b040318080304080f0c030a030e010806040e1e072108091530010602031218032802190609171c0608060106140c1e 60
    0x52000003850480041a07490f11489844178058028000c04210744d143e0390102d400e0b0395486a41c0000c0603e0780f900207480c04040000d000507040d501d020704001070416900c24038109425080c0c45c0310350700007030803800800c2c0c000f2000300e00c41000380707014072542d5100c0000c94041c2c219141122907500c01e00b0b260140e03517500c0c20780c0384d5801c00207401560300740c5a070f802004240d8110451541d001d4003000f2132090000c3d08440040054030406011010b003809800d0549001d0b404c001580140303406088144411041c00c40e0b91119480b04d0300e0340d081c000e5414018020b50324000c906c0705120004e045030110b441003207901d101c0c40d03403800c003201165a00e200703944c2c2101003141c2240803c0140380c54001400845030010442c50f00c5070301320322844000036100351642030190420800603a80040881441104107446c50010030102074020960304081075003240701e20484500e031f07210301e1060b04020018041940d000341c00f1f0040b588540001d0340c55800d41002141842018254100e032100c10107174601d840003000c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 432571456 1250 432570206 432570209
    0x302060f0f09030406080604141003170310050d02030724032f0706020d11090f0d020112021b0d02160e010f050d15060b04090f14070e06071704 63
    0x80a000c0c4203074490600000c08010103460810703403500305001c14000240f1810141e81d0003d001880810185140a600c2e070100c1002e45100e100461080410700030b01110400200303035050313640280c919610f0500701c2c00c1c0c21085203001c2c0c1403068980e070050f90250f64040203020b0107404c4210340c4045481c8400d20b0704250040b101085004039080280204012211100c241140609140c0d1005803a451800f0108680c0c0043da08a441650a110302034130340c4040e00c10050702808000165a40e80d054100300034002c48000540c900c90031010f00c909005076401405100c581d07440c82009a155000d03a5400410204d460b82d0b0103072188920140c100c50746c0e500260200c000c12030407100802c00340d01e49000341074000090141c8803040407016010041400c280c2c608401003030007440904040803d511181c41a0307840395001c503082500100701848803410601c600c0444110b401020080c8007901c0c04c1c0745104040040004007800280b8154207003e44130032088800d0b00c1e9109909518040303040c80048141e0f04107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 432572706 1250 432571456 432571471
    0x8010c030c03140c0705071e0f090c0c0308130602070803060f150f130b0d09050d021b09090703080d0507140c03180103020d020408030d0b09010e0c030a18030206 71
    0xa091410038894001d1040f10b50403465440b1900042c0e442e40c5107101154400a4200e60300c0c4a8035400044400207031010044030b541c540c04202c038031031401105807112003c40e0010ba02d0340d40b4000d0b651aa258000360300080290f49410107160a9449448110fa410003050000d04018000514102000081001584540011500c40c0e00b170001c04002e000d550ba451958604041c6000c110694941003040040c0011072548000640c020751142ca8202498008074408035501d40c903440c0b071200304481840743d882c512403070344000c041d503c000c41003840078030740494001802440c820020071010442801741a0103160000d480c2c9642c0c02888150344020304048500c200060a030307900058080070345804840820030808000c5007055401114400444901d841a5040c154200b11800300751101e80054401004900059a12500311020392400c3e03d40b5840018860f400007c0188403600103a0341c015044000b0f0111242c07240e83e04c62510009001c40c161010715580e40303482c00e8013010b03030001c0e007244036410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 432573956 1250 432572706 432572711
    0x1305010918030f0318021002030a030c0e0d080f040915030c0801050402010503060108090a05060106091a0705030a0c0602450916020a020a09200f03010b0304030c020a08010c03 77
    0xa00c214090200c072000341d001030020320040c550124103031080d04034903401680407980040481d20ba03400180541204129800940c101113107404c4120b8040c800c51040400c0c5050443c24841d100d00028003c03044040010a00a400700d0765440007000d0310160f42c05004001c01c10000c0c144900c65a80d0324111610003143c1c40c1508400118403d43d040c0030301401980d041e156282140c03103590066509000081c10014070380300302502c02010030000c0140e14001c0c0300c2500e42a00c66820700748189078400da0f00100d05c2510100300f1400c4001500002114900c0d00e175413a10300603c00e042e1520074041d03c904a008441240c081030038900703803d18211006005d217001100f4514041044a01c1004414071840c0f20346e00000520000d2031000d48c2007840030703c6200c03610603124405804d80c0040c4a200180c0c02c840c001c07695520905103102880a030325040000380d44100760800c004400c0303886c2140b005005e80c00c030440000c00810201406528880401c6a004080310a8113884141c814001c0c4043d404400000b030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 432575206 1250 432573956 432573971
    0xc21030204261b1c021207030b100815010504020307021002031014030607090b130801110405040518060412200c0103060527070e030a120906090b0d0504020f13050109 73
    0x7114a80740004900d0140034034080c58120104880001c03d04a005c1e0f0b0000c84101c00c14080400c14007143c0007851140201c8001c13030038074a4a03003490701115080360656074001c00d034000810b078404182d241180c2d81100d02681d070750f41d0300708100e0400b00c40000480da84c900120031b204c10308062000351415613000c0302840c41e4881c402c9003095916081552207002068208409108550002c03008210304503044440440d0143d55000580c00c450490401480741d003000703e000c1c401c9180c24011b40760084148401c03800d014001d04443c645601020307000400322109410881c58640c094607044420540c3c80082110034804040d00640b0f4403d003d000b0360000340361040c01300b02d40ca0700030040021003800c405880302041c601e04401d100d40802600b2442400b014411003011613074104202906903114050b42c01950000b904081d0900c0800e070881e100740100381d242400f080003400e00381e890390140c1c40300214440d1520b0000c01c100d1004800080d8010f0746410500c010490351741c000781d04075006e6890421080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 432576456 1250 432575206 432575233
    0x501050a020324060f0d15060305060612130b01061e0201020c19020f0a121101020a0f020f0a0305070b1e04050307052704060b01030c0c2103020426 65
    0x20b02c41118031106001440e02c04030044541007200440280c400b0f490389280c005202c0d10b2030220342000c032180541c0303501c40f01e40700c0c24204004506030003048541400d002c80d00381031002171168001e070002c04454a98040008000c444000a0440c80701d820040d00702d12541c4501c4000c00c403035450543c50807580015021a40d20920510031211201c007480c0c00303040b201d8511019240c84840d0400c00741d81c48101004240c4560b41e501c00c2e402c0003002092828501b41805290024054031080031a5056401c50150300000c00c41001d00070f24501e0f41101c413003400b91040400206c0242c200c0d00081c145105041c004030302081003600400b6404d60202c03501c3c02d10009000b082c3c610f4402c80c001d150300740c0c000d07410800403820304002440703800d1100f246442c544c030094994002e810700c0482c0d060b5004c9407100745d4001c003541c051040f00d0303500e05940b511070650703070582d00ca50081e07001c0c81e562040c60002c4d21001074200d503c6a41a500508804030120141031816440c12711002c0e08043d2911042c0500d2425501c0c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 432577706 1250 432576456 432576461
    0x304140601060503340306030b0f012106200405010905060c030d050712020a02012c060712020702031005010e060a030b0c1308011407030f0c0215130c03050a0501050a 73
    0x40b212580e59191840c3c3d038024031262480ca80058000d12408070103101c8069031280f0062500c04041030340d0029040346581414040c4000252816808240c04001809810210821088180702400080c183d2000e2072038540000d12408040c141020700709002c1c0c00c0000d0640e030041040300d20036624200b103551604c040164038030071646080c0142e030080000002034030340d83e0021903114903d4102000c0b180b8075040880180da00140b520380042c2d540b9200c1c0800a4000f4400c1210840d044280320702800880c90f45a80d5454040c046100b84081c8079100c1000c04141d804542900c0e50180c140c1e5122400403841e0809004280140e07440c4403034101c0044c0d220306203900301004a0b0740095826900362200780d00350916030702c1084142080d400c800380126500b90240225445606d2103210700541340f0b4441d0000b011100820316100030a42400c16990140e61b0004090703000c00b50f000140451078561440e00440300800200c0245000c3c003a075070000c140080400c903403c00710b0040d0001d2242c1c1e5112440341c1d04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 432578956 1250 432577706 432577709
    0x60d050612030c10090f08040b12070323060303040f120501060503010902092409010605031602030f0d050604020c070f080609060f010611100203130204110702010e1504050a0b0304140601 82
    0x2455024081811072031080345c111007a2203004400784050720086444040013940241c00096031081300080e941d031a5251001115030001052404100c003412800c203803200c0c10166102401e00007801c0740450600c0d82c0c00d03c1118020001100e20180b156a5003d0041ca9101705281c1640c407035203068000035a609060241d0304d001c41c1d00400c0c8588942c0d408441c80101c000715111448000b20040b49000f103603c0d0a947c0a001c0c003601d464143d16841c04500b030404081003800100c0840d0014400350b0f0411102c18141e81c81c1c4005440d01180540e14040842c009005005d41c01c400c2d07114030400080c116000080c242e054030030b001c5c29140d85544101c42c0342c3d5220000d6865020f203035540c000400031036104110581c080303c21001034401c642c051212010598000f610004040d0000007417203001c600d050310680b640180c05660040c03c05440d40c0000e4582511160114050741802000721000300300e03202181e002d031500510032524a82ca4403075001283d0411201110703c4416025003007d0340c94005030450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 432580206 1250 432578956 432578977
    0x1506020705120102130302310506091003020303031519060522080601050402070822061709030306060705071701060509060904110f0307031a070201110310050d0f02060d05061203 78
    0x850305c0d4038560030b111800200442612420b4400718074440d0300710384400b0f401c00c2c940c21a01c01281904100e81009650f0b4070280c44211025840c410400041c0c60210540b5401500040c107000151064000b1070070400d003001c15100c072034074440c03000304100390428080d01e11012064801c1c0b108080c5402c83d035082c1e81c942d009500c5168000001003009140c07640060408501c0741030300340c0c14484400d4490008418100c007000b103d403445a41400310a80c02410250703440e410a089581a040c22095107440744405000e180c05620001107103028081c04100103001000031081402d5901410350109000308103a0141c0c91003405000003251041c0f40c001840d074050368022101054039134442c400c11a52002c00000c4030b8150199550001c080350410303070413003d44078803014404500e1500480090841ea4400d030441c00c0f4a07818424802410544c000c81e000341c0d034056800c910082ca845c101440c6403400410000c1d8444400207040e4030300c194035003050703000b04403c5d00d006548038078408016449024418100e0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 432581456 1250 432580206 432580237
    0x10e040b09030a0903060f06170f1c0801030605040f02030a03030c0f0e0907031a0d05010f050a0e120a0c0602030c07050d02010b1507080909091606090e04151506020705120102 77
    0x51011880c07987c8030015502e80c9080000c2c2d02c0340d070b90302c030013925239800310b0101606d40101079024134203031051003c1002c1354150300d410324600201e100080c0188006010140915a844000404221201049030100b03500101264030780e0784549002809400c6e0a104800096004014890715602407c00030391071810080003904180c1d036000c0100c00411040d92204814100c2072910005521119499a80c60b40144000700310b403010740000300e0540300c0140002e401240380080d404003048021a40c0c43c866100d4828035503030b0300c0a2100c11500080300c01c2024040910010500080040744c00040c42c4652244003540d175003030040300081c0d080354214210306810140d005e03044280462480000c5c02c003148158051420804020f010510191044455810ae903001d040c1111614000d14054802450940380a10906041501c29210b80502500041141c220081091303d5100507412044500e10701141000910755a100029070f11300341441410700655440c040380700c3c80101802160960701c0e002050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 432582706 1250 432581456 432581459
    0x10212101a12250203041a03010b0301150509091003020102150c0319021201030f02090f061003090305070609240b1e06040806010308120f13021e09010e040b09030a09 73
    0x40d61407204000340034508660b12402a1100d02a400c6484903241000364000c507111802d1840d81c2001114801442c7d60043c7d081c0010440c110b803c0d012241960f000300c40d80c1c0150012500103440901400c03070680e0740000d03070310708001c981d80d50380c4102c402312070003642103984c400c2c14507860840d128000d1b1864103000104000040c00c16410070080c0c00c4c501c0002c50010710340f03407400c4841502c1400a800880d00c81b28450740704001d5107008171110380c1081e002e806075801c0e03081140000303007034031018131000f0249605c5100041c00c0c9030068094642c0e2540286061245842600d01180c00c200000424891a25a0042c890b0070207498031404205c020017901400400e0480c034113908c4210213010540d54003c2040102150a01c000c1c072610340250301c281203143d1030760506072215107401002480071104402803c200f10320004250391036a00c01c0d070155819a03640d54494104007e01d4480f41585803c66454800060480805200030384154040c0e068075500391140c40e0100c0c0ca0344200e203411000180c070b2010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 432583956 1250 432582706 432582727
    0x20705040c14070c06111203011401090e1303030e032104061113030314090303032806240c030804060e07180209010801141c05070305010212101a 64
    0x40701101c5076810300c00041c1c002d04403080000d502ca0b00f022161401e004008200c42c03900714603940700e101da140d0301404060084644603521404140b240c4d41d10b920140c6415a203e902031141280174200d2410340901a02e01090540c800000b907031021030000345443c1103584498000300981c0c6010384901d4680c1e07551362039048509400e450150080d60780c1591151400c140c1c0142000812400c20703500b00d03044140d869803c002c3e000d900500040303e941e410400401d611660040116540452411181c2c80d2a86082e502e48000c0e802900c0030a06c01c2d8640b040208140403007003040a120180d11034540d8100084c6201282c8a6084100040101d0128404140001c059821102500d00d04c030003110700165440c1d05040746150f030100c210b11625400118441e49591004410740545182c6000006510100000c03e0080b4080c000351142a0b591a141c18104142403150200858200000b552211f00f1441d4130704503250700b502c0103602604013440000b1914030280f84104c0351103850f20007504022541c2e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 432585206 1250 432583956 432583961
    0xf181202210106031208090106030c0608150307060507020a0807122405010e04020301050a06080c0d1104050403050c070909030212030604090c091b0801051011070b180411070302070504 81
    0x516a6640d8121031080074900091160b40011801100200c21407583d60201038017501e4003900d680420b0b4189541400441c5c6100c0004007241c5c16803810b040a0750314521040c2000068510703003640344c09544e400040742c0d48e10101800c8914000c5030300b040010b54810526544048034030036501d02070240414500410746907580c003d03485100407010540070401a07075a03822528260010099002003209010550078240f241c0360f4170030074041c0104001800d03c0302c3da40e91103503010005031045007052000e104200d0483c15050901d200540140980d0030545006040c58111081262a03842803500018a41210380030340d2180c00d40540160002001c0c07104034490b560710041c41c154004d915140910700060140350041c00034a1480310000764181c140e0203801a90300a61034103c1003295000060100d40ea84442c2044100c205085c514500c02000c4900c40c1018442c3d0b00602ca04240441c1c540350500d40362048880400302202c080062040c0c1c070025034407500640001a0060f44030900a00c91402c256 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 432586456 1250 432585206 432585229
    0xe0a090c08060f01090f09020922060f020d150b12040804180f0b100504090c02280302150705030a09051c03060509070804080a05030604110403030f181202 68
    0x348092200c00c1d480d103200628111040c1c600d480d0009080c0010041400746104900745049a5001030054404a80015100701406401034070040710384001d023040b8089080d00c03010045d070b00c00018003104110340c01c0500250020f0140b04550360420013110b1510b010030888a003514680544103042070103580400c2000c00380100210343c140410040850740450781c030b40740501c0709016000031440c10300c3c0040c0d10701990401c2e91071500410300030200d008125040003d035015210040030014944078400c000728681942d409425003c100304204c0c00f282007580903d1070488501070f8089403c0e500c00a84004c0b0090811290f04001070424808590342c80b0344c2d070b041300c40090300030421036a10803503400100701182195480d0700c002c0fa50380c44040142c1c2c1440f640c000d62141c400d04080d591840c068858804034480e10f1171000800400200044107680c0b681d22075080c01341301c2d0342e5440e2903503201e10300a031180307071440350303000204000d0010000100340740314004007901c0d10001d18920848440d0709101c8028802c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 432587706 1250 432586456 432586463
    0x906010b0d09051e0a02041a03031204020f040914121305011107080102041202090f04050303130f05071715010821070218040210020307081803030c0106090c0311040e0a09 75
    0x11344845a26109800003402c110103408005444500d00910400c000c407144107070100b03822580070b0310101480e580802901c04041020410003079030350342d5200044900c5000c070a01c0b0703441490b1400141c20b0004815400f100740c03114004540c00d03265280c03003002181c0945c2102504081b100001804a940b06250800ba002c3e0b4850444405036101c4c20103c0c05d80c2c02c42d07007060098106103620802035290070004580c002d4500c451982c4c16007002d0311401d49074403004000c10014042c01508004000050740500e00d016009002d03513644980b0340300d46c4c41104043c05401c034418410121440070b0119a024681e040700c01c201c00814901040b80c907400c440c112031568a00f00141709100800140e1518140100d0709039030000c80d007610f40382c540304029100141030718107000c6600611409001980c10300803103007401c11403880d0040c803401c0c40c0002407440c480c0c0880240f5075400c080d0300251021351070300014000750140d01c06102040c000e010001c610b00607403041d542c016941ca4085020312980d6805101c1c060702 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 432588956 1250 432587706 432587713
    0x60507030302130b09030c0609090a0513080307030203070306411909200304021e030a030c02040c0e031e01060b07051c1d010f18030b09060906010b0d0905 68
    0x100100108412a0725500c0713140c04010000e0311007964681800112440c0303104942c07941c10114040007085909000a000340040750340c1e940032405200d000441107041f2584405a141d49240c90305d0000d01942007540c100011905009020bd00b03100402d00421113074410080340d88403240e07541c1c892020310003046050212426030307030103030201521001a20b200000030314001f521458036200c110000c5a02d0580507501c6402c07004124400c904414040b00d4100d03404640740991454170034610016403034090012681441034041d40010543c00c82400800c25008680400c40114004c40030b0302c65400c000280c6a054000042d03014291020000030300d00341c100400001041612003480f6031095000c0c40c025a0306034840d0122040405400d4103074a0400210b1034010f00c296030716266241207803041c100c3c1074180942c44c1e00a83d2800d204204004a0820000d6030031049aa03d09101511000c282c800300464003d2000081494800144050483d1002440e1a00e02103807581c0d2000245203020702101c4501 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 432590206 1250 432588956 432588967
    0x9030a091413050a060911040e090d0c08090f06220609140910150225050d0303020c150a02040302010e06030c120903070b041101030e010902030601050d03050d2a0306030507060507030302 82
    0xf2251180307c968600d603071900baa07540d04200301b00d450302c8070040031800c1c0b5500074041442c0f401e03809207440d40010b900c8031959485407000c10010741d44540c40e64206400083c0880c40c01c84213105400b06d046d503071104410028181f610307400b0441d0300200d280200080c81d041c00c1aa9011420081c11060340103002c00711150308543c4640c0500040004a244400142d210340c01d0b105d04030410305c01c00c44c03070060354040d0180c07030614040c08540c0c68041240e018041c140e0201e112041510b081c4060304c2c8401c02101000041e11300004484000e400034001a40007894a0005000d00d045c2081241e004408403a07c660400b0041040300b1140c0c030004008000d980028003911000410360000c05005512401803242000f48c484e000600301e82851201342410384c104510800542c0700030079800e0550380190b03911074218003e03080a4596125502c00381075054540540c5003480030803480b610f0500d2190442c1c44444a510100c128242d5085000203011900098000c021240c0540020200310380f0034240541000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 432591456 1250 432590206 432590219
    0x20304140a0312080610080f04080f1207050408070b090d02040203090708030d0f050c070c061101060302060708130501080f010b03041106070b010303120603050304090906020c0609030a091413050a06 87
    0x10f43c1807034122004100d1072414001586840046024001002d2500c1c000e540f41c401a45c029400c03004e4000741822a002980b0486015040121a01071181015105407414611001009a4800e1040414a00130400c01091107850f0304115010300400a11406680c001c54080000a5001400e050510300c94030b031001400c031000744090400d4005003035001a03400401c004241c207175140280003120101e410030064002844450004042d544031b494082482c03c002e841c2580105016003010350302403070216200d81002220000bd02c408881d500441344600d135a900159045a000e54a44a0640805006008149000b0007859001d402104039000c407120b030701c02007145039014140a450300340e4080014018940c10484180c4892844401000f0440ca5501c7d070b2a03c0c1d01890060750401502c5081e01c200b4440c454055407007401c5500c060715254101664455902e50281d83c601c00425485440007a03500c800030043e000152003d000429180072504000b402050300503d51081c8580e40c50010555 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 432592706 1250 432591456 432591473
    0x102011b0c0c05010804120c26070606150c03050a030207020d0f02090603120a0806060408070602060f091501060e0d0b0a0204092403080c1203250f020304140a03 71
    0x11220303500d0700d03106500d480c10300841c00c1ca0150070070343c1130140c0003040c0800030384403d482040007100c1d4036200e1400c542e44c0ca00011004c100c5001e02c3c0c0102d0700c1000074002903040000404440307125510030890650381d400158103510410b40300002080d1601c03c3c000110340150b005004900705894018680281540024958403000c501a60150114242c0b1000c5080c1055282d412000440041161024901d1a05030030b10407014a4030400c0404004940140c65090503100641054419036658030740b11301000b55100c408407010000030401d900070859030000032a82c80034030b048500659010f030b030800c0419123294841c040c44507040380e128040c0d8000300e05054030290041c6889075015903a5850f00ca48071781a2a070301c07061100c0094040c80c5102641c010f0841c560b003140d511407070b001c0c0c4a8460070760650612443e000c0d218a0300d0000002c000c2d4040c49003088440d003c8002c0d000c1d8450b0a613684007201e20400071884400940c2c0b040100f80900c8021004401d60050000c01880c1760311307121350b103001c0d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 432593956 1250 432592706 432592751
    0x1419050a0506031e15010318021507080c010e03120f01030825021002010e10140a0b0d0b04030c0b0c1206090a090203011802120d0f0c0303020909090709061403030403060b010201 78
    0x17031034800b0400e014a03543e818000d00d4161441c0d400000310599050300020440e05070022a03510342e00000424004021070141038580860585000300300103c0c0d10307490b05444c3d502c42007402502c0d440150006401c00c4509807090306032500500c142c2d00f4000301c2400c20326111074210310411603c0c400718400d0010303540c46d40d0b046440705413640085003800c0004800c614280a80e90454012810010f85e284816035800d440c60780007113100b00c08245480c0a0f400308540900d22207014050f039405004200c2810341006da13100a00f445010074030a0350740c030740c810403007a400f032002c02408424034000850324a24001d055207800544140d00001c0700817003940000e08583c10200285000f104180c1000103601c2c141e00c40880940c0e2500103001c601211500050241160350741c2d20040c4031031108800207261080e4195010724a01802e645020b09044000640d1042ea41c810344480da82054004640e41c2c510502903440108080d0096007080c1c11665440040c24400d80d00604642d41d034851500c894000b0105c60341d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 432595206 1250 432593956 432593971
    0x1e090c151b03121d0a051e0c1005070f0c230f090903040906030633091e09230705211c080403030c08060d0b130602041419050a0506031e 60
    0x3c603400301b80f500ba42001c102449140183d0550820016105d0000c07071125003840c81120b410121000c043c030151040d02510790003500c40d0704010b140070704001941c081e8800740c6180754050341c404404450304905890184a41c503422000c150009031580c207001c5402908210100301741d03424203071101d5052089948550060f1603c5460396082c2c20700021f49500c961702402d200f144940710310610180c40700f6a00d40c42c03051425403503445203074140030741c41051409803844500300240309800c500c1c100305104551000b04203400034030501d0f15203188280010365100320b4030080c01d840401350207029056441260403d85804900a204058283c11420f85000130700c100170392150045410903017801022184c0c040c24440a0009007010302c40f080d6a0102490320b415807001a0800030f54841e102000040a00c450080034140081004562113030171500c541107410059a040701c0001c03403041c220558410a115440c0c2103102c58006210a040100c020743e80854010724180c0d05000306c2c403128400e45011960b12 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 432596456 1250 432595206 432595213
    0x18020310031506052803030f050705011a031e0c040c030f050106020a05250902030403020f07030501021b060c070305070c210c0608191e090c151b03121d 67
    0x510151800c005c050890b84604418060030f402001c1c07013001c2c80d18442c0805424490514007854005124004460185500030000d00c010b000026800c43c10f002002041c40c0b01e805004000d00c0c454400c910107928018a04009005484c04c500034400203052800b1808201920342a81c003142400a010302402448594001d1440c0003a90400c2414880d481004590f04183e814a8030a40519060010250307507038642300598941b07403032070141c0c40d05402d882d1081050150304000010b0100650107019101500118a580680c3d0000c0c1c0588030710007202c082914071010720642002c203110344040c1400611641489140716141d100c00003102072800202640010074030f900f2804c100031415100d004001c5401d0000c0d05082c801d40c41e030340006072441c0004100b5130f40c0407002c0040340d0204902c41c0b0301e0340102040011b10500d0420244052040c002d214041080044004550303202e000742c149030791070700030451100c3d060f40da604840501e40c142c01102c44503203e1580110385076486c0002d5078040c610381c005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 432597706 1250 432596456 432596459
    0x1080606010905011427040c020706140f07060f1107050307120302071e050115091b0e0a031401110d0507030b03070803090402030c0c120414090118020310031506 71
    0x4042c5196504094104081402c604444000c03501c2650540d0051503040c400303401440d4407411010180031380d42588541088a880600c5d038010a0031419a1501d944090641403948a01ca485100d480791040304c02c0b104001100203c1e1141d406000300590404001c15000c660800c281415080240d0036140d035040014898104102941401c0b1010501d003003e50511886844600642070701906020003501107144280420034290302c0216200303030000300c0e155a1910380102e4001880e1019201c17984507070340804d2140c62809032541c650881c400502c40056141182e80300e80f41c2d500d01c0c2c50485550340d220400807200300305e602c014040d0030465040019840c50700341002401e0300e01400f1050301030b410500d000d0000f41d41c00300480c0e119440c20b44016a0fa500c50601001c0c0c1403069600900e002c2c040d00da000c00c103103881040104202e6030004070081100084108020514500707100b0000346100c240b0b00d04d04044181e4002c0c0d40c0c09060441c107000201d6407601d4030058603001034100903880f40e90304070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 432598956 1250 432597706 432597709
    0x41707090c08060a0e0402040b060d0b12030c0325060f0207031706031009030504080a03020f15060604060f0c060c0503011d01050609060309461a0a09020901080606 72
    0x400d0301c1c481e200c1c03800a0640c1410070100d207041489005070b41c0c00152540000d415501ca81c0c00602280001901d015035a1581c0b8203201c0041c4595012907100708410302c061441d80c000042500c42c0c154904014610706281c612884019020740103048040e2400d025a94020aa8511804c007620f07142c400e001da070f00c101f549401044590300700700d11403000d0407170b100740003480d100000d141ca90324407034010010715003800e41820f55007805942d11a64091159011185c10586d002c00c98000c1510007100b1540400311982580d281e0900484030150800740521003000800d00c242690140d011407810031520b40c4200e0b44400d015209000e40303840c08500000f00410a031015104241c5c50320300d00681030032107541007500080091040843c100d20801c000700118213040e50601c110314040d8048160100110030b03098100c00200726100e101c0820036004058000f140600c800d042c504180d10a03a0014500350940000300c0321070000e0403c0100d5a60b034211400181c42d0100380e24082c00c0104024a22860f0010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 432600206 1250 432598956 432598961
    0x10261212060103200a030227030d110a0807080c030a0f0905010203070312050406020903030a08040614190c03181401180b0a0207051c080406050f07021e0304170709 72
    0x3007240d81014606560002e207007600b2502c80c8200103901040960382e11320740300124068040c020359505c0004c40800849402c003a09440840314240036026107195581440e01918411070140d014032158100e410b200b80051180c0c40200b00c0103100b001441d0800c0880010703280b071a000030800744089000070260010681c0c11555000013001d0901c011442c00a45540007400f2591809031541903540b6040402c08002e015016540c1c5910050100c90701c078520010000c04880c41030390300b5030727495181c911851105243d08120a00c01d00341c80316514080140851040e00620030844101c0406558100c1003101055482e000340343d00d80243c1041005010801c0701508417011403103854414098051070306e0000d0f0341d0b0070100d1b61124000c50010380310105810007500b00b608a262090110b00045200d0b0482608001410300660140d80c0c1040a83d607901c0303000c0700403d0140c80510160b800860304100c0100e05140890801101005880c07c0507507031250050783c40c81000c07101c100381d0080e8009001440c141c0c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 432601456 1250 432600206 432600211
    0x5130b0105040c051c02040b0a0207030314030403200c03071401120507082716030b0a20091f080f0f070c0b06061b0105070f02030310261212 62
    0x484040083e060202c601500d40c0c4904003a66000ca034080040b5010601250b0580780101a400c900c0e80d5200301d0504000c3d107400443c0000c03000304103500042d4103007400b14000e4178801e84d810340b540001204111010002c0c040e0b03001007403100e44a00000e46034192000c0c000c0400500742040544c540988e20b60024050080d00e800f44000b0300e03e0300003001080390f031050b580e90700503030069210302d00c2c0141207036600c44080d05d910b202201481054038055080c2412035414044034001c3c0ba106600e5140d240081c0141d40082c0441d078502442507400c2071010501d44010404400010407962448054102c0c4010850561040401003002502080058242c009100b0360126075072254265629001c000580717221301c42c0d0801703082810b5580004110f6203650b821105a0090030724001c50000b0400c101d2400390108135640000a1030041c090020280004241d90140c0c25020f007030403945003025030504c560b1701ca203480c030003403019004600f20303034500140495011000107400c180c1c0e036128241614101003001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 432602706 1250 432601456 432601459
    0xd030b03190c2c10060314090d030b0402040e041101110f0d050a050d0213030c12150207020402090d0804030c0501170a1d070902090901090605060f090d0605130b0105 73
    0x1050a0400040c0c001c00518155107480741150842032500c101030310702c0140e90090714140c3d03503c40e00344065443c4420b8a00704490300780d90300b40000c12074008200d08411040e101132400b50b000300042800540607030801e021118025200504007503654419000204090710281e500d100f1841040d421543d00074410041e0f003183c88020503101204801041d0317140360300d005c6d4030101300011030b41d551801e11a0084030076000d40c075081552200b003000c0d01d01101c44c456100444102340c1c883d4000619900e540030036800c0d10740006008080d40701e44550403000c0d40c030001e022a4407d81c20000c141d91503075104814003031107004001054440381546000d124071031450700590306005020800c0c2c8030f0580000c010035409a03042c46c02085089a09c109407a40c51000916150180918003020800210303d034050f209500e01110503851590380d510131001101e0309030240c3e030f41083c000c000e0041c030340f03481100800103400e020700a0325420076292111000c48034240d40f20f0f0400510fa42e9100240f00a8a1403640035050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 432603956 1250 432602706 432602743
    0x51509010e0f0405010603120f1d010212071b17070e0f13111314130305070308101a0910020f0705121006080606011206030c050105070807050d030b03 66
    0x1802410145101c0c01080042400201c400107800c1060a400080040d5807241c01e60454100100c0040c10307228822a0307180000f886c400b0f454003517a400d048445c405650607009405030124001901301c103a03024200c00c0d18001d40501c62402d084000c407440c10020030710035035082c1141b0240c1415a050074419804080314851800c04d012100030070500399074001401103040008000710345044109015060404d40c1d00c007602c64407109015499800c0b020f60307034200c4900e035421a03485072014500c24030120409000500700f444001c00080c0501c4659401400071355080242c260381c0d20464440840054070015441808500610581050300680700144000e0010340740303032961036607010341c4d82006100300351080d2034450381c601c50380300d080c8641081490301c40d105000302500c8030001c580d81d80c01a2505400141d00048183c0700214074030968003902c1e0310203c000e460754a49001100c1c1508044802d903242101000354500145080041c04840607141d00c002c41d07298040c03003c00d410000807020311412400b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 432605206 1250 432603956 432603959
    0xd02010b190605030708040203100509031804090f080708120a06050f0919020a050d05250c05060c09011b0606030c0b04030819020a080307030e0607111b010e0402070605150901 77
    0x68104050f079034040b885141c06c2441c1d0382d42d0b00010740b402401d94660a601d03440d26041c0014001c003c402810320102020f0b807a02e00b0488681804129444404098840820020a0400200000028062580031b0344980d0704004026064402c0001e050701d410300410342d2598100301c0360820032580d03130004000701d480000c0707445c0500614180340a2000e01c0c80d2070540c00500f80703040c1d0380207900351405c0340688441001585040c00d16020304484c04042850580240040049803910800007641c516a001010f0106510b41503580700c001d03044006142d06001d5104852102420305400b400301c4c0c40d00440003c01e400d0300e035080051071503001e5040607001040820042c004150303410111284000300000700d040100c09130303400b00d00307003102c42a0041a0301800005d01161940c103400032920401003405a8203561180700080c1c0c0c1c05244440d08080c1500240b004400030b020040c0050308040045c106014010f030078000040c201e0340810700c101d4110760303a0428070800c592240540c20a000c42600c4081403035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 432606456 1250 432605206 432605219
    0x3201c0e030111161b0b070c08191203020a090302092706010b0a0c0203190f0b01050117010509130507151b020901051e0d03080402090609060f1c050d02010b19 70
    0x4039030072400034141e420170b1031401207012036149284004004084582c0d403aa0038928101d10394004911071454a8440d00d02c40382c0e103201d400d804514100381e1198421070800c092110a5010b50042c0542c0740a001800500001685034125030030300c07a0b152101030f459a0703a08655040a91801414074000d207601800041c010f040d10310088440107000c905210a2800c82c034030010b880c1100f040500040c1d045084004400c110a11041e21451845a5061700090fa00c400045070300718804103010b051a40c0280c010000340c10030b0304d006034004401e410195a0469035071542440c1203207951010074009445030302c41046592160b1080030700d01c02c83c0c03030300d06581000d070b000520a0501805094421200c61b802d102500c18881d06c5d5444000d03000c3d01c60f200c1803001e801e01806c1004100c4090b4000c030510400118540f90140700240b2425004208d1054000d840c8240102145c460a50400c00039007038081401040d010030103d001038a06500101d8034076489411b1041e000c01c6261400c040c22903000043c0040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 432607706 1250 432606456 432606487
    0x51b07050a06080a231b0c010c0507020a091512050f0a050c03010629030601110d0806150723030d15060207050102030406022a0d060504061803201c0e030111 69
    0x4226410007113460990126401d54452194107001c44840d031928027120b520741c0d0858054070b4014022191031040c513580d00140301c00e032401c0341c5200310005030007001400b001181c2c01203100458010400c4602210000f041d440c58008582402d4039954000961045c0c1d0746424003885010340b484000301d2668140ca0290084404000c102e549c0e1000c00200000d591a481021018894400001100d161550004000d015410103560803800b600c03d1311001c40080c01640c003251109640416000c01e5910500d0015a20540703620b8000755030301040012a946081a004120807a1281440500080e26152010b850b20810741e11560554205000030820301c1d402188196151600e00003420621039802e41c0e9540c0070041820702c90380030715035540550501c00396911440c07246218031400c00801c82e0314100da11944104420080004030344040310413030f0305524040040d0041802003107030300d84042900e140700c1e1806152040c1e0700048584122aa82d883c00740920882641d00c055540d252102070f0300100318 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 432608956 1250 432607706 432607711
    0xb060901080a051f0605030702100603021c051e060603010509060603030706050c070c2706151202070221060f01150f022803030f05010501051b07050a06080a23 70
    0x40142e443d800650b9072005100c021250210344441c02080503100c800103041d0350415584800180b2410b10441081c0080d4480e0205598004203980b0b00405592400d055810004404545900501d10305101b00c4c5030039400098841028009021319142c070100f0b0501b101e07001131401d4141c2e4050350074041e10b0344000c421100d00c2600520301103480e0b5220b011a00c0d1130f208140d40105100c68240d000545500f100081141d9821001000110520623aa14005540301401030b00f413010403640c04410300c01c2c0100a44050460700250241c00e04581f0340000310700e44000c0b808000c10b417070b58140d500701240040c40f495a00c80c03805080c140d0790354141106018200446d05184051121000301c180e402070081203c00b0300c01c1c2c02c14555002d1301c400c401c480b840b925078803201140031a0509a115200c01c4403801490b051ba0010b80d031300c138145112903000703808100700f0b040501c0542c01065400b10302500e5554098001d024907450300181d500b409003842d0115240d0541d1924404013001e02000c0c0701420840d95034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 432610206 1250 432608956 432608971
    0x2060f0714160209070305040201020f06190b010210020705011407034107020c0f180f2d040c1502070311131803020607022e0906020a030902040b06090108 68
    0x5896a41c4018281100c00b05002e000e5480420b0508204072036526400841c40f0301d00c00ea007a00c101c480d128885c00d54a500c1543c400c0c00040c4000c000213446c42955125001414052040740d070040c00c40b021160407a440303100c1c2683d031a51503688210410f0401250a5003048103450100328451004103c29400350556034a0760703003946072001c2601071030619103442442d0720556500380814103140c000a503413562103c4000b8008d00501412050524020070f030030708041c85501b12005150b0359621885071510000381018900d0303614048204900e4404414001c1000081c07000d82043d007042e0074100e0384820f00740d1090b03580c1c082182480e0b58a075804a05d42d800c86c0d13441840604600d0408000440021044044058481c07402010042c62100b0340c3c80366502d2400380c0c080d80c15a8403007010403a2214208004075050b401e03a9045080c1c40310400c1100000300c0800140090745440b1540c0e4035050b40e100c8503a400000e5211070b8940190b1410b84118040c05004640c8285041c5a0b00c0029011400041002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 432611456 1250 432610206 432610247
    0x16020f070303031e0e10050703150e0414030f130f0305150c1c06140306060d030507020118060806030c100207061803060501030812101a0d0b0a090c02060f07 69
    0x18000d185000101c42c0d1404c1e207543c00b4072421503240195907981000e000600f5150b0300b044042204540a4443c6002071040f20114075190f50904000d0312845002800841e181d10606c480400c00c41000d00180110382c00304c1440e19604c11040042c2d28951850b5044002c0ca03401c07040d402c1001880000f40049802202a0f241402e40c0c0e480060108078017461909880d0094000401c00303d6440941c0084291170380e2081c81b10300c0703091090501d6552042260320a0b00101c8051101300480c1c01840036142d02c610501d0495100710b6843e01c4901102110382c001400310781500184260381c41e06204a0340c0e00c01060720102e5034800340d200020340d904942d20400c0c060283c503031442c2e120b99007070a840802554100e5414031495a40b40360100090303110581e407001170310500c80803d610f101e4020001d01140e031000d541001c4504d40f4102c0c140389510490302204403650b50415030790952200c40800e001084406000940440910b1010b424039100800e41803001d1030b13003820042e04a80120458100c0c0d005240700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 432612706 1250 432611456 432611471
    0xf180b0a121d0f07230d320d2309030c061809090606030309040b01030b03061005042406030c050f12040c0608040201020a060203090a0b010e16020f07030303 69
    0xd10001c11003070168164094a0b00b04071101c0010008011101022000444044a03550618000c48000b07400003805070044034072110b2000e1510065154445009038156903158030303815543c07400d456050468850300c050303844000e2415003041c45032070710200c15400d001c00414005140c06100045589100c0d01035100810766643c1b50706c0802c40002c82d224003400650742c1c3c411340b04103100a001c5c0c0c1e41c00300c3c0c46022030000144080c003011600c40d014240140046080000713910401001e0f02069200b00d04050303945020101c0d950f0200000383c050702d044c2000c080c045e81000240004d072404505080c0164030032204284c010311003000003800312a41c518001409804016048801d0322402850f20301c1d4603c007165413001c11094050250165200304c400e28a030aa0303c03001517170140000c440180c00740e007100c903c035000315626800440d800603601003945c4102255035218000c821080c0c0103060000b11010402521307880c4031b01825004400f50004200301d003100d1100382c0d038a402600004003015101c010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 432613956 1250 432612706 432612737
    0xc02190201080c121f08070602060105060702011110050f0603010209150c01091505010501121a01081012050a02040b04110a030908160615051e09090307120f180b0a 72
    0x3550400c8103040030794a228241480102420340780458408817032891440c0c001110140001c84030112082500039000070383c6130008100b515000305005030305128141da43c00f400410180820f81030b42c20300c0d1710009905d0074408500b0016030b80c01461103000342e05c1000202200c1e902c009d4001b01c1c9080d8260724560702e642c2c3c058102d0242c456003200400440a61445118400c02500601c0c1602c1007a6100c1851381e4848138050290703007149c041e0207812610080c10006552003810480d034400c007144c03050311a5a58840304042c510a07243c106451540012051004510342805403c0005104650501c00c000040c20800104c3c418941c808040c560f9942c40142000000e9041e40c01c2e100f08117901c0251842c050401d440a40700c1640c00c05101018400045058580031001e11038540c041c00325a0341100e01c800c140041c0d51005082004148404d21000c070000d131303030100112554802e030303a58405254841036028090040030580380880400c010b1042c8420f92840003640c12000c11440e144010301801c1c0c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 432615206 1250 432613956 432613981
    0x6040612020f1527010305010f050409020d05030f0409050105030c1c06062105100e10090305130b3c180a0608011701050903040306151211040c0219020108 68
    0x43d03910314000f0104181500c60f4580c0716070b22410004481207091004030f0707001101100c0c000d0050f8004041030290900540c10264820b0f4411071001e48854042c031800e40340c451964014814606051200003024050040c81f030003034500518045d4002d0444004400c0000c00d082620320780c03900600118a941c0b0300340040b40d0020340c0101000c851421820409890700411100c4d0701000b41c1c0c0c07074803546e0612441d1000e40c0c441c0090102c00703040030382492401d12450b5800303026901400d404006081c030120801c4410070004000421120349815510040e00112111084440804840026040485a8240d108018800c0c0302c24400280d4940e0741c40350300385170906180001503103608803403013601c041340950b001080b00341130f92030300740910000020b86014070b0b0903244110350303804445d00144401c000080d19504040da0840c007810003500c00740c0d191060742400c2b078404042940d942808080c65011030802d842006001005440940762142d0044107000300c02005c201c0080c10011244005410400d065 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 432616456 1250 432615206 432615229
    0x60b1e07140c0907020a050c010e060d0e070812040b0a0810080604060b090a0e07030212120a050d05100b092413170c0a0905070903021002060405010506040612020f 72
    0x10000e00418850312280359911001520341c14068012100800c24485c0001180040c0c1a88100200f0240310900d004407820500c204615401460130700000c01030384c44502172074207420840e40c0200942407402d0785047c0b6009150580d82449507013000180a10040c0008480040c0d00e5401d0000d9141c0340d01d080000c0010b420340c0038403083e005d51000d2104109064011611010084915842d41d44480c9007560071a030444111450a6001c10400c00050a000c001041c1e41440794051321100b910180d00c80d80c480c0d10503581e200000d540010725007480f6081d840340d40e81010b81281150003450030003a43e50314510134000114843c41c00070103441b003c9000304c030135403001685045c0810380720a41c0c5800b01d181c1301028004d0030301c0e0300115130120b040302a0020785c0f00f40c060001010510120b1516055034010b11004d81130030700f044075000b404009a102c2d100c0008200406600030030710351420b820030608480c03015040610071070170704004020b00601d0000400c1c40a404441c100301c0f1020308400203800e02e461 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 432617706 1250 432616456 432616463
    0x150801140316140406050f010509040e43060e0f0d020604090204080105011d06090417040b071b030809060c03130b030906070203090303040603050618010906050f0301060b1e07 77
    0x103010030f4200244407541407002d002c0d2003c2c0403aa44502c104815004060f81c0140040c100b48810500c40c503140c0c1046036001c9202c0b041c0d4241c0440032844288a4032110400000304203080c514a045501282c2c0818400e00f80c1c4017400d017000d0178070400034000d40c11401d40621038100080c0e0000c03260340e400c200c400e02c0c070b600812190381e4a5403800a0006508284290001c95181c8000060001707a05032585a0b02621403050340000e130b603441c0400022100240007a2680f5400c0e030086140d00700c490004002501001c2c15080d1980c0c054544420181d000c0e001c01c1a800000241c108006131110050f40c0d80717800111040c07610703802041051440c50190f0500e00540c103068503c00103c0410003c021401858910242d42031030381c0d0260103903920705c5100e00180d01541704000402140d4401d03800b1a40000c401000004040d21001c4040003d820a030001c0c00c0e1140d40320340801c21407520a0041d595600240c0003441094030749844083c0c0e5000714103070458001412600582d980c1912800c441e0b10561 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 432618956 1250 432617706 432617743
    0x240608060105061c1b0908010e060703020705031227150403030e03090a090606091a180f0414060103061703030c2a070302090c0415140c070e0906011508011403 70
    0xd20482c0c5c2c19203000030f80e450110702601d001140c0d1070018002c0c07012680003400100481d03220342030100e00a60100c44190341e00d002c00d002c1a01481c0c080b07003642e4061161440e445005999048100c454108c9020500c0100c4c3e11000c0c0100c01c00369008201988190075040006001c4940c0c113141d4114450321440c02c0e402046140080707030002d1294404003d441d8107076601d202d025150031020081c81c44180c2805800c680030712650380320b009030142002c41d008000d460401600300000116042c1c030f43c0541c0c1000081c801e8030400c551564144074100007480090744507204124148442902c82c840a003030419013010000703282c1c10381c1220800c28901d004450b00001c240346060f00440e4bc03039802d10b01007248103001540100d4001880f94061740d00b42c030000304140c000300402d00020340d44000640b415407500c000500801e1303e081828000c80c401421000c1029280b40381184609091030416004a564510303640c040c2200a0780c800f4049040d64a1441090442c05c030b1400046c0c50070044020311300b0001c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 432620206 1250 432618956 432618971
    0x1080a0204050a03080d0c0f0909200a080f09010c200708031309060b03040201050a05070c030b01080d090e0f04120c021e10030e100c11030403240608060105061c 71
    0x340c043c5c0104001d0304410350400460601ca00e080b038040c04040b070540005110b08000f0701510f409640802141c1c201441c1d4010001144510201150071400780e16020072007000030041c240010840450340b01c0e200030001c001001000310301402c205020b22040c850758215044840d43c0940030007243c1d01501c000d0084a489194001880d2030740b03c580e000b0038200714142070000554840c00d80940340901c0e0305031100c074241051044126066042503400303880f400410680000407c000300b945501030441c2d0400740410984129024002484d980d108a00104000d42005100b001c96211180c01c194404008a20344103400400c9070302100c00000a50700c03414040746900c1521242c000c509070700405441052111003103500c03d07011a22681030700c00c510782120340c0c074020003080c0d9400708900b07803801c1c00c0400d8035202c1c0602c00c40c078540164104450440c0c2c4600f500c420b290301d024504402d080362520a10200e400c01030074503201c6d50180304443c02050301090542e200701103590701010f40301c400d000820148 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 432621456 1250 432620206 432620213
    0x90f0603080721020a02010801180b0409120e0105040b16210f0305011e2907050a0c0b0f0405060f0f0d0515010c0816050307020901060206010e1003030c0201080a0204050a03 76
    0x2401c1580f0000411910490071080303441c00031030311243c10758058450360a1a0f00e8111014500d41c036004142d601c0c41c0d40e46004180d2590345100320400e4030b001e2006040d003c0d20880000c0c00e610640d804d22418410180b108000301031070355080316138200c42c003d1143c40c000060716200c0c46e082d0a1841c6160318401c51004902d03420381c402c00d203280100e155034050000381d0341c408405c801b2030b08a80c007460b506590390390141721111018095405000011103494030303410200400c0d08a03504800b40450704c0390840041001444031a40c0103002914030024035510b41946400260900c0c1300c5c901c642070065201003408940a010f0700c1c160b41040342d20380c213440e40d9035040c90105001050222007c01e155a40505621244c0d44190501e4001c20b41c4841c07030911345031184042522400c0c0d8681e00300c0301c07440f00f04450f000503214103802600030842d5800400c541c3d41081d00c0200225001808084101c0b0780326410008a43e000040e090310980a0038407060070b88419130400d0103072195070001d42d000400c074003001080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 432622706 1250 432621456 432621473
    0xb0d0219050d0b0907081f050d05100614011e030b0409050d140a02030702040b0a0305011d0f0109080403030c020d0602030c04090b03070e010b0a1106071115060a090f06030807 77
    0x40d108240b04003d0f070010300040026108007603c03500e00141030780703001884c0200c00c50035024628000003070409072180c1d200b0001e15601c0443c10101c41c0c1e40c10640e40f46001081c0ca02410002d0f11034001803004052100300000c240100c9800c0c00192a80c4441042c099140260310584c05054060000c2c000101d00703040082c0d9613020700a030480010034810084640074400e805551320b42280c1e901039403030180181c0130000641052185507600030802170000002032402d110791280a0209180d02c1060055802806e041c810309400721421a410501e10304002003160048609495060038194150b50950010841004480704001c00c0240b002062003031010a42c000303003046550104013404038040040526450309520320030048100c40c00c2e070040c0b256a0300c120107484010100d181802c2460280c0c14481d10741182545d0b08004120000302c05249060244007180c511010120501454240f0602180702054144248042c1555035a2220864007044e00081c0003140c0105800d5203039500d40c20b101d005c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 432623956 1250 432622706 432622717
    0x4080a12020c0907080c0705010f020d090c08032b020c0d020f0c150703030b1815090c070c060e18090d08090703031416050109050c090705130b0d021905 67
    0x580b2581c0d2034601d0900e03200e0744203031198070305a80e0040c3e15200e60b00d00360103076042200201e407695202c8003c001d00560a2014001c3c0e240c1c4004003152086450800d00c100201c2500214017a4200b0040403d102910352502c540e40c4521030503036500704504032840c1009002c1c0558074500ca002d54049411200d03800214001884c0d80c000684160320401070800c0315410a400742c504040304280320000100f4065440412031000c0504241701124107840c542581d40022a181c0e10b00500c444100143d605180038155448680e17a221549022003549a0340307845c0020380b0640003003211083c2005034a445040d924554001c2d00c503080714140c100019a00d4907803800b080180001000c5100068020b08000750407011a0b03010f0300d6080f881c0780c4030307880e050280d441500c2c0151601e101c062a500001e000344108240c00d4060009040e41c2d00c1c0c404104212100041d0007a000c010051188400001410401d10120350701e0603460380c2d5030301c203100304200a03001d0705e045100e2403107034524000b912541010041c031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 432625206 1250 432623956 432623993
    0x1b021c0f030f0f0e0a090b0402090a030609031b050604020405040302030405030706030e0606150d052d0403180501200a1704180204060801060503040212010c05070506010f0308071704080a 82
    0x841c00c1243d02c0308846400a50f41c24a0f401042607000704201d0703540f90721200c0c102401030005454500000d020440105241e032046800642da9041a400d142c1d000200c9003040c801c61054002140c10354031041d03031395080030340064403941d529004a010503000300122402804080d0541d0340240e6280c074058002d020003400205540107003c00075031240b80c0803048400344a00405c000b03081c0700b000d400741c0000b40f00040031440e001c68080c40360041802c1824400700f021591880e80300030f41c54140350041c0711014044000c041c00048440901c0340daa00f1000c4812040d0044803014404241c040405141c000c480c40041c25540e100f08103c1649070505000303000369030a112041400001401c01c0104074861403045500107501d403401401a14441c00c02903410600080114082402c3c0302525401c44000c00c00180118400040d800f080050030b000c3c8500501c40e40c4d815820461560311110b4440c452118010022400c8185403860031b8090410394000c2c11041080791f41032421407503c180b00c400c0c07404648 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 432626456 1250 432625206 432625217
    0x1e070e03150103081c0e150103110909030f070611030106020d09120302060c03060d0c08010b040614060406030b18091f0c090612090506100e071b021c0f030f 69
    0x104441008125440d0480fa800440c031480c2c1500008440d00307111072102c03885d81540c0c9030400401c080300104050b95043c03038150300c4980994510320300710a1b8041700c695114054004c540400c0716034100030083c1c941d90200440303015501c4001b481d003040100311301d8460030384990300030002103030055000407405190511034482c0c40c0703505c1d101d41024041e507007140c80003801a408100010010f0840001071034000002900300b160040c0d2640d200000041103400204203695600d54a04080c5864000c41000384075810381800000103580200d8101e119031700901081c15181c04541c5215212040382d40210304940110200504143d904103849420030340441c10484102c100d20700792007000d40309284440c0066101c0d40211031511505403080400500350031a91959103052501090781400381c2ea10403043e80141c00c603c0c0341003044100b1164405811182040b80f0035880c820004105278400c8052038048600b10054581c0c2ca030a00441034480b030005001900c4c842d451410944c00045040350600f1540b5032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 432627706 1250 432626456 432626473
    0xf2a03050c0c030703030c0c05010507020c2d0f0a030215040303120b031c02070b040f0302120105010501120207051f0e0706210e03090a06050406080c04120b1e070e03 73
    0x1e03040c0c0c600840d2281c1d0102d420030031a65000900a60101c1c3e0141c11a050004820340d59448403821588125001c00151704800c0c10084580b5044e0000707040c0c0c80f0706e4039000c41421281c02420100c00c1003928140d01551200a01c1c4040d5921000040000d55000707140142c01c00442d900c0122507000351000b100840d941c128803440c130601c0d13401902490741c0302030b0062500040042094140d22410010481540540407010a07000032000042025042500300460383c2403540c0705014104101150301c0140c0c1c0d240200600c5203a07031001800720311a040000c00358860710340d41001410041c2034010500715030342440b100c40f858006038014000c020502e0058990039036964205585e042e000c8500d94030300c00c0a0352544e400d8440b03e60300c80119030000a04582c06c200f04000480d1440d01c03160080382c00b0601c007103410031606501541030380d44940e404960904140c90405c42001c40e4140590090401d860040003550f91003048020060740c401d401071401480c2003e48014215604999a142c0a0f0090140303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 432628956 1250 432627706 432627721
    0x110a0e010306050f01230307030b010e12030f0a030209061812010b0102031c0b191e060c230105190e0c030d0e011806020706080f1003060f2a0305 64
    0x264401c0f00ca02801240305608158011181108805080d4154000c081c545803507084120b0b015600c26440c5842c0014000c0c40d09002520940c100c83c50148519043c5451503075040020050fa840c00898240d03854403103601c504260082c2c012046029000741000c1017001d003d6276241c0e43d01c3c52803c2c0c140c2d200030002a10fa4000ba00b039400003140680035078020451803038451000844030814000c4000000740b21a115000500901844c40041001c110358600034860f80c03074074101440c001941000041d581e6454800050480000342030041c1111403407120403a6145454441c401440e040d0070020441c41c0380c080b149240c2c00d082d000c4600760441c0f9005402030000e80c0014000001c90005009100800b001c00c0202d5424490307902440c100324452803a006154090508000605056000f030840e0703034242070004207550b03c01409290307400c030740c4010300451050840104058940004000c2180001c094400d0094040410042c0317041104010b4140380c001c031000007000c0b4100941e401c0c8000d488400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 432630206 1250 432628956 432628961
    0x3060108090316020f0f040906050402150c0a2415030c0501020c0a1206090507060c263a15090203010b0412050c120a0b01060203030705040e0c090301110a0e0103 71
    0x5464050810741250043c05807801c61400100305600509103150301d0703a00c2020806032101440c00700c034055100c0c002c2c0001c40c5084040d025000c040d000d051410714588807203c1d070b46c07141c0040c070103030440d410285044200b03107220f0080c820200c080b40c000d0010180c0440c61101c0c5140c0c600c002d0320425036040e4049160361020565182c910001010040c1702e03820b00c201d048030715081b090111002c542c1c0d0301911000800a01035000201466124841c01075814280a8a00131040c8504070b243d144d034003861244074282c4005d50f014820441340c0300038502d510403060400000c040c40d20f082054080a045550700d041500200b00040e2103179184180c6990f030350014000e070701080c029287c61300030034401444107031686624203001500400480341d01d0990b01011408d0984071004182d0560402400c6100744240f034809940184011b20042d85185072105000300680147d00895210807170b01d1000c00d51905070300050382c5046800800030085500c60a44c3c007000c95111111080c0030030111101d07100c945d806032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 432631456 1250 432630206 432630217
    0xa030308060307051005120621060a0605150301030816141e06012d0302100509090709260f06011205071a0a030908070c080f010f0902060d0b0604080604030203030601080903 76
    0x203403100e47c1009010300d425403203420000d100380e03080302c000c04485180b89600c0e05990b0b91446420040c14250802a9031001a5421500309500841d111080d20521100d90350403241101d401c5803180342c5900072107241c888174501c0e800000d00b541000841540c215100480c1020860110180c1c0c480c40f25400c05500b03031601030903ca035000c00309a403400070001240d40000b1100015014003150341c0f254495001507882d40e02070b0308040006402040401c2d05041041042d9001666810450758280ca02034813035050f002c440c60022040d280240c0c0d446110307801003024000d8401a8025a403071580c540c070810588010403003064403c0d209200000800502e502110311140c00d0202c900d070714156820701c09a0180c1412070046034a4002003040b00003081110007000b02600c2d50202612008140c80015825604d518a001c034000340380030702030780040e41c0c1c0300304a41c0d61814103900800c90381103543c000380b85030066504c80360841c0105c03000c00040560210041d84141c1c4262121201c81d2a00005150f41c0e0040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 432632706 1250 432631456 432631489
    0xf020a080709180507060e010908030c07050f1f0e04090f1109061008010605280c020406060f0e040b010201021204030908060f16030e12040e040618020a06110c0a03030806030705 78
    0x41170382404194460040310011860606104110380d030740720310452559100101107803042e0012081488640b44c142500d8a00d40d00844e0442c615050384171440d40f1945080c00e01c0014000709080d594295142da42010102c55000490401e08641c2c3d070403c440c0d000901e0400324440d9081d1800254145041d04036100240005e5071443d05030381c01e02d0415a0640d02251010345a40800503c41030b10520302c4141c00c5011700140e40d41ca00342440f82c410700054500c2030304540184120880300f8450b403076001c0c2c5520038100e801c031400314040c0315000041c0d0081c400c1d8040e220035480000104402c0c180c1240c2c07840c00320f455500c120342040c0e54a44404220344000d44401e020300041d00719168110313101e071700051140d00c03282e41130b21019811141c1e4161181c2c000da1003042201b00c1c09040200788440c51107034001e000c0b00c2d014102405a0b80782e00046540c00c09018180c140300c40d1b5a20100500b00410220141c4080600005d4040d034407400c0107001c002d01140c140f4803900c18201d011640781894528002c41015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 432633956 1250 432632706 432632713
    0x40201500421020a0b120a060b090607020f0a0e1504020a0516060e030307030c020c0a05011403090a0615050906150306100512040b1602010b0109030f0f020a0807091805 74
    0x101605030a80c82c10001c100c080381d0100340121000740e0b40300d44140c4d0050450200c5103a4884c4074250006403583c00070200c03c0c0d154580102040846040e408803280503900b1a0000c0e0b594400b4400608040081c007584c542100754080045007a583d245e00e01c0b80189c106282405981203514104020381c480c24004c0c10000340c00780401000c0000041801040700d219100106030500601140c3c0c0c5590000c8400c180080c1d2039200b29a0000c2c0c042c014844502c03402d0700c004814908210010701445502e605c0c07544948800400500d00c001b003030212441856001c0301c180003149106001c2160005180551071140c41d481000c0b460707903e400c0031081487d14180c1070311820b541d600810802c04409900741c09040c80030070008109499040d0188074444d0f44100c030074510303904069004454480c24061090300f0740e03141407107007941c0d83c0c1c2207440340040741d6000700700006481c101c0c6001c3d030050260036002500006204801b0480910100e180e5040c0c80382030404010f103403a900c0300d40546000800e0302070182e41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 432635206 1250 432633956 432633959
    0x304050a06090212120a030e01050c070215040909030323040b010308090d06110c01050f0108150c040902120105011b0c1701020f04080c0906100f080402015004 70
    0x80c1190880c101d0b2600060458207042000b01200707084c149180d6091042c01400180c0701c041c00d1301071156166440c10780300200704615014151000e07130b11449402a200e00d0020840d00c048902c001c08403405048250010301c00d4002c207107009400742c180b440304180803c944e40c658804820003690700307511442c0c1241d5900c0c034507460b50322907044075480850314940084441c666070300400c001c1d0003807103041403012103100d5440c00d00c420003c2c00c44601800a00c04042c3c040010080001c0024211080091140031600d1035118202681960b108603484441c5050020448000300320b60009101d0403102c00b81c85400000d81e0b4840c114060604c1ca140c000c241600c3c1c40014403218840400d007d1422480c07000062404410320358400d103a8215074080c0a03107034421001d080403810141d00b02e98010b2030907100c00d40f014540550180070000f8080303034203042001c4100000d0a40e8854899200c0d80c180160324401d050703070024207a46d03221300030f20b2004e21076101e2941428650f94401000300c181000302c91205081c10b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 432636456 1250 432635206 432635213
    0x2090a1404030c060209150c070512060f2502010e01050a02031b0d180c060314060d06050601020c0907021605060c0303010303140405090a02180910060e1f0905150304050a 75
    0x203200503003543d4850f0b0038080031b015a25010b1042c1c01c1903c49040403070300e840e080d44202c1e1500c01203400241c0604903203e4a500f0151000032a01d800861540200c0516135511f0303d8483c0c6145c42c03c90f0f01c46494038400340c1c2e10f56540c041d4070002900c25420004c1c4440d03960560300070160301c0b05171101c0000b1440104030030004407510000d1f1003c2c0c0c0d40c036440802c03c507103142e1445008014101c0107640d0468030250400025801d4411900c0d80780316480408414078080e000509a904059409003100d034079100000c3c0e4a07032003440078083d180e80040c04070049003003400000b50350300d048811030742c0303c2c140041c80402c0743d2a064040d12081c0502a004600e940c0c01c60703408841040c0c2d800400b0391044010b0001141c16520300e004a4403c0c40c448000580318010361140f0141d40381404c0c00580983c894100380422a0f200c594400300b41d032081d0420301002a161008034182d075101c2040c1c4985503294291081c0311540c08945c800031110100d0701250741842e041c0341403074548001d450051440c0d201e48030500c0003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 432637706 1250 432636456 432636467
    0x5010906050f09041a090109090308040809030102160302010e0714060304030509120703052a030a1212090b011a030702030a0309110303032a0906030606090301020903071202090a140403 81
    0x802e280c041c00c6092040300c00100c1c0030f440700600d5000280515940e42110b038144003010900401071a6403e1164030801c3c0c03400b5002d20000350016115550020300310800343c03425011108004030740c2e00c903407020b4505821f00a0082840041d40c140381c2c050007a00244210f154100c0180c804070050116103151165a010b45d540d0b40004940c42d0401d0034150740c40b0b0135900600160000354050380142c0500d1169034101d101d001400ba902e42004900b0940c4941c06417000900618450f40c014100d240c003014110060720b00e0050214003a00d040c2c1003142c80300801080c080942d049030001642c003c0402c0d0030442064050000315140401070344148003039100d0f0742c400d80240e1500c1b4040d68a4000c10022000443e0855008503683c400c6000100c01e9000302012800c12103c460301d210140301e04280e00c0c040047c405d80310281c0924440c00c40400d00010980d0294111241d201006040b2074200341c0d079404e142d0440011071400d9118250b00700015034025903901907240c07c2448480134201d80c4d13599036006d946 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 432638956 1250 432637706 432637717
    0x10f12020a030e0f1018050a0b0402060904060b070209090a02100804021c0b1902041406090a0f0f06110a0b010b0331021e030606120a051002070311070501090605 71
    0x805031601050450b545040c01140862610704000d0148035884042402c20786d2181011021494041c1c880b0703d001c62004948403482030381c0011400c002c6e0f1918000900540540d26a0a0344070f403500310001840d803004001400820b1080e20034034450307038a4024030307603c90801b100065000521304900201080c8200f0ba82a40079100130b089980900780d61087e0014042d02c4034048450f0b04484051201c0380aa9610070001002e60f007105529060800500c412502c0c180010306000740c00100700c4030f03440d030342e8802814050b10f0312a881c94440390341d8448800b0140398034800c47c004565100e144480d0224082454100305030803402d5031046910b40100c002442d4402048480845079544803030302c1f60305d501c2220381032115084c450098015058010440100491032101044902c0c0c104035403056200401c24580c40f49007110800214200c4000c3c1c5802d2000440c0d009249020380d1481c80415400b075400f600e150342c001d507141400c00285400d65542d8070b05074094980450210315081010a10a100612 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 432640206 1250 432638956 432638977
    0x90f150915060e181e070305030c06040318051c020d05010c021b01020f0c0d030507050307081309050601091e030b100503120a09090b0a0305030a0c0204050105010f1202 74
    0x260000864071010050107003050000c281c035481c0c41040110301114903120340c00440e0380f0702c0da13106003c049040c1ca65070b00c10b072400030780400c0b00c110740c4250041080c40a0402550804140c0c4d540e400b44440c080d0312441c04032811400304891700c42000a0100340d0303142a081d184080e12032031a00750300000100c100b204c0c06008990100e41ca0388144c000a40c02c0c002d08000f0f0010350020100c0c1c00304c0542010006007040c03e094115030007140100c17000c24001500100e201c4d000d03201c00e81c0d608440d040480e8580300390440982b00348030005068080002e8007009000318103a1a801404098841c0300140a55800382c3e5054002139001e0014400c020f0361810440400280b0740044440907a02d40e40d1180c81c400c11030b403e07120641c418034100b0150905000e48080d9501903249545040300030100580b08040d00e0103140300c920798505a29005494a070404005545c001003102d45072815058002e10210450400b00d00990420000080175405106001e54059458848c901e000f0742c96078503a4000e40001d541c0c40b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 432641456 1250 432640206 432640211
    0x309061b0609240c0e09250203120601030c08070e010e03010908030f09030721090e09030309010e0303010503070524031801230c13090608070302090a090f15 69
    0xa00051428482e01c00c14a208422034603645541040100381140d40c1c05000041c542880040c1c40c0c0c1c55440100704102c44800c449800481e12100c18112501078502020486480341d0461300340c10035000405014502110300b199406650740900440507544000401404608000f002c900003030302503c82004110411b14102811500c0000060b0070343c0e890040c20fa0703d0740304c00014080c001c51a43d041c00c0c0d010315124015494140d895139051f0380b1060040310b04101040801c1d1428180b481071007218011700d40c1001245c0141032610103a80c49038400c0d00c0e4419103600e4a09517900f00c003008820707030303040380d40047c003410000c0d1074034090100040021100c04011010052400c1000e0721000143d8042d580d0b042002e2015440ca030301c81401c4540c410030100e0405030703e00240c40d100c501c3e11046503016845815081e00c9601d906d11020800300c3c241c00500d0710f01e00f041e81c08200321307900040a40803680203c1f400103660311400c0781c01c4215070381e403040546030034050782d03c00000c1140451080162b05409500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 432642706 1250 432641456 432641507
    0xb090a02060f040501031508032718010608101a071b0602060714070b060409020f0409050d031508060103030f05040f09020d0e011a0910030c170f0a030906 68
    0x81c0c100e51004036a00302c54040800c0502113545e06100e104c0101c0031405030040f40713074100100035641e40211200781d0503410030012064031891040b2a4403501c508017500c40c0760110052005081496000d000b00000140311100181d20b203030140380d03c00708a840d860000781308045200c0b5010300c1980860404d5425031040c0c80012480301c50032600b40010000381c1d003e00a030b030821500007801412110041c4590b42d81c140800c00100d0b043d811030542040d01103400040503022840416144200c0c113800c154000d140c20283c034180710700410b0703495851110707550401402001940426440030703203001d00100390f40010014000a4040d04042c0400061401c0c1141482e5441e4465440d003502c030740001d0000394010074010100d1400780260b0240c42040d85c02401102d00d40e2200f52601c045101000f40304115900104984c800a03103c251b025640001000d00503e032502d104984504404040d8100d80c8903080c4c0314815001c000c200f91040640c0347d03440d4084549000411210103c0c001c01049000303082d55007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 432643956 1250 432642706 432642709
    0x2060301030c150504060816141303030305130b01171501081606050a02060f0604060b0a02011505011403130804151d040b010c060f0207080c1b061201030b090a02 71
    0x285008620400c6018103460405071083d06140296000c042800b02c2400240061a0401900c51788464545d01c0000c1e9005400022144101c1e0b41a0340c2d07101040003d400e0706002d408210003c2560300a4800b801a51210510074035000c0015801428000d1000014003004450300e441e1440942c4075011259400b50840c405002c0c3d44080e8800304150740031800c00c52228050a0300760004104500346181801d610100203512510000c14400205c3c9548000039240da403503034400e4024240c59080d540d02c0381d401e450003a0081c502170324091106041e4010000f182d6210301040348910f241c03c8c40040c103649075007264124010000c2c2c022540440140000b1903104444403c3d20b01c10300d915589d802125a8090800b458288008885402740d418a103180030300741d030000010040f01da4088400581440340400c411700034051558024501c5c60001100c2d01c171008000381000d160b8014103101c0035443c900004104c0148039400c1c0d040c0245076004010070114425035256a4403440200c2a0380040075181d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 432645206 1250 432643956 432643969
    0x150a0b0702040f05091605010201060b0a030c021e0a0b0a050132090f01051e030c100504030c0b0306181b2512030b040218090c0d02031014220e03040302 67
    0x1202c40b15035501031b010440c9101c0354031049000600c0d081c0000c00c803007418184400702d00e22810203c0014141c0f00c45003074503240d101f0403000d0031030040100200d6081503110b1045032140c0c00108241e5001452201040d500c8104d849203604039040082250101d440f90101901c40c50700c2d4400340c804442c005203c00100f52100c40f01035100c1c0303211220755146503045c58104102d4039607480c4094070780030b0701d4000d075140f0b918001440c003907907001100c0340510509030042c203c07413500c21500b0084c07000021080c006581141100554018401165403801c0324007449001000d54101301e035520707051030180c11000f80034400ba100400440524610309000361203580b0460a0318003150004440003400041100035059140c4584d040c0b43d0f034200c1d01036140541d100304400040d1013412020f84030f440400c0101d0308110205013140d811410054056440b881c10031100340c1061218450701c12140e01110341d0100d6031408001b03c131024003c220205480c4846085614018000320324500198881040084056078400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 432646456 1250 432645206 432645211
    0xa110c030304060917090f1210060902030402030d11030a050721020d0809071a182d06040501170402031e030304060b03030406090303030c02030d140609150a0b0702040f05 75
    0x80c0f4000c984241945001c0c1060361000220880f5030030180300c29189641c4019004104440888030980c01c000c0010310036040840700011041e8844c07401000080451203900034504c954001c400b42c44c0d078030411040c15aa0004000724048580d00204085000e543c06400900711181c01401c0032002130b8240201131080120012100c00942c0c006c41c0da0102c4160b00a82459200c155040a07125440c6004c51140c04180c01901d020699000420304a03e195000041222030401c018000d130703440714440e81f0f0190a460306c904000c480d0050740071002d4107408e000781140c00325041a9580512108000c0042810b040003900c100e925000c2d90380a2400c803103100c08170481c140780c2e44014698a00386840e201d403c0340c00b00d40545010703800a0000b042059008003460044a070035007000300b115403550204900307504c180003945804925007440d9601c90107001c904a4800e1201b0346d02003807544c8030807240e161208284206503501c091030903004d1199811100280c2013491001e840815000300c0540c40c0b00980702c08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 432647706 1250 432646456 432646463
    0x9030a05250b0a0203101401050d020d0213030c0f06020c010509010c020103090203060a1a121c1103030106051206040501180c030902041125020306040b070e0d0305040f0902120a110c030304 83
    0x11081c0b0184444c100c6e113450007010b824000d00220302c0e02e00006809806030201901c821a40854844ca40c100540c0490b415041d60000d081c1c041500c91402d000992401d001c0c4485140401c0740203e605400003440300b1740010142c40d203900304031030040112006114403408038105a00c0300100801624208030a80c010b03c5040700c0071a168111808004041b1145c85105120300e1090b068070646200c0843c00480e10b0600320b1580345c0700080e440303040d40c4030822804025498030001000107030306540440500411034020038414050b03140d01e07082005450080c041e0300c01c06041a46000c208401d503078050001031a03103003008190130800703030000380898009409012001e80300180010035100501d61812500304402d90700286c031202900402c0c1e9a81d4020030003000381144074082501e45015074102c4c888601d0080210b4140c0780a49001801c64002e84643d01031414a0503010402e40c0c0746009943c0440e2140c000d9141550300c1c00b6200c0040d100b102102c81e09802e0030400041050010b00003140b080c0d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 432648956 1250 432647706 432647711
    0x628050a1a03060103020a0509040813090b1c12030f06170a02010f0f08060609010507080c010f0c140f03180d0201290607030f11010603030806030609030a05250b0a 72
    0xc4001400d80c5800416901c0303842600040014030042e0348075450030040e540141c03140700b40780d0b480c3d140c640003038030600040102408000c82e001842602c1e9801c2912514015110705c0c055207014214100ea0055141006002600315a8030102c10362080d480000501101040401e1145c0d4494001e69007110802e100c468a41200e2800d03810340d40c02c13400e01020303400c06186c000303425241544000d003001006030a152180708000362400e0b95a204105661110303400000300d40d07680c0d80d8850340c1ca000300148605070305101d06009070150f10303501030025512400300c0309403140d1510001c0b8009a400e03510007010344030003041144450900c864200462001e030030450b00002059120107404400456881810078000044040030300c8064480da0700740d030780d0386030316081c80000c401c3c903140242d07114105c000800080350318001c1c0008c00e0541c040d240501500c01074090b19029103400c41400d4032842888403450104a0804c604081c1c0000241407810251256600901045150b030b244404078105a80722034440b40c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 432650206 1250 432648956 432648971
    0x5060f0d051911040c0f0c110a0330080601020c0609031504141209060a0c0c180212150a0303140d092d02012a020402040906080d08090628050a 63
    0x240745c800c801c500809420600240390003c42c00514079401524014020222040201c81c0c1c0d440380c002444c069682724548038068078007064480d135184120316464501c44072400301e129079540101c004901401069018040440940c400e0101d1075106007051074041c441c4603000c1e5140348102065500071442081024086498143c1281c500340c81c0002150780058200314080050340d98400f250324051550070030214210741c0c0d007460744101075a40d1200307006200c10385041080344101d5006100f0401000c0600243ea01c420520300e8203d140d80d140305802c07100ca840240082401080405480c41810700498909440c0719803031000d03600c101100305d030700300c190340c1880d464101c206d009400e621441200ea00110802c03500000c141c203828880c4c0c48000461006080c0c1021004600e6440700c41d0003610566403550340303217030100007000107200308030950084860001a0a2142d02400e0050509900920131611418081035044030501450008141089840700e0084441d0251600c50032500d0303000566079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 432651456 1250 432650206 432650209
    0x1203072003040b092419091404090303141602071d0c0705031b0a060c020309010c080a05090d150c1b1104091b0e090102042105030702030a050102040609050405060f0d051911 76
    0x1503140040304180510b06000384a4904080403a0140d210200d9000c1000e50160070150014080c4600e81c1005400400c108080c60021031440ed000c06c4040d821070b020956541180402c0c0d241401451030b004000300c01240300c00c1808800341c01c2d880d001d0401c0e43c0c5045440d402101e046081d1031000580b0f600907811a2051003400d00c81c280407140c2ca400518507048140300000d000c1e4414410090009402048403031441c0c0c4640f058500c00f0f1809040700c3c0c01c0d0000350500c070358200e0000841100003400c14410b12160342c0300704880841081d03005000f000c0039102d5030f207050202e002c900c1810780080d500ca03407150107c2c01110b040c512241a10710000c58140c1000c85c062070744080100300366440c1c0c0c01008200b01489034070b0407941d6010554800d0710410050751600304d0030342c4103c11010b5850f00c40c0e02203003402d02070194001c1044401e9615124420340d525024402079440032210700b42c2c0842c82171606400c5003010704a10700643e205c1c00665104410750386111360f100030340343e001303492070580030a0310b42c42ca = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 432652706 1250 432651456 432651487
    0x1e050a0b010309080712021e0708011506201f021e0c0a0308100b04063902040f0e01021630051b1203072003040b0924 52
    0x4000d02803a0502c5610002e48a0001900c42c10304c0c02812000e200800241540c4280318900113020b03001e0344d500307000b00221002c0c1c0e50f0310b4103070141c012a5460402900244216041d101040300d049031150803240c00320314861a403140c182c0c07111080c240a6141120081c08000d540000980c2900728010b841d0444000780b44c003c1c403005000318a018000704004079072074100251410200c2d030716250502d42c07542d8200700411040c000ea440030005403000305020030103a0b00f201c000c3c6d403c40c010203d000290301c94a1216103910740205190414140c00e806014007500302030f08041441104100003003106086046040c0c2203900c440b41d02c0c11009841c91104042101103120b40800024400080307c9881ca041c2c803480c050400300ca4401c042c0040003404140e1280c21103150b0f1440c98446068901c480701480440d61a503008444000c00100072414054081c0c01c50b00201c0c809202400040d07040c0303030030308040c01c90644c00b008105500612664610044d0402002140c8805125030180c50715040301c1c8080e08807 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 432653956 1250 432652706 432652721
    0x52b122d0c0c1e06020714070303180501050a0f0302162006030c030106080601120c030605150c1b040b1c02040e060702060a0b010e04150f0b0f19031e050a 68
    0x4000b06180c00710040b071065200c0f45411044440900079403205450b2081c024401c041000b0141000700004000c10310000c1750740070032203002ea219840c55074109051400000310074040e25000c144203103c1c001d107191003000c1c00020080541801480c1606854141021504490301103c0c0c81c030141103260844d400c4031440a4420b0701c155002415410070030716540d620f000500810040044910020324070760700c00c40074854610b4000c00c0c100701d0904001c9004000c2c04250041a0180281400394600d61101204840200c00341070080e1007104031100c1a403206520384160560301c0780c0c403281a2040e40d41c41002201c854000b41c0a41148810a44144000e0754055001703003040e900b0031010084250740101d2119804026200e00240d10410b0b080103944032030500c01420340003454410f2542501c9010411441665006018102c01c240c2c3d842140c00d0900ca003200909000d40e0078043c1d18201c640c14029184140c072141070215042c80c0c1281101c1c8000b82d04044541d02944078400e01c01c28030301070b104182c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 432655206 1250 432653956 432653981
    0x40b01080d0c080417070b0301030b06030601060503041a0c09063412030f020f03010b090306060906030a0b041524080102041a13150309052b122d 64
    0x781120702925400e0f140e0082e48990610201d803074028520722401481030303a000d40852405140c80e561a410030030142e6000302d070310500903c110f00007c180c65004400f070340c2c13040e980204082c2d444000c08400c091070250140c8090305c0000b052144900c00e0396070303001422842c210f00064000600011044540700c00317551400c0001d248560900d5000300b49071392205280004282404038000d03d0700d501c0c0d88024400e442e0380c001c80d48004800801c548009000600c8036030400c07412a41c02d0784a100c104004910260b407002c1c0c0c540c0c05280301c0340015000e03050751503106c0e020352031a031200520b14a0f48402ea6003001d01c030300001040241003c0300382c6a80c030302c0315002c1d00c1c441000314101420320000e603000001c81035a8400919000c2420f0201510400da28800391000d910002541c089443d8040c0140044a00445480c014440f81212070300044a02c403441050b200d00c1c0300380410340d11000307480c6000460480c004454443c040500b81c10304403035446018144003c051360300c0c0000f80d9088803c80c3c2d210348569 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 432656456 1250 432655206 432655217
    0x15030a02070c0e010e070f020a06060b03010501020d0327150e010605030610180e0102090d111c12030c12110324010f03150302090a0b0a060f0c03030903030b030303040b01080d 77
    0x140010000c005c5402e500806504205804801180041e8a45505220700074166814030201180d000450006141266000e80032100764609202e015402d50760007071800004c000703120000c0e220024102a692405602494011603484291680300b401d0b510505484201c50f9120103040055040400402c0d501615100a1002250601040c20800008070300c10094440d1291601c500f03900c401c1d41202e4000f1401041241881c400d46407140c4a803260320b109a101c0c004200c455000148011002d032031140d408600c40a4040b50210158000c00003084610200700301c036001c00b928880ca40c401c00190300b00000009440345059540396802014098101d009010140a02203440c2d800071803121801d001c1341008a41c4a0a6000403684401540e20107035001000c0c0c0240011244282c3c0f14120b201d0382582c23401c68290301c40200f40c070198003071803401002a406801c8200480e00c01d901008045100340b502094880c800d40000345541c0059070181c50f056001b5004002c47d25041007209070301074060401c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 432657706 1250 432656456 432656459
    0x150501030b0105060f030a05060a05090a0e0d03110403021507080705030c0c0a05221e091a07050a0c0602160b1501020106380c0304090b01020604020a031115030a02070c0e01 76
    0x1054410300024101f01c16044d22003000c52602e9940008480240c600541100c0b40d5151220250000d42200c002092180c0070348105601c60750710a00440218a001c09032880c6450726541c240060304484640d030103815042405184005800c01004040c603d006000468076441c6c0046040d0500104221040c41410400402c100d281c4520a1080050008a2441da00d0a420700340110281442ca0072615031104803070740c01c0001c60096401340f000305001c1c08048640004080814445c28000c0e100e60001c501d060105d1400c181c030880c845400c040c480d4202600313200440703003404010041c0704400c59450500390100800004a9280e00013070344800d1001f48407441c03074500c007102c042c00440d082107170078405500640c03c80032411032400d04074010108203a6841120700c5105031a5040790041190550408510040c550300c0007800b03c1c001c94000309549000c40c519a10000060102001e543c3c0042c0d00110454181c159030001c0c44c0f20301520b100160355a0700301d00d000400521590003040c50312141000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 432658956 1250 432657706 432657727
    0x260610030b060603090a02060c1f02031e07020705090424090b01120c0f0b0319060b0301090903030b0405040809030c03031c05060a0e0103080a030c030216080d09150501030b010506 79
    0xc1c0181c10100c19699a5900c1d214040c069060000c40d5134069084080040c0c4a00070002c0002c1e40041c8611041c4240ca0003501c2100750000d0b0312040d03c440302542c1411007140002e11a11190f00e40007600307401229469503549001c00d800340c9c002c032000e4552480c0410104c00d14503204040420590355000100041c80070307940e800d50340c550103000c3d078440084003060b0201000212a0058046c245060390b4a507202c0c2d441125902075401294551000741050b41c002d401f02c2c805015001c2500e500c800030a007180e0074040990010410700b0340a0b000c040c4c491b001444241c48030b10a9500a0f401803100f240c1e0b808846080c140750401881940380070f5401000210a80f100000580b1100c0b088002d01040e1074880c0400103003401e030035811a230101a9020000000c00900300024000c9003241d85041c409010707000010742c01c034003d0300b500344404282814244002000c10000349400c3c54a81d10006100300e50f501c0301d41d02155036462800301103640300c0040c000d0002e2a02018010401115001e1500740f1004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 432660206 1250 432658956 432658973
    0x30503061c12120b06030c07021503070e01080604021b0133030602070809030d050a0e010e010c0204050a18050a05010b0a06270b0705030306010e0a06090b0903030426061003 76
    0xc0440c00700308030f10300240704071805030b04140c0010f01d004000d6034403401d147c80300400316803158808034400c020720220040700c24051004d0364420400c80d1618414004000f00545004030010149903200b5400c02c01900d28842d0b540000104541180c000156058200b2844d0543c01401c01d0000d180a8109410158401142c5c4080f080d254009005611100c1c18a0428400d004940550b5410300588000010b080d1340040070f0150404c03503030350f8a0142040d48005440f600b108003a460300242204c1512805402d168108581042c840309000031011000b9078507a16190705503c045845402945005090180074013614074040d1048552501e00d500d4164040c1c070b100400c80007076402008074107940c0f40c5400c1c165448c0c4020000320b55130584d103d81c01e2502135146c1d4021517400b804986084008049820b0a100c201c040d1502e50301c4041045080c041c0b000034a4004d0301415a042c801000082601030000d9841d0103a2030001d4240b4400401a00616040c840001c1003242d951140c108200042401300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 432661456 1250 432660206 432660233
    0x210030204141201090b0906041104140601110c09090330040f0611070609020405070e1012060f090617060415050402010c0228331b030503061c 63
    0x88805003e103038081071005016003000354026007859188800c008001c070010031540d1081d407207004140350304210030041004940350480030300e00c8840048005603247d409884081e18200d940380407140c1c420203420000d0740c62101100c4006650b0008500c1d401400d02c160001d4030f0100b0800301d000070a0001103110003221000074000b8101c809401002c205200c410390002ca1311103440b03030b8103540d52611070400341c01400352007104034000c0d8905400148007911989618002140080042c8071400c0442030459840b0742c000b5100c3c3d0700320fa4900300010481c4520440d400108032030900822051714001f1700410020096a1b005035075040101000006490100201800b00001c0c50000d00c036111400100d9004110f034400a405c0030b998070b40c0080c0203014407094800101c18103030f20b80ca001d0f1210b4450340250600c3e80044100c6c0b1190080074041c560114841c02ea60540f442c0c1107800d0440c509240780821181c16064011030400003e00c107082c108420fa4076800c4032014421200c42c4026a601c22107004503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 432662706 1250 432661456 432661459
    0x20406120501080a080f07050102040f0518070f080c0f0c010e15100612060e070e151e0a051e091008044103030108010501090e0d11031312021003020414 67
    0x4c042c06d031400d41c01c01317403030201750020021510749032100300450707155640c0d014142c42214640341007014140035002d600d12490f105e0f581d40310342500303510095404500207005101340d50000c0c44030305003061884014006400e000800802c580944030310407810000c06200c0390010100440c104640a414034510f04200d407514601100405a0051107600900090b00a15010000d000138000c02c998400141812408112024001d00d50020703980d01061140002c040c0d0000310b902164891407505102403d10342290f428518a000c10249280203050620081d20390903030030108032581203080c10781010304260482d0178a90b202d030408e0b85075901c0288165000841240404000501121241403580304541c6241c4502e601401c00a0840c0c0c4c494009000d103507007640c60040001290300e1640114064203120101400b11400000d0007241d82d0442d090b1240618802040250040c4c0c03a0b811144004003402e511800d602a01072040050880301c0303071824005c050040c0400c1c040500ca030800074480c0b410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 432663956 1250 432662706 432662723
    0x110a030f080f130608040b07050a02101a09070c05010501080703080f0307020a210e090c070206130e0a0504150510090917030403080115091409180a0303020406120501080a 75
    0x10b150740c401e04a80300d0340e10405084a410f000019203e40c200904500803441749108015580d60040100c415025000280f0016072110603481c4003206030798003c8000707070050710806002c01c80407000700303142c82d1041c1e900c3c00001d80c0e00716038442404001c0c82031070701405488000d41806490340d124030b4210300502c40e0301c4182507000008260300c0f80c002c00caa8142198040304042c4c0144040c4da14590b480c44248044000c030350206402001443c0c40e40ca00d038070071804100040d091280c03503000c1c003070150021001651081d504240c041040c3c0e00300c02c606485040420320214140c03400d131614851000d02d09003100071450800d0f042c8000364080d080d1311000d41e502d000e4002000620b9040004402020081d804c00900e00001400281907000070494180c2e07019402c200582e000e80d0310b0884400c08284a405c05c003240403525000d2624002c0d4101d0341101c1c90340142c4003d1a510148a070401c0350000c000c5010036400074003003140707c1d0840c070807408040d0300030820485907140141040e100c10052070010203864 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 432665206 1250 432663956 432663967
    0x70305090f03100b04180b072003130f09090b1812071202010509060906010b090105071211010b0a0b1209150403080609060d03021509030c0d0804110a030f08 69
    0xc0703a16414010405009040b00e41036844014000003d0644c1118207020700e003050000303515200b012940d4aa0141d00191910895540d0703041210f00808003942d80840c54025100c0c200100300400c090a00690f1402605007101d04d8980248621180c5a200e03d00e0181090609004507243c2844564030403840119040b401811200d8030381410654905011b0901c4089107030740a010760481c8100400296400030402074480615981e45c81d80202d0f240081640100014002050308401030700684c0e006041c070f0b505104c29596508a02c050013160f0301c00003564000d078501204000d00525010760407d84070242130a0401c0c001c84000d108000c501e603011131000b400f2030b41c801c6041040250b0070000c0841500e1604040c03030014070241d810f444444c8250601d401103051450410764909609605400070070000c03260b94009862903800401030f040500003480000e8109900748413690340e880d411380c0d03488024600b40c94206d580d038006545103402a01802028800079051009111000d81c1013000c054848 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 432666456 1250 432665206 432665209
    0x1051015211401030c080a170901090e04080316030e0c090c0d02030f090105070203031302220218010809030906160c03050a030e01020c09040209280e03040501140301030807030509 79
    0x10005509098416494107010142c01040c2861007030589100d0450100c40c9551011029a100203101c4060070050809908003407010b500b2000300302d40101030400104043d500d101058028100311400d4a031204008200032411040e0981890300c51040d08081141002c0a82d075a6601c0e00c1c19901907020304602c1000c144031042c036805030703000580340b4001507540c0e00d0310b034030425121101514000c41c030b5824103011400150010069912400d0a09001c015070f402d240c080140d480c17946032025444202c40c40c41d03148103014030b000909000707040e00c49440c00950fa580004041e01c0c80103182026030740050001d441590f1f9a10120356401c04968124401c600640c18401c0003280701c0e600c000c4c6980302ea2210300041540140000400075400d8003901ca2503004172050180000040740e000750701142e01c100146940c0280324011044070895090024444010003401c3c003100c0c500780c40303914180d2000c1410021503900040305402211596001c0303065502d10f80c1d591000d0b018251b0000d0502c9030115018145 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 432667706 1250 432666456 432666497
    0x70503010b0c1c050c0712020d020906011106090106050109050616030806030f0114010f0e100501080a020c01090b06090705040f090911030a0b0f060a12080315100e010201051015 78
    0x141d0300460401004101c1e144044c0c000d9000a4034105103008a00d40095480300d1494080100e5401900002d1940b00d10ba0800803041d1004003050706210400a00549104041251302c0c460302c0c044000041c881d0800340054005000f552003548100000c0055000c41c0c904003031084502c90349410301040e15158080000c1c02c0400c0c00f950703110290320303000650305460010001c090490700c0d6295000c0a16486032541c0b12040011102d01c0c6444400d80c00800040d44941041c641c030501c610401820b054510683c4bd0079a26071a81c15251030300080103020070f40c5080c000c01030300030791241401450680340450380079804c0700601c24144420755900100c0140482103c15440c889030003019600750018900e40418085c0c41070b10004404e01c20440054510b00703010040c14150f49242d003000b41900060303070710405154070003804080800515008141035455040101401e0301c1c4d25107850303002c2e000d181d000a0850740001c282e840c2071540c0c00e50420540300e83d1044109920040d1801d1400000031200d00e105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 432668956 1250 432667706 432667723
    0x504060608072309091213141c02120712060911090f15060f0d0e011d19020a090507050c010c02011505090a09050607110111040602030a11070e0a140601020105070503010b0c 76
    0x1005003002a0841c0b041d0140100c1c801a10148c0c12030700d002d029403005002c440c0080d0600d41600e54103460040000d0701d008601544ca13441c14804881c032141c0c4540d0341e02007102c3c400c001100c01c540c65810bc00c0802440da10f40b44945441502c180b4600c0c5411000d01c014a80c01401402122070000e102c60590307240c00f8200c0700780418a040c040c1d5a03003914212031000380280129840c40e54038140c1030410040c42510000d908042c0c105c01452800f0000c00146400861417104983c41060610005000c1005000c5c2034881c06454072001d4480c8100d200e07150030b50710000040d40c04c5900d0014069405c1120f220380800355201913600c082c01c0e41c1c8400340300c00109172081c40036210340315850410402551050850208005240017805000201d6441020b01d00443c050b10000d604144907080c001445070007100c440d01c8071041200e81070b07541d511600c441c0101c140c07000d009480d11000304100c4040c1d0b0302c880c1500010284020000c600e0250002043c600043c0281034140031300185244c10301100304143d11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 432670206 1250 432668956 432668983
    0xa030e06070c23041e0c0c02010504090b060706090302030901020d03150608060f04090b150a0e01090507170408031803031302010f0207030c1d16050702041806050406060807230909 79
    0x503602c00c42142090314041e0f030546441c03d41040b01b585a07041c40342915042c800d40c1a1116030501b4106082d1030040c1070b480c96107a07040401484200081215802810b84a6009401659451601000090520300e44070400c81c14107050240044000d40080110000c80780707a031406520380d49620bc000740d6440c03480b00350980c0c01810003003004184401c401c50103000e03004c0341c120701c44440994403c0c020343c081c0074412903d00d0f6140b1401001121461b40081e40c0c01451b62a2800c01c4018200c0a40c0380f901040e0323000c0e103030380e070011081000d14032580c0c04054184200c50000e5042d880c01c82288172401c4203010000341040207190580000b41d00801801c0c01655200c00b07000b210365100e070f48a1119402c480105000743c40a000401ea102c6c4001e034604c004600e040d03452501d040d449400380000f0b80454604c40210392030012548000c80c02c030b446218001c030f100c0c1c0404104149012000f03490a450b0341c22010010784682d511b80c0c0101008461981590340c142d0b5204040d40e56a2907407070420140d4044a0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 432671456 1250 432670206 432670211
    0x5090609190602070510090314070b1801030b0a03080d1d0a14120720060f0d0c1d0a0501120b04140406050f010b1b1006080a030e06070c2304 62
    0x60207481115a65030302501c2c19542207442065035401009041e036500855100483c1403004240040f82c004103490710800303a104200d071a99135032803640d03c00690003044881320943d940c144407010396900d405003d10700c181c100e454040d50740c08c5443d041c1c103038070401c0111700982c1e44c0c2d241c01981040e1a8200789003c88005c0702500c0d41210b150400c26809080b81400d42554010101c031986403620075401c2d2040144c00590003030402499544000820450304515503001205000341e000703010b5030300020544100309003404104e220201d24003420500e03074002404884440e104182c1000d442d01c031a07400464034246001c42c0c0080b40e88180600800b98000c0303a513001801d00c0041050300d0103403d0090b0085d44144020092640c442d80d001c04199028007030700000e20002c002380340032501c4117020710300d0554138001581c540035080d800c0d000c22104a82c0c01820b0a230454100041495048000b450f6580401d0314214941980c50744d608002c04818090388890400c00b0451084941b60740050000080300500704 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 432672706 1250 432671456 432671479
    0xa0c0c02150a180305060606030411030d0e030c12030a0f0c020607060b120706050304080703050c010e16080303093304151d0a02090a0e070f0614030702070605090609 73
    0x341c0d070b944607000b00404960311204401c044500b80040b981201e0b001405082903448410822480da400a441070b500c4003584014019203584c1800100c0005000c0c0e01c070a4210b44042c0305246c1003025015030580700c0c0511340d041160301e1001004844000000d4540b0710250b2242c98400c0d1100f49040002a42100b00414550100821584a11504c0104880136030340000b00358545680c0c0e241e00c0c05110700145d014008600007075083e10282c580c092290400070b082c005144000360845181c032451b2030442c2c0c003403150f00c0141096610000e001d072001d0300166241d07150a80c03a0603039440b420368104001da441d58482c0c0c17500e50105027030742c08003003560128142d050070030f0b0405441d501d94402c480c0f086c0c1490708840900c24402c10142d940340c204503c01801c24044076400f000100c100c024840c2c50201e8944505080b010018810b80c0060005102c01c20406410410001d1002e418080320840220b0304005100b0903079000120207044407180e00d0300716521340c900341c0850300d01e008122001d601301503001070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 432673956 1250 432672706 432672739
    0x40e04080c0105091f022b09020415030201082e0e07090f0612111605010911010806151c091406090303061e0f060f0d230a0c0c02 57
    0x7814036003080c000a00c956100c4040031601ea800025030407040320500c502e0340309100c006402808050301082058641543c01c140e40c0001204240448031800740d40e031440d441140340911500494401050100c190305041d5070001e0803107031002e020100c144a07403284086c010600048460740f21745022403071b642e91035503c0306491410702c02a105440401c0c603090300030030100310080504089070a940d40b0303003140c28070a005c001c000340700700f8040614500040206029036603903c83c0902115205000024005a4600740701680d0702c26258043d0410036484c0c188400c40c0d80320036000049021110307034183d698418902c003588407850484440180d03070401541c0401c1c0701101203568912112202550150f554507001c0549130700c01244e02d15481101280344415944420300760700c103400350140c580404c81409500080c03113904a101c03c0144200c001506d015001010b000303004c42e59a500640b0303507600e4641d00d00070000e00001080c1d80c2d01c0c16603408110803820700c620b0f030a0780500d8015218900041c4483c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 432675206 1250 432673956 432673973
    0x10809010b0d0302072c0a02071703150405060312040515090a0314060702061014030115030804050a06080f040305070f020d0503030114030a0f080c030409180b0105010305040c03021005040e04 84
    0x1290b0f4501d52040480e45514210791040d02a4000b440091840c0c07a580c0c07021f000000750080c3d40c05640780315052040040041041000318010040100e0300208644c8110800054901c004d140c9406500130380c0e598071840c860b507825201503450840384000b8000281200e40c07028018040380380c1d800942e0803070000a01030440f101c0604c41e01e012050341c20551302c00e0b40c1640e40d08019038801880c9900500100045000307810000d910000040c0041080d101d51005828041a150800d0341c144000080421461500031615001840d01d4148038016181c420b90603911120024000760500c41c0c0000c1460810000c81409452260700414403003190b030441c10629640d4000f40101e06414075401a130000c54a4002101007240d030f4020800c004840d0309940e6428030780c010360381d5502d640c44140030106040302c0c103000315110210070318076a1811010138280300f98070102c10b0b48540c3c1814540000c1c003010842c035a40920a581d0142d1701e410a40703400d054101d03850f100b50342c000b0b0410003040d82400100034080c3e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 432676456 1250 432675206 432675209
    0x220606060c1110080609060604240201060f0b03010b07060902040c020a200d14030405092a0307120902060c030a170f0906040b0919030206040201020d03020315010809010b0d030207 79
    0x42ca4403454550300741c0c09001003008001008800320726140700203591898005c841c50307809007010340006d08095590511041c41c05080d21038004681d581c10b0300c5502180d0921814005047c000b811120040c580610b010341880b041c02808004400010048140000d0f034008900751a8050702c1008402890403000392115000f00c0c040721105004208091103100d01c14208091804c01002e80c3d03c103440c1a40c441210005201070301020380414840003840f07030348446841d8480c6100070a820703982102d0055138408141d960070a0300d4203c0c020320a0024046e03110340750103c484500580014100454000030300140280108514544000200410f850350700450751841101ca0235103009036034441304035100700083c0480300b05810340d1190b80041c010482c03520440e5001100f0005135a402206c024442040a0440105801582c0207405120442d60704009840128038103140460943c1040b030045048000c0400245041148100c04960916021b6001c03844001e40200b0800707a40240c0c2c98080d484001c00d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 432677706 1250 432676456 432676463
    0x803070909061a13050301110703030f1517071a0c06060a0605030c03130b04032a020102070603090204021308061009090b220b07030605190b03220606060c 68
    0x5000008081d040ca01400040c0e4810b44440d03c00b15080b621410f40030340205000c4c40c41c0100581c0c0000d04e41c1c03420311828201544141e403445e6070307040c98203000d0207440076401708a0100d4a4600448006100d0349035000a442401207102d07401c1440e42145483c000380e680224003d2841403000c0e10303103c1c00400c010084442101e007591540d6464100300700500000d0700ca0600420010400920007840d4000119032144913000c25802c00300c3c0c0c9440318682214211400c40124070007042c0a84400003004080c040c505201404001c7d0581e07550000b9102c0480e84078540626882d480560308540c1d40d50107440d490002581482c810550340e04403030345c0c0e40505485a01c410001818042040b1846004550080d500a801140b440e16082c105c443c00c4601120844504080e1080240000c1c424019080c020802d40e074011540710b0404013040360580e00d1551110548900410030840781a109060325400484910088200e0f40050031b0171740b034000c180400a1603a4540b1001007041074000c03540e020070500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 432678956 1250 432677706 432677717
    0x20f0607080108070b160809060c010204091d011e1d10140708040c0b1b0615030c0d051b0307051807030b010503090c0f040b0301020406111002190309050109020d080307 74
    0xa440030354070f0742d51086d000f14090408038048101c021400203001404076081c06488586030000d40327054282246c0154112040c00c6032680c51510742440d038080d9170b001c403101a40007081011441c00c45d006000e82426a141d4955480300403c010004030226610b07101d021420035900f1114900401d030000b011548140946052004042512144a44c00051299510400340c0d0441d40c246a51410a43c000403280e610084800c140a13000d4202440f5603802003164800c1604e0b5100c1c00350030507040044040110340689a0340e09504007041d40080c1400314140c10600d0121300c0703280000440d0a240c03e40d041550030940d42c92401c842c002c142c4581350f100710f845981c10040300400701e004540310b01c0181c4049072194400c0440c0180c81c038007050b0b50f103800d02006000080e4907504901290030790300b00d0707030004000c190181240d140e2600184004014200303080011840d00b41102442c01c107088007101a101010754a90b02e1004001302503001c0c241c029002080c00120211910300070100d680200d0b1349000080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 432680206 1250 432678956 432678959
    0x4180b01150305130f020f0a0308030a0605040e0a020906040b0913060b03011b11010f1811060708340803060118180b010918090b07171501020f060708010807 69
    0x610038800c49000c3e10f80300d00031081d292813548421603280303d940e800303980c0b05c0a44114030b151030b5250700308240150700c680c4915450f440c00c00c4440c41100c4140d88124052801e103900e44601e00000309105064590480e5403e52940714400420020310300c0d4092107800a80c51010301480210b0000b8102019121300300612140428909050988008803081c050102d81030400318065401907421b20403000c1c10400000301c070540604140140c1d10102021918600c0c50b5a03071006003c01c188404114200a65101c0d00d040c140307070703100e01d824851840b12a030000e0458a410010104142818000c981d01c511042d0400c11035040a000c00d51007901c9990100318401c0100f40c180540000034003c07601c2c0c00070515840f01002c3c841601501c0e00a06483c104400000c02240b00342440034000d150100b44a0005407044c0685030818108501070100d40c113014100948a8a050092001320390000c1d035080541c15842c1c007600142c1c80e0000e0368503040040d00541d001c000246910585060403108208110341c2c425 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 432681456 1250 432680206 432680249
    0x200f1207050f07030f0f11030d03020c071d0414070e10230d0b090a15050a0b01050f0306210f0c01080615090415050a06021006051c060b04180b01 64
    0x18943d5110003420903030008820b4000c29682e04c1c0c0d41c030640d809040003203201c0400400103400c1454010811002c00d82c040b030401d444100810100740905110364203100710010120200c6103001e00100028070014195040c24038101c0c007441040024040001451624101030140030810515030051410000e00401841440002181c24440f002c002804c0da37071a820054031411078402000305108400d1180402e032070006500c804600c040c0c01303282100051f850803c41414815101e04040c1c85040180612404040644500450790000300844003852000c500344035050b03c0340403452004509000726121000410008900080c02d041d090b6180c8100381d03109020420000c6108a40c1c0800d03460611003050345040c41da0060038249042401b00700219903a10001f0207041180d0010300c0180c02890410000b5031a50041001502080360314070064503000201e40c1e0043c40c0c96a0107031202d5110b984505054849500ca4105624602030800d0050303024204150085800e20a000505130184030340d4001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 432682706 1250 432681456 432681463
    0xf05060405040b060d0314120a060b25110402030a0f05090f0307062a1d030a0215030613050a02040e09061005060a030e1605041b200f1207050f 63
    0x8075403110f141c0c0c101d5100c08040c0070140b1100f460032424400890311540d012020100a0462141500b402d0000c03460a421040140c40c2130fa03000e0200310b00c0a000e9503010040318410003405908109900360321100c40c0c00e00e485049480a00c03550020b2000050052052680e04501d0b02c07000111014002078407500c0c40c0569401000400c0401c0c0c0c0c00a108000002d81641c0146038580729010081d40300303c40d540d0111241601500c1d480020444000c0b502c2c000b4140034240c5280c61500700c000d0613281880e500415410a81c0303a030808210900080012015503900c1143e41d0381d034030070810800c2240f03040c03240080258407900442541d440c80500103400d1603400a02d2074820682440182d001a01c0c003014000709400c800011414503032541b140c0701400000b00143c2200c1c0c030805407488000c174500b409200c100d609051503100704003014105072000700e8100c003100814800c580340d89204e0581e1202c4050504020b400c0900040c020f86411094814050300a04070701030245040d07801c1c80c600f042d01e287d40c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 432683956 1250 432682706 432682711
    0x911100f2105012c010528030501050a060806070c03020a080a031d0d03060f0b12060d0f030e150c0606010503070201291c0f080f0417060a060b040605090f0a0302060a030f05060405 79
    0x20300c100c40385081f0401024902d40c401c903150307901107102801342d1240e9845080d00c00c125650340c03125503200010030112004008458100800d8205180780e00145d44000f0b4803140840380242881100003422485a03209502841c0d90461045000207044c104d52069502d500c41c104600c03000905281003c540610810b0b00c8200711410740c040b0f0707407504000e625200098640184416405010056104017103294100b0072032106201eaa114090b4400001c00c02a4980f0a440b0284241605121030007104a0000e5026082202400e000b9220760382c10804902600409064842250b8a90820f8a0398800000c0c1c125174040220742502002c14a20103c080b81d105140c0080c2c20b128000003980003042c0d1140050407104020802c181ca030a44036a070051072520b40031484400741d4403030360800844654520035100644040c0710440e203020301c2d09400604902407031101e41d10958022484420070790b00c11080200440d400f03400c2c01c0c0c40e501c070200e02900400113031001c5070203907041c00c00141d21403400340710701c51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 432685206 1250 432683956 432683959
    0x110d02220c02120414131e0f051e060d150213050a0611190f12050307080c030628030b0702030301030c050d0312051306050a0911100f2105012c0105 65
    0x4865030302010070403000030361000311700482d68a140c40030b9001c7d00f1949240219075a170a012440607000000841240d40003802a5035800c540e102d08510344503807465141e0442800c444820154249040181c00f01c0002040446454400510466204422040103040b1756044a01035960f6a54180989400c4441c90310515075405c46440c1c604111022039649196a010b050f0140c50391990356900c0302040e01d1011140c1c0802e02c040100030489600126259100b040201400d095081040201c0e004c0c0554000040d0a0340400c000031024418011240c07009540000e112100c0e4108414003039100d60083c0070a541c041401c040100c0c85040440d801c11080b076140d900c1600300300c001d02c4224001c04010303240c0701d403120000901c00c0114201c0d028560045a01d440002864401441d200206c40601d05010b4020026260fa801401d9008040c002030b814842c10161864039025441118a0010400c12345940f0326141c0003150081d40003030301076102011024070300c080383d00008420341c080f0000d21419 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 432686456 1250 432685206 432685229
    0x1803081e0403110f01111218071205032203050d02060405061b0c06010620070b030f041b0f030605070e0306060f01050403060911030c0a03110d02220c021204 69
    0x14002840b41c262038010f00510016200140707a010b610609684440c130621003103410110f0036201c4c0110f42121181c0118200403910726690b4448034850711290765100340350f258881700c00b024040c404103100312090400a04410244504201d184003104419400152090b2040b007002805540c00024801e00890304013008103125612071000c141c85881000400c01c0700710051240200e100800c2140c28041c1c0740d0303611307078481c46203407910140514510112544080c1e4825081080400d0318102183d40004141c190400940e44505080c40100b1054030b92002d20810200c00040500c4020301c0d04082e03a105100c20322054480460449110340c400140c43e500d40c0143c00440c286140c1820403403401c000c10b0401908080d40d0b611503100f1201c10a0060b1211230a10144800e00c0c80c051001c00178402040764401a80c60441e200c103104104401c8803540203030170603203880d8195504c0411041642d1803d01b2901b958030981140c00015000c400807090142c800c0b202031803040c80412007a202601e485400c035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 432687706 1250 432686456 432686461
    0xd06090e1e0a0f080415021c050405150a09080a1110080601020c0906010207080f0109020a0605031b070609060e030a0201150b09060f0c010204030c0e01090903080a09151803081e 78
    0x107882c204018000200d440b41410000086c1088011504003c5813440b50013610052000c4280e9010240c0703440001001c00608020a000b1036440c0340c00b200200c050b14103101d44035000c3c1c950956986e104d54000784000c0c0302c2d920504040000e88010030042e21003d5441c40c0e050800c54200b170301d04550a484036405030b084103c3c011591b00b03080261560140051040302c42c100d43d90707980c890410540c40c07081c82003030351166289003d5003010360404004142a240c420719500d0f02e60340604100c8610110010103490005200c0c040c414030342c2001c560b19420804c1000480d816040c030741e641b40c1c00319500344055404c0c07410407621035111030900401c95600709003230317858401c2000400c0700e1a03018a181000710700b4117001503c4940c200b4805000603503c21904078003482d0814540c5425414140e00150805040621510010707500050650304a0f400c600301081841d460703d482000c101603030103600301c041d1414a01e103044045651202c50400c1c041d031640c0c100382d02c600f031120101480603410f0800c82c1c0c0044d0702 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 432688956 1250 432687706 432687713
    0x605091509040501141512030c0c09040512040e0403030e0105010b03070c080403061a010207082107021f0e150301030f38010f09021c020f0d06090e1e0a 67
    0x1c1c2961040c810380c000038a00b071400b46900310486094501d541d9a803543e402c0e00185040c80c0304402d540c0c2e281c1d10019800c20340d102d01e090f03646a0b40240a5402a1604804901045401c02010b001000d03c10140c6445503151b40d89803c40f0b079000c0701c1c1540024104a124002e0300c03c1881490b041c0c68901c0f01441c074695031510107441c440d0741c0f00c00c215204001007100101003070341881480c903207075040c08168810801002c00240303080c50075006000141c00044103030031000304111503d000c000515240c1500c514039030002850320840d682d1840b1441032685192410304c6e511040e498101d80040b1507030024202d5004a01440b80000d00005206944034400ea4001c58401c42c12060103510b107540f5424104092685650f21148441000c0102d1250b1401402076903021070403000a41070b21801142040026810001e05603c200b03080e405481d0300082c000c403504035800c2100c002081c0c4050074003050f0782c1e50304a03500411854100945500606094801c42101080e44664a0201400811103100740f9103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 432690206 1250 432688956 432688969
    0x51e010f0e0307120b0619030f0218070206181b0d0602040521060112080d09051e03120606160813030b0a05060f010f02032205060403140106050915 65
    0x46803201404070080d030000c0a0b07030b400c2001d54098801c0314030310503600030b030b505d00075030003040291800c1e1288035405952095401c102c0c2603002100d401c031010086007021800032808400d034264242d0181c65000d001c000c52190000380d400d00807880f0000b9014090401c00c507107516211188400300c02c00c5a03441c0d100480b45460382d000e00c03d007401003000525056494000a0780c0708056442480c3c2800f00003800404418140442d5004022035044080c410701c143e56108020320403c2d2103501c0080d0360b54645030034000c040140b8038101405101c0b44c0e003004940c400b0140d90b5042114a840d0300d10100b0700291039401c2203825151000c2a50380306c00040302d125610821a50040d0303604011404241e4000800b00384590ba4290080d0125a4001000d04049007400488009484000d0500001c100b0840006900200f00c5040c44151224400d00342510382111510f01c0c01d0b03500c0698400e02c041408010700c01d0306940e480090602d0310081000566a50600c508584100d490782031810904609031403e017801c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 432691456 1250 432690206 432690227
    0x1b0f052208012c010c0807111e03040e0a060f0b0a0302070611040801051506032e08010e060709030213110706050f0901200415020f060115030501051e01 67
    0x1a40304100c646807190303142110006604103110074481c1003c1d011500d4244400340b040000314009004050355100b01a0503c0d0001e058041008048803140410400074003064483e0710b04c40240e0440d007078400303440319666041801813070004404d00e0003003402448280304120455078800c80007610f1038684690b02030a43c000841c54001c3c10340130410040060014424140510760041702d290300d031030401000c0c80c2190801000f28914a03c8200b84a0700b40d61807a007665848020489041ca0444200030f0000003040d905032882c41801042c0b001048050040d00300c1c04e140a0781078200c07507407543d40180440f456060b502c0302070b40101d401201e4121b001e802e50030101c44141501d000f80e1034030304541e50f080300311a0222007280b040100c500900000039001e006401100324840051101817042c0d0070b284000303102e6882a55000b800e00d107410301640703000384100c40001c0c00100c207075815076946040c040d0b00c2a1b170004944001030319040000c2800c2c94904071804e11609149440f14454802e4030040d2040d840f603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 432692706 1250 432691456 432691507
    0x615210a030c050a0b0703020d0b030318060306030c0312030402030115060e0d08121003140a0b06060a03110711030d05070f0308330906040204030b040b040204020f0705011b0f05 78
    0x4c610320840400c0340c046195000c1d042e00c0d540183e941c964514000216855154014482c2d0810004034800e8440c6004090b04483c04403a055a80d03110880000d18101340e03030004a030503018080c07421031030309041009540318500a03402407000c07181e004500034008545000e0070012402a01c88941141050400c041d299840349020360f00d4041050006000c1d80000c40b0f4074080c642c0b02400c10310410408030080c8101408000c0100160411980d0703645ea4010000d05a0780940c2c03011500441c02c80c800e07002041900d43c000101680c0d4138060600441c10014141181d000b4484c45206c40f202d0380c0314004461500c0d800400c82505c144840c0d0782261204009007031100f101c85030a460081d2494a5110008010f4200c1500b0b5800a142d100344a1105801040300348200e10500040000c030f4112489903034420f0b03200d40c02480780c1c0e480f807000800900490301101040a0701003244420000c0540c8130406140080820151001490703004481110740007020750000382d01481482c01d4031072800c05002d51500e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 432693956 1250 432692706 432692713
    0xa0302130806040311010216060f0b1c0b150105250506070c05251205070b0f071401050c1611060703170109140114120615210a030c05 59
    0x4681010041100c601e0708038403195001203091204054201c405103040740c128000035401d21240d501e12400780182c2d14405040d0329124101c40d080700d84103034031000300d0090080c40b5600f004410b01c1d000d8024100d254048a480382c0340808030f440b0100702c0c051701d041c0002c16991145413805030454070b8014210003c41c12906c2a02001e0346000450910401d48190b2090f5202d071106400b45c14140e14000d01c6002403032800201903224400b1070100b82d0300d503081d6412505035605610080c6449864280b040e0700c10240c80350081140d0068110380c80080600301e014910ba003181d003021615503030884100b5546e1000c010010040d010381d0a40c070f518104910341c002c52446088080c40400700300030750310140c012800242140451400b0b100c01c40f4450340901210300c000c0082d0741c09000030003107010041c00ac01c0c001c8029001c0752044c42e40d0b8030300120020b0040c0401e6403014100707101d038080c80007020105148643c0c40c00c6140100e078445040c0c49100000319100610801c16291030549510b89040c1040c0c40502 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 432695206 1250 432693956 432693967
    0x90d0f022118090a0b01030612080306060307021204030f1a0f01180b03010905010f18050706030209040905010207060e060c0c03040b0a020f1902090a450303050103020418080f0a0302 80
    0x994403d03500348a40b035100c00101307048000100040856500d41c00c00e030179040c415a42140070a11100c141d9074444001d4665276070381d0b00e8615042e880e211000c058a9880800004c3c04001c000040381c019031560311a40c021160026041410440310380d0864400c80400141c90042180140590303811100302070120001030812200c001090030341d00c25a10a403016919181d040c540c14080303210301d1589003124800000320109540d1156112505441041c3c01c058000c034034400265110b5210544180c0d000d0001c41d590000c6280c2180034260415100909000d10f20000f03d100750714000301c9030003100351300146140070706215414945400400c000401c6114000704540ea1030303010031212411549040990351440401e1040250294004120000c134034242001c81d00154141258141d01809040b203250900b2900100c203c142c403040103181c18a031b4803202d00c50303042c140c150f407009050301d00030348041c0a9680c0125030440c19090709035009051650401c00d03105c142080c0340c05410903013950318000d49030030b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 432696456 1250 432695206 432695209
    0xd050c2407120b13090b0604090210032a0c030915051b071208071707030c02100c05071508160903170403020402040323070806061207030b090d0f022118 67
    0x5a01803503084c80c101d591980309800f800740303a550199100d03008580038040046160302080c0900415000601459210403055003501c140da404030751942e06500748034203603520480c4c0040080025080650100d016041c02080e003400b0142180c0064581f912400e2510b41c078000c0008007030745010180c0070a0b004009011454006030780c04140460b000f07030f01194803000e0505009856212002c2d0003442c0440c2040503200080e013000308101103a0b0111541c80c00d01e13400d0201622141d000c810000c1240c0140b00000c20213949240c1a6285000207544d103e48550312071405130400b100c0740516a0124a40740070400020f58030105001100c9003450b01c1c10f06166403540414142c2c0c1081d00211126012286600e44500c42c2405003040c3c01c02e542c0007441c195241002564440b03001500c6680100f0f03071076400a0300327034404003d400011907101ca080d404a16140344690b854442c1d031220480042c043d04000050360340300048101021000551914000c0300400030a91151300400f0381e118203c08840310405203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 432697706 1250 432696456 432696469
    0xa02120f01030201053013050d03201c0e0610060e131508070b07020f090f01181517060606040b03070e18040309050901080703050a0f030903050d050c2407120b 70
    0x28030007511f2018602859440e15030700345120408800101403804090003140781c11403800f0400040001000f990b40d07040c5100c0201c143c2903110803500f9180c1080c035104c6290310001159403194080c11100512a81c4580040f40c582109011055018004074400d0200c51a140c0c01100f50344400c4c000c1c0502c06645201503800d00c851031380001c1041d040440c480040d400c00381009a1041000c0340c2861040c64410314081011406020b10b0003020a602e04500e0004143d42c03295146440840c86c46564554a100c03102c0500314400d6030660300c1c000c040110306542071010548041d00c0b1140e0f641800d696a05e20700701d80a01c1007407001d40d4040c0c151280322100780303250801c4600450203a620000111304001c1444492a0107074806907140e0300c01503003000800c80c04a49000d5843e800300c1c031003041c04907a0504540390b40441e0800380c054068103c0c0e1440035a082002082c82c580244252181c1e1600d030710002d4034142031300c0c03900c0000000c990001a04c442c41129070108071030501d10700281c07c4000303071302181e034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 432698956 1250 432697706 432697711
    0x103030504060807050306010c1511130906051009090506011422050a05010f03020313021c0614100311040f020a200309030d050d0b090a02120f010302010530 69
    0x81540041c00b40706469224450030303801511803c0c05440d41c140000020910303e400700020f001b003246001c0003054483c1d550080003e9020121003581c07a64090355048400d02840d1056120b65032038030381c0004890904103d826480541c0e80ca03800343d02442c0159072000b41c103005110604004100100201d0944140040e01d585469040b0401c03082500b10714056005c2c0b640c2d00a92300c61051014100401da0740301030341400d07080c3e11b8600982c803511150090030041d900e5110003580b0142a10081243c4048036410080281c02102c05018804141083c6020524281e03001c01d800f040c03003401440070030108100240420b10141001598440c1100d10034102d03003021007902c0026201c64800000c3e0501c0360308101020b00d10310301551918101100207a61450060b581c00240b04003c0f50030044001164848900307418040c10302510303464100d4441340254030002901c5006c880300300100b094941d030f191465050f02d906071039051902810021004a100801e01d40486030a0088510208a8440d525260 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 432700206 1250 432698956 432698963
    0x50408070813090f140f09120d23040c060e0d06020f0c011416020105090309010e1c0f0606080a02030601091d070e1b030c070201051e070c08010b040e1c170103 70
    0x86900100c08078518a001c040d21288064070906c0611a262801013003419020802203002a60340c6c841c1c1035400042c01344044645010390f905600c0c654003241c0020224811407141c0d52000d103168440c8000c0d2000d4a075411000d800107405030281e4000303400781d4018101d2180301c2000d1810100c2410005080d0751140c1040310b43c0c903480000384070200c1045280d00c5120031080c0000d000c18039100510950f01d0040c103045d541008a000807140540e1a0303030401000110300b0b41461140568942061026a07640300c000f22000c616000001841d11000301e50703048030a0340140508696480e220400c00605456180e551041303c40c11003200400c50100154802848100744100c11450329801480354030060540342c0c03484100810070000d04140e04c8045400071617090810b2070f20b42d10200041c48542c0c0c40305024200715400050f100d810b201ba00030b4004221910307200203006000d207080c1800240d8070742d002c9148580d80305024251030544444202501c80301d07240f9220a44417415183d480420b4020391058 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 432701456 1250 432700206 432700211
    0x50d0f050a0b01020c0d1104051f150909020703020d0c06060504021303020909030c06040f150515120102040b040603020d02120c07060b0409020f0d060f0203090708060a050408070813090f 82
    0xb50801e5070140055141e0010488090b995005035840301e0411007180e018a0b03100e15035940006110b84044515a25811081d1102448042d203908120103e0700d0342c0c0c1ca49402085000c240000d09550a008803695a607265010b80702d070703c18004003900d00c0c900087c070450340103443d1400420b290b02e076440900304203882d00031054405442c5d4014006041e00140c000c000c95081000645d460f07110000f03840350050707800301a047c2c4040c1c090810704a00c03000601c2c41003031641000140054010425080410380f00102c80f2202e489401c00b10031400c13407185210701c1c0100320003400108111406540a4080706072a02c83c00351030b040c000100002903060841c1c040c00f0400000c0b8911061010500c01c80712442c0301510200304503815900028454070030b40f002d030751086960704c510604001654110b50000c1c1c004103c00d5480303041c070f00c8000c1c1e01c0701541e01484d1120b2044000040e43d548044c000d07103002e250402c0c5840d04d030020390340721040281e00c0804006140490131a0002e1a440d141c407032070722240c0c40e02000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 432702706 1250 432701456 432701471
    0x30703061e060b03161409040f060302030c0103050123031510180606120b01171017060f0406091704120204050109050930030f07091212050d0f050a 65
    0x140421501c0c103030801c3e9041e480901c10010000100b0f00f030a200c1010303905090540341041c420380c0c030191003514441c6030064248104084900c0080d08490240da2088003130b25610b04005004400702c880900c2403000002c81c0814456254101004840158030081c09a03a2540c1d40c01ea905030510105440340300c08801ba40c0c1c1304100d410906c080d00c8805420b01d28061210503c0c0100090254050041c000c0e000c40d81d030310307890240c0e03805050f010907074100c140380c0c200c141c0c581844c401c40159040d200303900c0c2d0403602c8001c80e041440c01107111880390301c0c004c44100b07880d101c03900c1e2440200f0010204a92035101909880385400c0c2480280c001042c18050341c40001c180d61050006480060740880c55150422003070001240000c900b10452103400c40c0041070300444400c41d549522581d42001031380c80800402c9c401400b2260300214030900b59a160303e400746907281841e204042c6403038805003c466140d201c0c0842d19200d07400816503455070107400314240e09918240802c82d04c0594009621a5440c2d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 432703956 1250 432702706 432702761
    0x22a0f120601170714130608060702070503060601020d090b0c12040915270506150d020c0d0f021002031024080622020d110304030206040606082a03070306 68
    0x1c460340303443c02220240c040c1c54a002d04071a82242080c0565105032602076694007042c046e075104400800b21681150b085080100020f901da100301d000e51400f9005002c0024042d50000526042c82e102c0307561030710301c0326141c0035120b21542c211604000395805070070000080710880002401c09481c001c5400140c1003240050318800807515400100301d81e5080c150322201c0d03104260007090080d001c07080454940da800c1c00040e140c149007900310909180100b01c0c10184950f5030b02418981643c3d604651003c084480e09880100c40b4164000040e48401d88104036580c094000d5a0004201c040240c140b64940b07040d08441060321406d4178000c03600001c03042c1d88650220620b41c01a0041c0c0d40050701c0e00c040341075402108a150310740c1c02c0302600010319641d0202141e002c8008140c4c1140180d84a08040c0b8000752140c20a4070180c50341810035101103000307540410400000300740b0640d015020507100b00300c1d4403540b179440601039140c0604400003000c191240a84807070041000342c0000303c20000305 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 432705206 1250 432703956 432703979
    0x10e06010f090c09051309020619030f020309280f030f0f030b090105042301030c0815190c03230709080105060d0305090a0f0f03030f022a0f120601 65
    0x42c03004410504207031200f40310036041342ca01000c0d14010b075009500d1503002c0740d4070400b60485010082d0800c00008100950041900d8103040203403039a50180800c1a107900080264003007079698001d203400c0100250000c50700708000c40b00004c1960314044000581e6203490405001a600c103a0110700081c10480085a101c1c0101c40c250780181402c101640d22400402c6d40c026050041f10300455542d40340c17000a0344001c8020800c070280f00c104220315a120320701501d01741050302c0342d101b40d480b0f2100e229001601840110b8854144580c090105042ca8007102002d00405148401410361b50f08080706e4550003d0006080400d04210740491428403490050070b84086074400300d010391514007480280d5540101030385015070075180450325500010005445000154404060f00500c0c3c080028821210615441140d0094803004200b28401c0702c207a80b0358420403d404d00583c070340540240c586180043c4041d0004000d0038003000710b50480c012031081c12403010548401e0388004010001e03c0c0101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 432706456 1250 432705206 432705209
    0x302030a050a090b04080310030602040b0403060b030304060206062209050a0201020607110316080f030403030b01020d05160212100f020702100c12030507020c0a09091205040b160212010e06010f 85
    0x3900f00806840703038031101c120440103800100889400008207054002070380c030303640c003840d0054011551560b40d9151001241e209110440359075040030310184041c078000c010b550495901b0f80240c809030313485004001e034400a980b0200300340080c0140020380005036104030801036100300d004054151480c00060710300700006040c04100480e03040785c140246808002c2d01c081a00c1c00140b109140081d14200c7d82c04d0140f00b00c1d00821090103c01c00090551681091b880803100380c003070b01c4010444e81001c0700e281c0708800a620440c82075112480c01801d0040f40d9114241c1018151102282600c500c0030989084241da180c80303503000700380c10003940740c40b284101c02e07045141844039030310700c10342e640454000103a1184000e2540d100001103a081c001e00030003890300d00042490b110300e41c64005140040082e1030082d250b400741c011640b007001e070180781110242c40540d498141401b908103050310a800903070301c0803030300101c5600c0d082403514024042c8810100c9401c0c0640510342c1807810140c0c250307159 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 432707706 1250 432706456 432706471
    0x71103040803090f0f1005030a0e03031003030e12031c060801021608130b0a080708071815051201120209151c142b020a120516050d0302030a05 63
    0x4100c20402401c001003118000300064801d0305503c61003100040e0145040c500309a0000e605840001c2e00c00d83c000011445042071100401800015002c015540c0c04100c1d40310340368014450042c000700340940c44601c0e039088010500c01540c1340810419055411840142c1c00c50003940b20462042d80b00e500800d4058a4440000c5080c2012005491a04142400b010304041000207442690400b070902800140400034041540c0c0c84441d40000e0040d08100c41050002d4840000302d866244030ba40d0b202d21b002c072000c0f44c680101e41440140d2120706036010104043c44001c0002090050601004074000e004a40000d20282c00c0790051011983c802014101c00c00320b40b00d4032506598801c226990314021082e0000c2d40302820780340124441e1034000c00101c0768443c0e1001c003043c21b081d062030f001105104051403a40001c04440036039960003401d2008000d507214460740c1030390601c01c90207080801d0b40d01e031084168034038540f2840e05148185000b0400a5000810403210300f000f800f4890b0040c14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 432708956 1250 432707706 432707713
    0x31006181808070204050402061209032a0c010f111002070c060801031a0403050c0f0c040c09060203250c030b091e0c0f0f2706040203042a0e0f0711 65
    0x1542da25101d1912804000070f10866031030780450159290001036800480100c15505040d042c0000c00c1c5e540e80d04954110343c2103814032008614410118150100f660a49100600c1c1e84507802005441340d03075044401808120364450b154000741010403020f501001e81140050303580c0ca070b900302a40560203d41041040c0814000100001018054040c3c02c0c40e6903c1c00313180c4203499900e41121280b0640b5a460480d00c0b40058038507030708e039010400c1e540e00751044400f040300525583c1c0c10756035140d481c80741a000d84c0080c0440c900c03d000b2102c22a140096040044031102419138940740108401d4105440d900c1c1c1001c10800e11460800c40c0c0314094001c0340c1c81090b0500c449a4407076075001880348550140404a2681c111912092680410742000600b0441034414034114603500740070406003181401000400b00e41ea0742002d1084074010780e0450410070036103101d01005540015121680c0d02135944c44140040e07060706004001c0e01a6000d508000d009041103c002416a0f4051805180c0c035013 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 432710206 1250 432708956 432709001
    0x10e060108100c0e1018090b060d051f0b0c161a0919080f1207020102031608160b0a0c02122d0406020705091509040b0603100618 57
    0x410025403444852800940031844010a03d821208004a0303840c1c19080200300c0545450b55400012002112042e080568610365841c4401010303a1680020550007107420040f44965440300d410559000a00c8101c801c2d064a5030003541100c84074540c4031594034070b40030840380c2c0201414010302045500552464071154200414503032181070090361466400070010301101503417100300324608406800703464441c40c0d50b0380d8513000d81c90b00820f40c11500791f40180240c2d011030003010800c0e215481d8041e4021070800a1a03030305260b03244003400080d0b03182c0c502031102da03d84600e4160050381c114030980f2020f41c1802c008000000b07070340340389480710117542000180b003181c03914140c1503c2c0d03a2a0401c0d0130a02c80c5900e0001d040c3e94501c00403640c1d82082d0001008070340180c0008000f0221081664407900c030343e1700e002080420f01c1c0c501032003a5221456170046400306d100e41224a8000c0001402c4d5061f0000080214045602e00e50240c2c40704421011080000c004501c03d1011010140c3e20441c2c404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 432711456 1250 432710206 432710219
    0x106110c0402390c090114040c11010510091404051f09060612020a050108280b19060f0302070b01050907110619110a0f0807021c0c05010e0601 63
    0x1214201805801103901041000916403180e01100d229000614000c0040000f444551500d400c2c05202400d148100300c1d07221400e0130030708001c1d4100c03140388810031340b62603c5004000c050f00904d28400208400d032201030407841000e109840c042c0c581040c8003c40c00e403800000c2025a80044240d51f2032129100812000c41d80105261901101c0b500c1e919140b00083d880c2940240410000681240c1c600000440c01540103081200b200b03008480000495941d0b0004550168080b9161200d0101c60341441451007280b000324080c182c0c80800101e1000c04c0f800102c1c5581c000c0803c004103001c0303030003820044250000200340910100b898103500e004000d881d03e495100040c800e0341c0c000c40b070041c001014944a58200e41c859102d043c1600c859042901e01d00c41c0c4004ca400300e13250000d1802592104000655003150070000107526811244008407034103444813040141138000354099401c4203045154803000e81119850b8035210100c0024140c01d02c5030031990149407160700c07584840018400c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 432712706 1250 432711456 432711463
    0x1212010614070f140304080609160305030409090f02280e070e0f03120301081f060608010b0d060302042d02040503070b130b0a0e0118031515030507080114010611 71
    0x10030f60045040899011903141140d82ca034620102900a80030100e40414458800b151540c000c0c6a00011a01c05411401071861a004680301c01030260340100310400a440303468000d0741c00e00340640300d0114030050307039004100201001d8417520415031a42194419015114840c1d0000e840040000407103807801300b4000c1c041038440c550041c4102d0403900113810710f40d420003480304140ea0300b40c949a2070303507901c410729640d9000424083d44110700004076056001c0642c411901190301c15a62800141d2912010003a507501c0440139014080c1c1f910004805a101c6000792402030b0100c812240c2514200c003180c059030703007a0301c52490545004200030061a0b41c00550b07801690400034505550300000111510050700f164040e4920700c0b00440c00030074540d081203503042100000e8840005c4c548043c02a0f804030229070000a01d400540c690783d070115090b5030301c040368030111038500f81071651320f03a211185049841d80c4907440581d1070f210b08164000ba00f04110340100032034144440c103000c0c04030001e6107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 432713956 1250 432712706 432712717
    0xe2e09180b24040512010b01020f060f0415020705150703151409090313030b0601090801020a080c03090312010f050f030a0503090616020409210906020c040f09051212010614 76
    0xe2646282e45100e12000003045800625000307200d4414811a803105a02074181c00d5104d40c05400b0300e41c1e0030314040c000810726a11a074003c0108040359542c940d12101100341100100300460360a010079000101b041204841072401a030142e082440d08001c020b007681d2852450805000070200200820103c1c482e1030000c826080717a80728000d9940341d240b00d1a501809070340c422850240d150000074403510b10b2a66016040a99600300c0b2191a20149401e074491001030b4030018900b0350025200c1c040120180d6041009401681d20b04403a42824440100081c1c0041055028001d000c000300e10f403207580b90003944400c3c2e018006482e21a1201a1039004200d0fa1034002c0c41c0c00101a807485400c0820f158085900910405c092059400c0c031203154000000c1820050200e5440c160139070b0300551080044500e5a0b0003000308440c45400c1c800580030803c107654100c1e8440741e10310b000490a01c14500c607030092090b0179448006981d990b90034150103900010a1241c01c0110541e90035003c0b0483c2c2c1c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 432715206 1250 432713956 432713989
    0x120f0c06090302010b09040f020f1c0204200408060a050a0608030415050405040f05071d0a06111c1d0609060301060e032a03011b0e2e09180b 62
    0x101e21200d07042c140d01504c0b0303100a165001d0f02c01010441003003c5100b9a5025070b000342c504074800702e416014845141800580300c440d02c00c00940e44001440c040c3c002c0b46400d84071005406c441039031813003070124075001030b0002e880c140c0040c41000300810381032154951040c0c0c4000e007841524908001551a0311580c001c1e80c40404011580a01843c0a841140e00400c00507100b00b002c1e00c642000300c4000c000c02d50700c907170002da086005800716041c075844203610f200c4001d14110900345401c80686941c0c8034006921994055000d1041ca401c40114142026881c991628113004c4503a0b0408516030071810741c3c8501c1000c003800307464059220b54050701d054800d87d0410110040d0500d00091414401d14105407030482c50b240110a00204100040c100c028190000d00c0071411214040140910f10840003001983d151a20368182c0f81400440040056805c0b0450340d81007040341c0d91700401e6800300e109001c11040c913020031080701c01150b20b0304140c1c0301e10340420040d140350000a00441c0d0040070b05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 432716456 1250 432715206 432715211
    0x6030c030703060b0f120f0613020703021005010e01030203100204030b01170a0501091b09020301050609091e1e0c1204060b04060803043b130309081603120f0c06 71
    0x940040c002e600060240103484c0c1929280c911410207030b20103074401c00a0b40c05c4d201e88440030483e0030f0071700c00e099402040001c0003085400c1c95503110034002c1d0460315040c3d0840c0300d01040510003030100c0c41054082c089401503c0c610750304500525161140507024209054810002040418105079600303040d150f091070710404004458455902e844a042006040340d480d0080709000c01400344110000c0d204100b90344040c06a8500e0400d0807400b0174415150803e03c01c001030103081c502030034070750fa000501032403001030207014041c1100c0455088070316000014500011401d004507130304249500c82d80c155842c91406800c4503c24100000c050801858a901c940b080c59260307945801400c0900000802c494444c2da0761180011003000203503681a1440141d654002e006c81250703032102c0c00c00c3d0740c140c10700740549810003460007010403441d0035010401801c101107a200c070184121103040c1c60360303010152000d096040c0b10f54038910200400060000741c502840d030b042c0e00b01428072003203900002d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 432717706 1250 432716456 432716461
    0x306090525140a0e1005100c0206041206021b0c010e09010518090f1002180d02010903030c020a0b070302010b0306060102072610051608130201120e010902060a0c03020609030906030c03 81
    0x100e10f105103a5003240c0a000401c4042003182984d07030040100300c4008807821198207441603026500320680e00b05c0a500254108400c1c041503e91404100615200d407000515094440510703006400b454000f40c09283c0103000d600e0030a40c0d0100d14480e040700d08035682049545003c1c00100014113520b4003c0c8149134610010b03941c08000d11000f100c00c1c10708030584412445008504000b9800000d00c199001354440260b910341c2045c1a055880c5036041c0c49600600e0b0840c1c800b980d405003455000c0740e00280440000c600300500d0405041e005101b60000b0071061031240c109401c002000301030904541c0103920800080e18000c0c0c4400c1481480528451610a000b0b46a4140344080c8400c6048905000070321030380e10032001d00111140340641e20004903071128250f540c4e091203d2240607001540111044121070750b554458108480c81c080001106d01c000d5001c40d4440c5c0002003241702081d8203c070b001040c150144921580480c90398050f41c5041104400a455400050061408408003100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 432718956 1250 432717706 432717709
    0x4050108041b06020a05100204030302120c0115030c09050609060f2716020f07080a11130f152405130e09010f0b03061902030c040f030609052514 64
    0x100182c07004440b086103a066034807008040c1d940c01c05018112560310621030b401815170918404c2c0c80540c1d81c50f0f40030308541200b00003020300541020b010040b00f95600c10306107030404480d0b03400740d0082d4400c82c40c0c2200a032506008004030b80008003814003036010603040250581d20310f8040c07040514100c030424002e450a10b20348840d01d4058201d810303c81c1c0f5150500019203146c0ca03665007802c40e998202c50582c20424400c0da2a80814071404186034886003240f8009a800c1c3c40c41f0714106005010b0b80102c9250f4a884e205545801c100480e841d5981d0001a20401422000d40b0181c074580400800c081e940f0144403510500c0045d00347d041040200b8414807202c19946d15800600b50300800400034104804018000c000002801144503c1c0070308004481c200400d40318410842c1541a0200b0401c0503031a10107940000c21400382081c08000c049058801e941101d000b4500540340011100081d241440c40c00841d80148605071003195010b04603030325142909401e64651042e80e0401808200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 432720206 1250 432718956 432718973
    0x506071d0603040503030a1107200103110307030615030915050a09080309100b1f081008010f0617060c04151407050604060b0603060a21050109240506060405010804 72
    0xa04081c0d118100200340824070200001a501484226004120f68442030710000c07042d00c00ca02d4010002c0244515002c20880000d044414915041c100424940c449241c04d09444e4402c80d10712010a035101c9040c400c0a0007152181340000080c20704024803022610b500032050344041052400c0b603250000103503c0130300c1e9008a122654405542034490030104e1149441e010b2036039001c000203246c003804040d1b900c6d0031803810701498410070703581884641c180c00c11110f0303030801842c00e003a50342c2c1560002203c0d07209107d40d00e1008080100022640e0601a90f040e6102260703020301403541c010ba051000101d041c0741102c00700d03441d6031920000c4da0910042501d40c080701403138240140c02c0c0425030314107220010070000e110781d00c280d408100d202c47d02030402103a40030648030940c1240004205005030541401c600f040900051400306608485030303115425105000000c031014850702c0c481050f039010b54980c0b001761001e10074050100789024408244c2034081c3e0312900703040040382000709003441903c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 432721456 1250 432720206 432720257
    0x2090609031518010c090909020102010b0a0f031b0f05190b0304110f1f0f020a0b1614030106121a0d080a020705030109080412080d1406040c020109050607 68
    0x241c2501c480405041d181c0095900c00c40e4500380300014a202607400f0f0308188a0240500710640307920305c8107403e0807103160003807030080c4040303040d0741d82c4503020500e558543c4e50490007000180c80000c0c015080d85040046220480440d000c40000c444080c01003080049500054803c00e4450070001c9580d00010000c0c13881643c050359104100200f400140540c04101010310034060768001e401c0c1c03094809000e01015074540c070200f01014400d034013803481d00c6008200d016850a104845208010b511282d40300c1a081e10b24810f0240c155001da0007041c0c00403500c107480c1402503411410343d0f00d4108090030f408003640044d801d0035921100302a586400d501c10303a00d04c140c060040d071640340c0c01e8070349201154030400c01c083c054450707030300d000030186014040e410301a680842e425081c00e250400c00c81c400e8010540444685000b440030685000151103540903200714041d15207082d06001040c007080b070b94030f0100e020440e41052440d00100f6030006659030004010300e4030b900e54030b10303001c2880046080c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 432722706 1250 432721456 432721459
    0x11109031501142809021801020a12050f0408031b010506010212031b0d1b1d0127051005070c12022d06070602040305011a130b0f04022d1c02090609 65
    0x1021300114583c2420742c0613054101200d900d00799003c40c02801642c2d660400c450041c41202100c022039601803140019105410485c045181010349401c107090454011403e0340f540c41d800000c100c0400c2800340600da41280e828005440110240020b400c01071100404079124510300e803084040fa00030709411a8581340444000f00141c40c2c0400700128164076411007840040e084510a03412554845c41040714145c058544040c171841e0089501800868200c000c0c0c0380b0801c4040008554690b81004001e40c401d654503255942d02c2445d003d9602201030300a0a040e004020440005858891544080c4c0c82c1c003031142c00d0b10041c20707800c1031400042c142640e43c00c0a00400e4940400030a80c0140003a00d03c01d0000380404050800760000036038170140b101b035100104103200440e100d05603000404182000d08220b000002241c00329090342d01440803c15005a07808400304001030001d00c941a001101020030710345441d203007000a41d0640101004000d13540016500759a82ea50011a1801c540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 432723956 1250 432722706 432722779
    0xc02070b03090309090c07060509120702040e15040f140706120f240311100207050907020c220c08060f011815031b05090d030507060e01110903150114 66
    0xc011b8182c0000760890b07101140c0e07075400c00c40481d50107000420900410200e41c0c280905012541d000c11000d000407068800860164244002c0b901403a0440c05105070b02a03900d44400c0c29041c87d2102500080e4640304a80c0c0d044810180300065006120a40040314070358041212002c600c40d06008004101e04e20301415040742450700f0641e01c04044804983c00713600c0282c445010a82070103c0b0a5030b05481c040103030003200051100e0301c0c0000d80503420032154411142c1c9501100c0128800000c8085401803526400510820a0045018004242d0079138503000d0707000c0c1440008240c16014542c80f09040c4040c00c41003040c1401c2200c620350040c01a100702d00d411851911026000b004a84000070400e28a55103d801040c0070b181150000c420141000031880542d8504035119003000c0404c83d0329a448d40000c4801010900900007511051100c0302d554118040805280c401500b21903200c0002c43d4004000140600d4040f010141080d40c41c581c15030312080e80c6510703161803c5401c0f513007000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 432725206 1250 432723956 432723961
    0x1201020c0703140705090105030d081f0305011409150a0b010e041401030b060a080a060507110d08010501080105010c0b042a17210328020d0b0906040c02070b0309030909 74
    0x10702141d038600d404405840b484ca44540500c0b55a60007400381d40c0c6c041e0f200c1141c03801d14034412480d07945c0c000d0b91080c0600821840248000320103281e94019507450703444d2541d140c2e45d04200f292542c0c102c0b40901c000c001c0406040b2900040c1440145a403030540d5440c80071012036401108a10813001c0d00074000c004004559810700e078140420b00050300d0150b4903900196280c18604102c4003a07940480041104000660f03500c0c0c05400010201401c101c80c0c02e48501007020b003004080c0200400340c5900200c3d60504000601c0e1200580c0001d0410007020200004508100481c5410076044030b50382a046000802928495030030103210501d40c0b41c60140010345500c03c074034201a18031400d09543d0040300c0c00c42854944040b0801203521503400b0404100417822248600709803c18280901d5458031040400900302d03001010244003482e00c5804034032440c40d00c0504070b42c0c01001118100100413110500035030790140c5001e040d952600c0003000c12400300c41003083e90100e4070000c0643d040c92 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 432726456 1250 432725206 432725213
    0x30c1407090504061b080f1e04030c05010b03010b0121110f03012102101b080c0c040f090314180316090c1d0114040312081b04141201020c0703 63
    0x14001143c080d255a840e10b000d4182151711880a00c00038621036442d11400d40b80c804014001c07080141c400c010101a0034038040313aa081c4c0003a0130384142e000e5250060450283d01300903094407401303407100d4402d92500742641c8851381c201e01d1442100c4c210341e166144000641c40d0301030007002204c1c2c0c0300040c001c000c00c0b00384200c0840c6000798140c84d100881000d50035030441c8442180701846c08025444502c1040f4280036503c603024100e0b900310200701041c03402e4455102d1481903400b003c1c0d40c2e07010b03811541140721581041e008280c02c1d035846000800c011545038500614071180540a034205034000540581451410210809141c0c4000d0a035400b00b989130740c8075440561607100303900800d8103000060301014054110388003202d010316104081c000c1054011605421000054000c1d05400c0c4000300c00b007054a0700c204941c0c0119101c01d00e00c1d0408a180310840e01c06000e241001000c01c000034003440319801c2c004118241c0a48000c802017a40c030809901a0007100c000401920480742c0001c20b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 432727706 1250 432726456 432726461
    0x180204090e0c131404080304020d02120d171308090a15030b010e0f0901140d0b0f0609010f0303120b1f020601140a0e0105060702030313060e030d08090a030c140709 72
    0x2003080894000804040d81185001901d881066603120700124400041c0411b5a41004550240c802003040c10b0440c0c0a60000707149170080e030300080312544000301d20901d480c3c000c00500d406038541c0c00340b610f082c5032028180d480c082110f880200740351000b25100c00981c85070000c05000e4000392805038440010844000c00a10b0042410350000321a4168000b1504000d444235000c1c440c007400c19689a800d160807603c000341030401d1150001c24200c004c402040840124038091018422180240d041c40020480081c2c8180c00200f4604596202000007a800c101395030346040c684c80002c2103104c05400000d0038a020145013450321100310681c00a101da0101ba0b96041e10384125400c070310100c55509110301d40249005125001071b0000041c04149880c90143c101d252005089905d040d018409082400c1032690100010540c1c111986180c0e207010702a03104000c0c410f01e000c020501e01070441c196a4039500c0d6001c0c1c00d000d0641c08103814000e1020742040010502c1c6d049441c495510701c0d840e0700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 432728956 1250 432727706 432727723
    0xf14030a021f020304050c0405041704080102070b0a0e03190c0807060f0501062a080f2802010506100c0314031305121207080a09020d0602030618060604180204090e 72
    0x11602c00c031480e41800d18035109036030280703401c500100402010201400001e00c005401601c10202010755544003140010051014206402c0056103d00040c40c0c100004080075042c7c3c2d041030700f44006440d54200c000140c3e45641c41d116124030645a03039400603a4004e4420f9005810018002508424009103802140007102c0c80e00d8204076580c2d807403804503090300b4031810041408100100451241500b55040c41581c1d0003020074510302128038090b100e859001180350b0f2201c00c1184030128900402c04071806103400140002d004c01e10340301000850820b01c100b5080c048c080031402503000c0c548a004e0204c0061290026144e5030700b030440c0105200d84410318102c0e0580304031103c01c81150844400c0d2428500b5101c0f45010607203460f50152080d0300c0042807098443c2c0e03602c00000c0903a1310f03160054021350003084010380e139040601c107006601c1c40c0a05c17a0080b044054003807107100d80f18034040b60200d0300d0040040404090f29501d00300030b0712560340140d5245092041e0040c15140201300d100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 432730206 1250 432728956 432728983
    0x305041706160509030c0406080c100311091309020306010303180902070528050a080310080c0f01110106050904150606080f01050d0305040810060312020102070f0f14030a02 76
    0x95444020390780c03034008489180e050742c041e1510041560184002d045611401020784a00410540104049030900e40c40711816603c201000145d03420703e4014100d42e131003180380501140030f0305080c008241c400c004400340103910700c94840c1074400d1207510441d40c041d8020103492040d6580e0500420b448030160304d04500c0f1420300000100702e141032080b141c0881d8441c002e000b00c1c03400c0c20507224814070140d0210000010240e0701d800000e806008840c40107204d041c1441d02c80c20621003842c40140240c0208525902001c80c505c1380d5554545c0c600008a002d2a00c10340ca100455030890262089520917038009610106000800c041d940740349103005180c000c01c103c804d130394aa0480f0004d1003035503402510741c00c01d0014080e41c00d10f40c100c44690750003824002d203400d80d540d0b042d80c60014243d565102c441d566a0b030a10400070854540c481c16442c0c2d01c000e41c1400c509071140c00300522180380080504002d90102002c00c48072007142c00081030036209681c2c039403036000000303501c40307e0410202 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 432731456 1250 432730206 432730229
    0x405070510140c10051f051e03120a0e01050f07060507091508091207031d0a15050c0c061c02031f0b0c060109181202101805060105040203060619050c030304030504 72
    0xa6140181e81508500240b20742d1010b950340c52034841417210704954a2300d0b81c00c4000c1c4c0d0802e000580d4030208620004600c20b1004aa0f42d8050390400070551402c0d488514104207040208a42000486055030316a5402070b4000810b501c4000060303c44901e164400b0502c03800b00414040c2540e0040105445100394405a541600801140788000d1003510802000b0840c41c900c02481445421036100c0c00d428080c00c20b40c62141c8900c2c007980821500001d4800082e0001156902c000060103003c2c0040c034280e600a04128107419012006405039005030756095010000031112041005101e64444000c9a030412494440740700074520b0b2301040d81c096030303031140340000604801e4621904040440c1c0040d03a0030401040c0e920300a181c900318150b107003140704401f803400500042d849410b40c604010540e03106102c14601c1c180f414084140d100c544210301c140100402e9849030300880c1c06038030100300c020150480f2218292264000d101c907948240c0300c04400c100030160000d0041080d11400e5208 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 432732706 1250 432731456 432731461
    0x3010e071a0c060103030818100507021501030822090c02160e06090a05270715111b0616060f0612030c03030f0b120106031202060405070510140c1005 66
    0xd640b052240d41c1c1d6560307000f6401040071074030454500b41c001d040115500d0403243d07804000c80c6050000e984062407150f840b801e20041d180c04102c01c041041c0c00ba01c0140480d07240d91248100c82c001c01c0c50150401050013105c40c6502c03041c10303454000c3c05c5450410003402d10b6040c3c0c020760762514a2200742900740e201c1804904001400c1c5003502c41c580041c42d0b5070700e0f45d54541e0840041c0c98003912130381c6024650a01d403400c6041d03000c421018107000d20010304d842c914040300000f001814070f8400050050700d9250347c00d0400c021400e080c5444107441c503000c10b50044004134015108011100e200812103e480d4030802c0346c1074212185c5180d4090051051175251a6040701088001c60001c001c26401d42c07403600020b0007900038003e2540c540d600000c254640801094500090310b20040d2103955a03a01030003000a00b03c001c5d40b0040f03a0348001c041501d081d58a1555584160181d144566581004101018030600f008030060465168250b202e2055214241e5910f071580780c81d44901d41810300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 432733812 1106 432732706 432732749
    0x902040605181f030201090b07020102070305030c0c0415050117060a08010617010c08070516151805060109200918130c060203070309090e0c03010e07 66
    0x5101d0b0103280c00301c000307041001a00704545015151407418800360340d000400030291001400c0b0166143c10600060f483d0030310b030380e00050203880b00003481c1805620201c6c440c0e54040c1c041c4e41c01e00c07107442d24443d04542c001c001c1c02118002002c3c10340d5001115011304800750130042c06041582c0c4152100706a85c00e498031900100802440f900b11800b401c4001d10076801140d02c00d24007540d160511500c003e00c01c0c89402e508140316031004140c13000340000200b10f903c0d02040c0d6101004204044010350b120014078000582da10f010790000010301081074014050a05101c025079000c1c50f00f02e00da101001c0d001400526004031405900707840c1c400c0322424071406070310b03110420a03250200e4074003000340c81c1c00341d01721004542091040c20002504400408140d80c549403004c07030842042007415181100074881e066156081100d40c8048c0d0102003216401d071104d1000e9203003049844034 = true := by decide +kernel

theorem cover : BRFrame.Cov 432553956 432733812 := by
  have h0 := BRFrame.cov_init 432553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 432553956 ≤ n) (h2 : n < 432733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
