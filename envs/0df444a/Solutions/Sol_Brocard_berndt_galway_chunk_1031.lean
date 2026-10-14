-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1031
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:55:11.472985+00:00
-- url     : https://prove2.me/submissions/352265eb-932d-4a98-aa8a-09f37f42d030

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 185251798 ≤ n < 185431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 185253048 1250 185251798 185251819
    0x305031b1204060b042003180705150903070b031605030405010b1306080706021b010c02010903080d050403090503030a09030201081009050408030a060b19050d020d0903090e060f0d06020306 83
    0x10404030700e8076025034024040000d461070a80100b008855240c076007202080d4000c070140c0300390326420082e607a1255034040d14129070244040c0b202c1c01c005154000d01c2d8058501045185e5074595034000d042c0011090703049510040d1184040f002c140402c031070800b82ca0344e03507a04840045110310042e6402c00e100d5130020468144560000d01014800c56400106580c0c0300c1040000560070851030000b8002400034090440602400340110401c2e46502c4e41844541c0c5d51400c11079104541000045030045200c0d80c880b070048010f140500700584080d00042e00160022486160200c21260305c0c1840d0745440000514590064540c808000e250600c8140c1039180060414128040d8902c1079104900700c556034507250804000322248c0d030300081e1031820203002503000c05003828138000c40b007082401e2103610f0710203400f0b02001034450810004110760811450004050b00148840c0a0315080c246441180d85c0341403d10502d9000349041a80c0454009081c1000c00c0113030303000b140c10000141508030381 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 185254298 1250 185253048 185253067
    0x10315051201050703060b0a2a050a030305060312040501051905040f08010504020301180b1f150206060a06020102030705090402030a0b2e080601051b07150306031e0305031b 76
    0xc01c6044040080d95035101d9080101940d4940b2540c005003030349000f43c40c10580f000ba00244124600d403140000b003801002c09081200c03881c103450084540c09021201090400e1070014060700040d902c030f03806440b40c03424852541044c0400c2e182924410b82d101420801080800a43c1010780444602841810400810100c451070a060068803040b400402c1c01d00b014070605084800d03064074112090703000d000c0e0000013607604414a0b0002c5200040c82d0420742102400446000560b01071014040c41e03002e001071030382e004210948103103422500b03481216520755050f0b0907440211f84540000b14100320401042c5090303405540c00c6a030b444000030745640e000b4045800400110b6058104400d440f02c60803184480e05214500031019140074030b058181300c00043c1c018001d01d030030301720301d180c03498980f43d0000300030003084000300320420010b070400303c986074013900030840c50209070b41655102c4141b0b000112010030070340714140d041c1e49107481d55450910710600b45c0c569004040c10303e4400c00c055410b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 185255548 1250 185254298 185254309
    0x150b0d0507060207180b090115120903030c18081c02030c010e1e03070503030103020d0203010f0624020129010c050106030b1015080a051b0f0301080c06070f0201031505 74
    0x40d000e150000c2030392a042c60b840384072483c60690302c0c4005d1820300002011544800d100281100d903401150060006c02e40000c2d54683d007812100c01441e480d0030707050304c185507040c0c0009000e611141c4440c0385007200344a02c1200e4000c0b0740660000b943c030070085100303160031000c15110422000e1050380e0411110380042402d40300e007440940465807060803542030381a281c4030188015281034004500c1c007007032a954151203020500c0060f101e00070500b03001065481c01c1d00600c0480b125030404200058940d0301b14103900e60011080e4442c0f0014132030b11a0194014440d11040c0c902100c4081180070b090801d281c44140028503250401620028050000d50240102d50196100d404114010f140450300b8031800c90099000c4080d48418444c002038072900f029075560000c52440c0c0115a69413440e468101c155100c0a1881d070305c410015190b105032003c4006076050300d4095090b0380014074118100300301360041c500b001e0074140c007100001d001503019030300c07814401c540ca803252460b0b940c0d10b000107403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 185256798 1250 185255548 185255563
    0x1611030c060f01060207050a0e0a0f0b122a030a08070515070507020114030708240d03030905010c08060604151218030e0102010501061b050c060a1e0903150b0d05 71
    0x42c10355203903005100060301070101001400040d110b21000c80d1070201c40505460700036003480710a0303079640000100f40c035040d00600801d52000d02401c21001103410b10300e96400b000c1c00c00404011881a564501803c100082107100c0402001001180d002d91524540b80d40300107001c80b0503209000240030180b034410340452040c030b1152030700f6071200d48900016140d030120000340c0d03250500800802000c540c2001d80750b80c0001d03030801803001c155002070501c01c2d01c24010110583c462508080e000400d545074100d800b13543e101f8802402100b140d550280d842c000180c500a41c0504140400e0011511451a124a070040e074038040b156507003508130000484000001003001007a03c001c0d100d09140e0000000100b00b00203200070070880d03241100040c10f14043c00090404007101059400510408111626104200030b00709c0e0759074400c488015020351500c8546484081a504080b1002d0f801050800304480e0440345611003220250404401043c1c180011940101240020300201d4810403008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 185258048 1250 185256798 185256811
    0x2030604030c1502120a09030309050111090a080106080601050d030e1027061d060f03270102040608181507090906081207060b0102030d0504080a171611030c06 70
    0x6449460b03003850703048080708954120043d80108000c540308202e00c008550b0000901000084a01c1d8902d01180580070025026101e0343c00c01c1f18180844900c20002e1a001d142100e0500c0955078408100382a64900d2040826075088100100b0803401e0104038261203511034540b0318082d101c8400010b408105a45450001039640e540082c9240c1580c01c6584181d45002040c50800380317418401484054842404040e400220080864075158981070f0703043c08051141c256101d01e402590301e5641c03111440440307d40599050005080403042c421901500c840d0740e03828100d03560701c042483d41c0300202c81302c2c20003620401c4078a1181c0c185029659015451941d0395800030751405034420b041d900315812054082d00005805e05851b84030008460159030301043c00300b0703516a07010042c0d05600800020301000c41c1050308200c10010003600900b4600b859484030881e01000909880c0c0842085a032051100f081092040c4c5880c02040c94001c0e0310615800c4911b0325140140c1c1c242801c0096505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 185259298 1250 185258048 185258057
    0x50a05040303050c03091c030905070803070201020712031202031b0a020f0106090c022116030306180b131e090302060a0b030c0d080a0201150b03071d060d0f090203060403 75
    0x3448101039160061a40007903a0400803402c40c10308244c22a02e94220f640a000fa00c00c0c803103d032011540c0a41c00c80c54070503400005807010306a607250301c030362a03620030b0b331041380103003c0c5050200f00b4084c01c003a5107040340c1e050383d2821080306405150074000c1d40b0240c04042480154204c00565001e0740e0018200300c2106c0c2d02401045461840c03060a44045800c400740701e90601e40d4a103111a40011811042c0b40501c0c1030f4513070003481c04000c0d030300307440b401c40e0b008240d4030700c00e90f007009047d0507400c40c0003112110b1a42001c02c0ba040c0c104441280c6a01d0103044e0710101300b030b101c164003c400750030060303001402d111080c1a092a81040108540c1408011805030700140308010000d452889190b1846100713402512140116a002409009104000524441020aa1414070fa100758815456584d6205400d01180d407106039602c0d1a401c201c2d00280020400004c141d1343c0409202c2501000c90042c1c016410300c4040403055001c0c0421413081441030769a01d01c1c040c00340e03504101d8140260b0081e202c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 185260548 1250 185259298 185259301
    0x1050d020d0213050f030a031803061d07062c0a08060a06050a0e01080a081b0303010f080f1c030b0d0c090501030b07050903031b031207030f0f060f05041e050a05 71
    0x100905180456032104d88201d5086030700c1506500c0100780e40982c140c4c14076096008000d80c40c1300c40c601e4105074001403c8a03140c240441c407a00000c40e42040d00310204c0d0110782100e83c3d202c0b422a0400401101c211f0034001c00c58148400281c03d284100c40c8030346c02005248501c4c1c43c2c0c402903180c40c400300c0d021100f030340e205c510810080c02e003410004068003450108401c0c2e50704101030103607905411000204001b000041c041d500355640076444142c0c02691003540e0703a07541d6604e1200058000f90190308903900803202000c1e41c0c0c61001841000b1b170000462480217444d8003840c20740c0180492a201a0401003000300c00c80040c03074406a0b000903140080c1e0028a075419820203c50601c0d0091200e0140f001c100070700d252039500001aa90248a1000c20307411208801d005a42075005c0c4409520384566400300f40001c0a4158102011018a0301c1c010800c0050314141c1606484c0d891049480851620400780800d0406800800308007809410006484040f000c441040303500803900700118541e00da0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 185261798 1250 185260548 185260567
    0xc090601173117090a08010e012901090302060307110604080a02160b03040803100b0703021005060105090915010302070804081c03090b06011d0a080708060906091002070201050d020d02 81
    0x208a00512111126000c082d10041d0744500c000382a0260f080814903010507109180c0d40d44400b607001803c0450000d05c102c03c05009118003074007800d2010482030701c0c0d031000300b210709113a80780c0c84030220816036501800500d150240300480d40068901e800700b04181c9030030f00f0442d004000039030081e4483d1307244c0c954542d00f62400030f0600c403c4040101c8010380d200b404100140318841600e8120350172280007541ca88541c0344049406449da07005485940010502000341500030070404142c154800c1d045c00107950b00401151680f003111405544501e03204045031440180085080105c1f03010306006242c0046134482c080c850b007056020304007650084c00211180a0643c07190b40b110b41c060704041c002581203680e03003800e004000780400d040100601c1034481c01600380361070f40b6510402820402c2110303140d14200340c41e0049070089440342d114800219084260008a0701c0c0305502407000780400705585401a4003a41c060030040e1f041090511034640380e0416840104002c0148100c01640d64a085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 185263048 1250 185261798 185261851
    0x2b170a0f18051c02030d02090307121119081203040f08070b01030c090207030903260c0a142803120f06060305090a03080a15120825050c09060117 64
    0xf80c54510400405400d0016464000055821035000f584000da00c860401d008249403100340e41c007110049400036060001c0c0074610300b2210722403a040e51403d04170141305009400d1005644a640b6241c0d22a1443c0c400802e202e101a40d0840e2044030310002940745900c401460740c0115100341c0b03500f016040100b01b000340d82107158000340704100056042a009413005400703649980b0014084460300020100540c00701d005840788200c1c0d01280580358082c0c021381b00c1daa00c9400c1e50032114040c0015080d4882c60380041c003004030b8002428807524100100103c00080514480101c041c44540c0b1141d030b48480c8075001e45560005110790000700d0038944100107041d0340c4080e1140865030051071840012a40c000c05041c1e1000c40e45401080b201740b00340c8209050f00c019404415141903520b140c800304050000100015030480443c6608810f188910b404001140d480080003a40702110340101410704c02407080e427054050500d240c44060600b0305101c031860413500014803408041022881c481e10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 185264298 1250 185263048 185263063
    0x9090c03061008030a050304080c06010f1406090604090213080105090d0305070e090a1d0f010f0b1e040902010e0409060c0906110613060603080c2b170a0f1805 70
    0x140c1140002d110b01d4034100649070b12030030710104100000080041c013440300703800407158009401c404807155076079203810820191056024144120034000301c24ae42d5480c1c45001c3e941c8036400104502c1c03605141100d070030020741c025480d1200f03204c0074071000620210f081c41018451401d1002510340898042c40040031601c00030b004100f4001c1000d0f080d40d894441c6080c07a03610101710400081d0a00c02650300c0011100445402c030010b105450003598440700640280590f180c4100c0e082c40801d200c00104101549000d10303a141145035032503a2900c1d450306410916507240181410000c0a0310080440e059070b080b070101f03860141d151801404499407040c081d40060001c0c3c54400351202e1403c810f55204c1001904500700c00c408921f40340e05003c815130041740210380c02100b80c3d540e1000f00300e160762114500f608681d00c403906514000c2608504034003000002e4080e07661400950003100c0c41f8a0140e6001d03145907800c81d520f054611941e81d9511410380000d40040301a20200042d01e01036251184 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 185265548 1250 185264298 185264311
    0xb0307050402070f03030b1f0c1e0201050a05130b071103070e06010203040e0606130303120e030f12070903080d021803070e010e040813060e01020d03050423030909090c0306 76
    0x204100c0c020104204c548040b1000354517103004104041140c002540c00380083c80154941010b40905040c11780c1c01503800072483d031140c0000c0300000703011210201c2d08180c00d0301c0039001c100c0810400f0304e05032080c1d0082405464052034006081d032658000c2945401ca4941252050a4030a036000540780420244000301004061240c5034503004000030f4990080c1c1c400c02c08000c0040740403840c00d1b41c81105070343c4400b4041600c1c401240c3d980c200142180440c0302440811440d209076110008400700440b582968641032541c41c141c07600040e5030070004000c02003005c00800c4440072000408620003820400c108a50260300c5e5002c040d8030075151504522564803e0780000001c00c40341078401c60250441380f0140c401880e9a030380782084085071194210001c0310301d0182c0401f01c0c103da000411054094420f81c2103c00d0074130502c5083d802ca420684002d400310f58614a1740a04d004070340c46168003255503100b980e0814414a001c0303101000141c0b021440e80d0440310100a83d81010403031268082c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 185266798 1250 185265548 185265551
    0xe07210b010305090a03091404020408030f041a0903070303080601021e06011d01050a03030e1306060201091a0403140a120f0204051c0f03350711010c09050f031f0b03070504 76
    0x17203a070080c00503c881c1c400c1c1c8950481d43c0c0109003942d6901d0381514002e00c00401900d03621035030800c41512640c001d010b840a0402d28206c0108603410b1101550b110040207001082007508589081d0380006004003039504602c07031029002c0201e0300c1a000b8003441c0100c0780041c502035040c031001400c0340240510300000b4007050b01c01001a95250781c20380003141e0305400c00c283c4172031011340400c5080750301d0808000550304003007000a10540c15030155296a00031140081002022415014131100a4030040c0009603e0318001d40f0505541c4c004007080041070030250f1035035032000d8904060b103c150504820321a4045070070455428078103d44c0b084040e2113034502400742510390b00d49803003903140b100103020050084502c15000d50440c048644007a1507c40344140c0d00c00a41c4028080d0310112408030005a102840c804142414041d4104c070304503030f0301c50089440c100000e10140b200e06902c501c4e4544103184c2d03007800a8038843c9060060404040d00400c180c2c00c0c110030715240407844d030710050190313 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 185268048 1250 185266798 185266813
    0x30507050303090127170601030501050703020a02030702040507050d0905011a0102030f04090216020402040b0304030e030c010c020f0307030822050105030c040e06150c0309030609060f010e07210b01030509 90
    0x243c0e0722101c100d004004c1041c00503410902502040c40400c01c91b04041400382948450101401c800605035040301d105100038489641c64800c05c0341079001d000c1984016038000e000740300040c58036400c0240d000110786841800c0841d640f621400f0380d0070421301551035035514600040603503440301d41e018074a14280019403401403001c0800107603100c2c0384900395489502240700250b03103526404c03c1600c560010010741d00d0319107642d1002102e50003920308030b001c01c809241070307501401d0104010700350f400305840d07200510746540c0074004800c02d05540d0703a81c10701030310001000207507020000d451000d00348860180382a0801500342c1440d1400d810460601900340104000d81642c0e4080700c0a54807203503115100781d00e640010400b503070345c0c41000c2c18a00c1c40100b0000d5001c600080035008801c070480c02c4500944405290648450b000e480c00f060400444005100703000d01c138080507400208a02c0c052041440a140385030f01c60105803035070740040703031543c901d02003035a070601510342c102026001071300c401c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 185269298 1250 185268048 185268067
    0x3021e0303040605280909180213410f01031101030905010e0d0203031905040c0302010e0a03061b0323060f0a031a18030f271009030507050303 63
    0x1d9005a118080410000041c440c141c01c804e484600320014600d001e8106003111050080c101c00c090303001c0d4000c0c040c50601f02c500460710554030340e14481d401038441420000c0d80c0030b010000d0260407500104100b4600c0d905a804500c12650741c00d1031200300c00940e0440c545080c01d041d043ca000d81001141c6400070010301c0403840c4070301c0380c3c001c2e4002424002003c2c0300ca46071140c00750814000c0300109004442200011a802000442c4038095215803191021a403200304403c4440588014140d002c0382a000e00040d4000c40f1400381c0342e0401006840c0040d500d80d0f030a429903410141c0e03032400040400d1541700058042c050750040172f201d800d074410300002650050203c4100100200d100c2c03c041c504800c034a45415010001660308644042d0515415032925640504261401842d0000e00121400d51507004001d91343c0241b5000710580c03401015007a000c0d100175041c00d2b02800411507001014890b601c8107400c2141841580315003150516500f011400c20100f507009034000d801c108481c065 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 185270548 1250 185269298 185269303
    0x213091202120a230a0306050301060b12010b07030e03060a02070515060d15021308030306190303080a090512040e060a24030203190914300c0a15020403021e03 70
    0x642c0c00c403038075020103030352007000c481598503a0043c0d044094038400145e000c042c1368140c10440a90700d0690090002503a80d02c24580c1c1c501c600c00c85003c042c5211001030049801c164010078101c5c0c060b02c0d120000e40d000f100040e040c40010385021003000d07030028034a01002014014219026200c6102504910700070f000f04081c8035203040000d050018185042600d4078a90f030660700c00d26941030000848070b842e007441c1551b81e803003a28503502c207021205003a10440060450b030313010f9075850707a284002c1e511071000c060043c282d80d0724100d03820701520040e070302c0000d020341c0904005c0a680412585504000c2c05102001100780c03c03403d0141c48004041c1551001c0e10b9400d800c00c0d14604d001a03590b076580c000c41140c94008080c901c1c856003000a0705041c07018a0744072010650480781500c54110144d201c00c040101110390f29000c2554044198083c80804006001d0307041030300083d40d05204075903031028401500c0d940700607005507011030144250b0030700c1d83c0e214840100c0341c0d5071501c0018580c00002d6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 185271798 1250 185270548 185270557
    0x507020a1203030e06101d0108070b0c0a020d080304030e03010e030a120906110a080c0406020d03020d090c0608010918020603040f140d0f0318020d110301020403021309120212 77
    0x440c20344841c1803400402d480b943c4034001440100083c0d0f203040c248000154010203a034452901d618418080150820030f80c0c800b01030403650745400400d07502e86450114104e54222500c9a03016029000d100d001503110080c1500d00079125214059491519243c06011006071000c5039010342c0c54900c1c0c03109211000003c07250b500b1000d042c844e24007003003c0343e04009440984030003840c030341c10300000b065040319440290610008648503d1003d52350520628803600072440303400b006034850b060128805010754020148521000d00100d00d41d801511072040e003900c9a0b0141c1d001801c454010021820544198000d0344002001c11001c18140d8001442902010700040c0c00403a17a1031048003008540d00f24541099450000d4a0301110f5908002c2c203680320a1074040003280c00d00450031615148140100c0b00c0d280d006100c04070103c40e68503140740c25180070103601d0b09591b00b044003001581d11004640440e44046001060912403450883e41034284050380d0b4066601281c40a28030008403c10346 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 185273048 1250 185271798 185271809
    0xa0b01030209060d1a0a0e0a05060c030406110a080108010b030f03040306020904021e1305220f06050a03210c031b0302010b060304050309090903041508090a02060406080708070507020a 81
    0x10040c6031107941c0040c4504c03000b201c000303000c10302d45c180301d2a030408a24a224030070f01010000301b10134900b20740900e0b12100d2826000344036400140004d01000500c501664000e4002c60380042c86400341241030741302d03900c4070715520302040c1550f004000b01d0b00240207001d484a407e8018142064001903115641c3c0250b02000349015000f042e801856110f81d07045c0d8000d10980404100b0a035142041c440c5d850f40004041011510b9100d0049845e04180f50240301d00003059196582c0301c0607034142d040060001401359007525440d0807002449640706183c0300080c5009407170300c060f2841000400503d03d0365104921042c400130304502d0000c2500108000320400c08200308203041400c5c0d00d0103d005028000c62541d01c040044140001c1c46000409483d030070344240c1d012140ca845454a155480c000d52040003d5004004400240f6030f2149040c203803c00c0603007045031200c409071713400138545801c15044400013543d0b58041007400c5a20080d05600b100b050309200f468490590082050300c680d90040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 185274298 1250 185273048 185273059
    0x1091b110f06010303120e0105060a061215150314060303070f03020313090509210a120e120703090e160f020a0c09050915060a050405090313080705090106020a0b010302 74
    0x10580111800c0c400040020060300680e9003540e120300c0c000c1d18036010014108086d0b482d29481000388030051191a0049100130041804145007c0080780c4a6490124070078081d030f190001d0031140780441200c031010f00b20707108010f5440104414010211155410315071485500c100c2840f17841e88022046454941c4c00001030350100480382001c4c6d103148145082e1942400d692100001d103518927911150081c0030101c1a01c1c264000c04442c969441815020b2076482c171010018204442d0050400090310346143c040400c03115000490141000d00c1c001c0c0e811a60607000034403004143e888800e1201a141170102e1060038140f010220917454004220740d014411040c5280c58414020040c150b4050b40c40480b4811603a00d500444028100640708500580728070035111032503125032000c81e031080c2e5000c0d092003601860481040007a0101600d4011240400c101c0389902c803c043ea5003130060110540280040740c90042801a4400140e00c1402103402c02c00d044000200f0902e81c1c00d04490b01102d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 185275548 1250 185274298 185274317
    0xe07020d05090d260a03020306210c13110c010902011803050309061e0703020703060612080f03060f03030c031207050403020d03030b0406210c06141b0c0603150901091b 74
    0x55122400050303040758005a4041241085146e0540086104140c141d8140200208409a00b43c1914440907040c1040e0440700450180341854408a210203c011201040350707010400c000c0010741c02840e100070240d452742104015540c02c1126070480304640c0301000d03446491038440da42c89002d28100e4910606002136843e58002091500c8244424020070036a034400b041d107006507032001144400c490b19030900c03100242d0102c003004000800303070b04134111918004890141c01480e510040009034825003200c5c2e1035415880c1040a0417840900da001541d0311004030030700c942c030b2070801040841000b00030002070005844620002c6106549400d01241c80c42682e400140540403a4011b50300f803104040350003a80ca00300c1d8044008017070180303851100c4c00c0d40b10202200c100302d02c400d01c0181140200400c5040200520721002030509004c262224002808006181c0b40d03c01e40741a81c0a111307288490155140c06400c0a00520000c881004150510701002c0b04330342003131800b041070010043c0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 185276798 1250 185275548 185275583
    0x70c05040b0d08192d110f0c12030706110403140a02060702060309010b1306090f060f030b07050706090b0906130c2723070c0203030301030b1e010e07020d05090d 71
    0x380d008040f605645c05082c00b01021000c8282e401c4480b40e24840040c18111541862681c082400207411342d214010b880c14a1500c0c0c203004144030710259224042c481002008003013601c030710501c44900285e0b801103075505c1c17650428804500ea88007640c0d4251b0403080c0d210703006070340f11000c44121544c15100640c490b40d405c8242e80c010b084034140260000c283e44d800fa020394100c4c0e489007040d5401c9110070480440e90140460842e04240506207a0345010f14052012900340c000c1140d010485203085854210070346da030324003510240740080310040303550002e1141211040c000309500c03c600f40f605804a150544440801d6032040c4180650300314a5042100030590201030320ba003400c01c0380018000a21164504508a00c5128052025110b99008128400e128000c0ca40d4141c1d0000d0003141180d00b56281c0b002070701805001c4401400d40c00c9807081210303c0d2805041c4c003c15402c5440e24840c64041c9029040c543c0010000e001c0240401c102007240e52000c44821070f81d030300603050b840c1c07000f00e02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 185278048 1250 185276798 185276807
    0x714040902040e010203090f060105030c040504050f0a06090201030507050a082d040f0b010506030c0a18080a06090203211c0e030316020c0a06080f040303020906070c05040b0d0819 79
    0x803030003035009801d0406152090005400450140020324210b4410011100c60fa80c1c071018280980c40e49600040e41010355407078140c00c000d81150103082504c010031092140c5920f804590402102c41545138202081590380610031141d00c00c40030f041047c5001503c2c00000d1418000501410000e4680310350000c136081a5039059202c00c0c0e2028045101c1d003890300b01884006102c02c2c0890304c20907a6030002c19270382420f000384c1e0700500c03038041610b00b0860651800d9800410034000b42440003132012001441c00f4041184840d098000c0d4000107103080180181400d140c04110441c0c3c078a120f114000c2440c080c0715007211104400400028008100501d640024001d01c14031020140f0000c800d000e0181c4c040c80d51131b0228440c40c1c01f100e84034040c84040c0300c1c609005105000100340362400280700c20050300143c650040c0303e450014a499100760000d401d03030700a03103402d5400320080501484541054407c20345d10080842d42a0103821081c1c3d61a64540302d1003030050001c1507100010312619028 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 185279298 1250 185278048 185278061
    0x703090c180618020909150103090f081201080c0604180b04110406120504020906011b200102010501050d050604081c0f020703081303081302060d02040b1911071404 72
    0x300c40c11007011a14060640020b8a02d500840783c05040c035001944507042103200b100c1c075440740507000a65035500c2a02c5880c00003205219181416104c110950000f016405034501c454441c00032680c4841d9640314440303660f081608a042c1c0c0e640301400000c01a9503207000e886c22500c10b00c019010300c20058444001412a41c2c0003540c0041c10005130681481ca0b081c003510a484c02507030382c4201c0c100302000380701c142e601c01e0b50080e4100e421480031602d0b070f5203c1e070384540801c81c1554a002511086982c1c174829042c0d1011043d48010041420711401e60b420301849004000c01c507600c01440341151144d0341c80f414040c0004143c0c103000030784040c0d161142d064250346a04d00304020000041504801c4003c0e41c08104118001824040014500740858542075806901644e4103c4282e071000c1d42030b40018082c080999101030107000c4041800359600041002e0520800001e440d0000d0300221007070480c0c6034403c0020f12040343c0f120751314110006480700c1240d0180c00380b05140c106420214005148 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 185280548 1250 185279298 185279309
    0x510030c2c01080a020310090f120201021b060a060605040305151911070605070305090a080309010b1c03110a0b0a0b0604090203040b07110c06030c07020103060e07020a060c14030703090c 82
    0x41e901d00015089001060070000b01d40203609859203a007800c0031910848800b0070700100030a011442c8400462861600a036040e540c90000628042168004101041801031604002d60042003007069008207070140720002c02d01810041c0c28142542e6840e502c45569014052502000200041056131007000d08e240b1000c0d9042c0c01c00810286051a400c01da2200e481034403540c0c00c00c0c0115905500c288101c80c403410920015102001d81680c0c2c044042d070001e881a030481d0348810011280c1d50750342076000c645504c442544502481149405029203201c8080e01026030081501500440c0311404560f501100008001450010304000141240142e400068800f171020040104001200c002c2d9401003085480310030001c0040080540d0b100c19992040b500110700740082000101420082c0601900c141004a403680d250050903c1b074003000c66000380141c0c05144600240404c1e4468a0a010100e00d490f044100e040b001d030300c440e80701c003400880816139107000c2c003020302c201c00e02d01c10042c24 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 185281798 1250 185280548 185280629
    0xa1a1c1106031006030506060403200406090e1011090907080601121d06090d0f08040c081c0e0d030c0b07141c060b030103020102070e0a060b040b0705010510030c 71
    0x4243c11035a4040340c55005039030100707240101098203881c0102c00d0f00c0440f64000154000b4080700c0040b01540c45043c0035281c2c0041d100c5401140040d41405410810104c000082c441c0d042161038010a41d24180b0100c007e0145c00c2041030001e40360300416952061032418501125151000100c1c0c98a031a180790440452070006502408010a089484403040790001c540030b0b5140c010015841e0001c0c00c00d084042510880708036842c5008080b11a0310038050000002c906944010240c20803a4080c40c03808001c0364040a202c900d034000b4001c0105040075600c5803014003c41c0d8028242d01c120310000f4001a68500014009038401c070310190074a48503010040d1105140d0031440030142182c000301d41202d042210104805142c0b00036641282c0e0144d00400c1e1280c0751000c102042c000c082c15155010351129004692000c08900800c0101071540066685240c2070034540d084500161028160340c0c2e46000400204142d001c1c0d640c2941c820000c08842c01c411058404a6140031889000c0b050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 185283048 1250 185281798 185281801
    0x30b040c03080f0d0b01170a0b01020709020a031e02090d02091906030b090709020309030f030c12070c02010908060702100c230903010e0f0a030c030504080102120a1a1c110603 77
    0x221a00f014000f036480703090051041240c0d240054138150a07050381244605c59000020f070201c440d81d04070340104c0c0010b005030f459007901c805440d01a03030301c00c240f4030000c80d885004042a14107001c81038040008420f07811804c0c00840070006800c0248640040e105034405804280826030f12030440d440c000300c2a104215842d902e25000c1c5040300200c84203801030203600700003d64040207008603031003140358602451624840e160b900105801c0584114030450082c45039500a401008105d4092032444e150b40100c07008520005004454030b40011441e50099014040302a800081011072140120700105004030b001c03034210750013a0001c040000c0d072080c0310304e07403401101c140004010200c015070003400700f8446030964664403850641d0140c4030303912070200780000c20700c06c1028408040c820301e403043c580780c1c0d41e0300c4c0a403c0e038008007100c59211900c0001d014500300c05100340c02003040e401ca4510304140c040000518914006004c202e01d040c00e40d00c8a100700070032141c0c400c0780003600512140d2603 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 185284298 1250 185283048 185283067
    0x804050603040f050d1b0b070c2004050a0c0509150c03041403010b09011505090a091d1b0102072102060301080f0705150406050c07150e010905090c04030b040c0308 72
    0x1d0f01041d08140e400c1c2c011054921542c1b4481e5092030120300041c030403846256401d503161210028000c0a4008001400c20303007000185140300c0d504500031551140c03230302d14841142000101c0c4c1c400342240c202c540ca41880e40c0c00b09030700f04050720a0700c003080320b0302c3d1100c0180200502d20342c842c3c01c400c0c0c10755000000f008903880b81072415130310f0020340c250001c0022602c2d041c144403c000080c0110300f90001e40e0079100b000e90348940c00030860510043c10401100355140762910a070746507003c200707000c5115854800250701003004040642c02601010225a041001c0043e44031911809022407000356940c580c0c0280702c1c080b04507514554080c207829a03940c0d5501040740c030395000c91094050380c002c044001074203141460314a444d28060740981498503180c1101540d4951041010074030710b01440b4400030700310101000c2c0c01c0300e203001c40e1a24010001d00100046c5441041e412440c03140320188240a880583c1c2c4003501c00340da070700261400c0a61602e051007101240690b10040c108040043c11040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 185285548 1250 185284298 185284313
    0x3151d0708150a02040f0302100201020702090112140d1b02030106080a05030703080a02030907180b04150603060b041203030c0908032d070b19090b010e010e0708040f060504080405060304 82
    0x107415580c8441c2c49035a128980000c0c103034442c51241040390f036801c44051002d8a800b40407069901d40303074000145041c019a020902d885002da1085c04880f402000110a10032003003800750f5410444000ba00c030410032010054084000301c1d180261910000310b080045480951040e8060079110007101d4920080d450f03d181e6a07840000c08500143e8000003003003070301c00320b0b0003581c0c0141001e0001d01081420490303044004036124440411191b10307444210069150791003503000308258109070105150521401174259050344e80301c0b10f00c10204110820250b1007000180004d0750781864042400350f0b4a190807101084943c00106c82c900002071a00410021000d8031071030303200d1aa41d000401120518110442d000b01000035011814650004031030304480783c1000000e410860b400119030003075440d01101110260012072014a0100051141d4010100010f81c03220b02480c3c40f0141d0310341652040441d511044005001e035032100042020810010242c4029182c060105d54491809051012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 185286798 1250 185285548 185285563
    0x90606050a050102160909170d05010e06060909010b0f04081c03060e040f110a1502060a06050d020a030f0602120a0c030c030c0e13060503120406030b030703151d0708 73
    0xc1c4203850301040058594008149403013400708895080c0f210610b4100f80c01c2c040d00d85600b0480b8584219400119030b014110003902440302850b100048640c10700d00c4887c107080c0c0c0942498420282404230b910103684800e0000e055801200c105500d032814441120310038041c50704201c902c0d024822001491240c42000b030404202103940c01c1c480d1598800c484080c03d0070503140034002e01c407100d1111012070078400011201c800041c003100030440d13070342d00d5800324401282000001a08a4410b2140d5400203010b068040c26084825489010950340000c652010360b2000400502140c4051414000150b040d600600c0710340300c01a00c0c41c0703400c1c040100140046032001c0d0110303240074982c0d01030510a04c00c103608a040c0340c81d00027102c0c880320104542c0d144818529085981c45100c04609610244407141d031401035051050342740d41c1459000760941d104003480502a510102040010500d24040c0075003840542c440020007611000700e2030b011005403a03501090b44218400041c0705000002c0d81c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 185288048 1250 185286798 185286809
    0xf0c010204121101080115081510030603030e0316260105040309030311062e0902070f140d0e010e0d05060c0d0f05040807380f010803070309090b13090606 68
    0xb000860800545d1080000c0c02450101100980c1c003550950040142542040c803040300da8030440c010f00c0c0000d10190b00d40d1482000691030b80030400416070003440f28000d614084024045404031a569102400e03c01c0c8a100502107412411501c1e40241e010100c0001007210028020340c0741c00e0134098000403040c84201d00041e03158107051460301e800f054150140030309001a014461603000110100601ca003050b05084100040c00261030440d480140b4026210310180a412519802c0c82101060103a101403450340000a2810200394444101c060203d42401c3c40424a004100442c00c0341582c401c004020348546814030400c0404c4401138001c8011019080c01441508045142070356002c0e6402840808148400000a0f6030030040031101d0200d03801d011118040314801a40c2006403003803045440303400205111203075800407036007401340002c20011032400603107580041000c03d40f8811a0b007070b04e0740d902c1c03030b4111030b40c5003001145100d90760002880340500d141400c4000b440c076403088 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 185289298 1250 185288048 185288063
    0x4060312081e0903030105090a050603060705090622091103010807180b1315140108160e0d1202100207110d0602091e09011a0307050c0106150c02030c04200f0c01020412 74
    0x140c2e00080b140034261107032f2805005480c2c20f0b16101800d45203074100c1c2c001d10307920007030034020314020004034000c9003600c41002c41ea2050b044e10b0440c0703400880740c2d169125034004034204018070088900280042c1201c0300e084c092088184000b251100070030141300002d600c0201d40040e40d0202c18a504284003003c50328889000f1282d4444207815601480e8901e41c0c04034500d44000742e48070a514400c0c0e45c4a80396410001e020404003000220440d04016040701c1c03140c0384601d0704060380c0c0e04200c4005c0814840e04211705e00340c250b841d043c40e07129101d80205e125554480d8076004020341901620080c14025010044140750410103101c4014201012030251081f080001401003039841c140c00c00c4204914100d1442d1120442228075901c10301d03650400d903403108000035001214041040c2d52040d00e694403034901e00c1c948100b50511000100c2c0e144242c0c10f1003000d40241d0f406240d50701c0b0304110100e4003991850310300040c0c0200c0c09024250402544041000141013445010003a40705200d200b9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 185290548 1250 185289298 185289301
    0xf060c0e0f03070513231305100501062c030102030703060305060624160b0109060e10050105040b07030e04060e060a120804050907110a05010b0a0504060312081e090303010509 77
    0x505643c0c142d40d124680e800150014243c00c085503540c4004a070a040d408203c0003020301c5c4180440c5094260b4000c1043c050604c210010b2040511420040c00c40d00c0000780306071351520b2070086c0804800c1e86001c46030400c03065410f0000c18900d840c6a070a10300600207640741c3c9010600170b0004c0015100c291018081d10000842601d4004103102684884500c3d4600c00d07148078001c2001a0001e8540c02d2003101804c449101054001e14070743d00806a084021583c01c1c10141c00d01c41c0000060004409802d800105000d181c0e0040b0554090f1103681820350784400f1603003802c94400e03540140160f0804c2c80d14102243c1c15040c2c8002d680724070000c1d80c0320400d07140d441050b0003600d2034000000c0d0034404107100522541c0740c0380a04540043c414034004031042201103025040440240b011111695196000308203400c0020822000788801c0301e08010031443c0d40c60301c8800c0f00d860b852240402549800286405640002c080f103010410350078402c0d5464001a0740da503a41c421300032184500708a10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 185291798 1250 185290548 185290579
    0x170f010524030a0504051f09030306051e130209040516090b0a120207020111060a0c080c04180c050415050304030311040b090904021c0303050105150a1b0f060c0e 71
    0x8461421100c141c9502450b5030703521001a0020203016108554a0103440b2501c1800c001800c030f2258140658640094010010700d006811901070380d011a024211a01e0501404a80d10a91010382581600c0295180130700000e940001c0c45200a1385502c01d152005208242010503403441003c5100d0300c4035040980c50382c0101042c2e000d42032900000070116016030b0141200c0d60044d003031491040c14050001e03400700001c00d081038406c84050b0912941c8220b09010359038001c052540050700c0f8580d0528090a0517445038030309103000300300442c1c81c1c9c0b90020406180d22500490f80207007048110680444051840280580d001f910240c0c006400c1415032404400d01104442c1129000c2c0c1030300c0c0c500621f8009110070040f004005907403091050a034030a401e0081f00688079618407907500042c0300d604040c10402001c03000590032400e840c003405155020b0f038102030400d0100d21703206050149038201d80303000380c64070040c8a0014105420301e4011441150080041108030710205da004000e04401c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 185293048 1250 185291798 185291839
    0x310050c09150415300902060a0804150614061b1c121122030209091501080109021809070b0a0e0306060111121303050610170f070e07170f0105 63
    0x701060381004840084085c0040d802c0481441c1710f06007a1030105580b106500002e00540059801401269800342040100412507000310001c012a1104004142c02d16008400490418401900840d00091061017a41181c1c40c0010110416012101140400c500306440040900c0691010071114505101400b2160081d0305004140c08082d5050500107003c003414101d88405254034594070003030100c00358840c043c060f4442c0f4400001000d070700791520006000b00405a2003030010340d02d00360be1040165168000c3c50503d11b42c00d441c0107165280c40310035904010b055441001c10f510001200e243e0103801034901c1c200107008500707680c101d0b56030400648d00022900e500208a820000c24061404164000f0f0003002c841450541000d076180d5850034a04902600c140101d40548007040201c5960001100e5882d2102c101604030701c045104170030360f503041038021008012002d6000172481842441c01103841c4032200e494660354140384040340340000c402c0c02000e00513001c443d8003245c0000e5a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 185294298 1250 185293048 185293067
    0x90207140a020f0d06141014060f09040518060a090201080117061f120c052403010b030408190e1003090c050d03020c100302180904020310050c09150415 67
    0x2c1c0031004111090820400501c070781d00700888005d80e036068401020380d80d103081180b1400220705541d03001c41c20f24803040d160942e0459030030312541d010890803607000011000e071104c8000036a0082510340311601e4a52008048400c00c541c41e100e8181048950000c41c1c0000c00f00d28000c3c2c0300c01c41e203642c9400c0c2c0541070403c034685040560b480320010030b00c8410b1000012052500100240000d2512100104502e140840c420750301030781c0310b1009000300d03d00b100548241010703050780304440c50316041c0043ca03e400140f080800300440440002c0600c20b0380c0701101c02d040c80400e84804869020100602120072420341113000b2044104001c14083c02441480c0c80d80d034000c4040c1046500c0c1604024180714081c50071002c40c0108000300e1800d0712000c1d00c8103c17842e980d40300540c4808803072462150704038100204070312545982d410300c400350b01c011074207141521584101152a0752003003500402441031066464101d915444490720788190000548141c3d030351042c1d91074440d0329500301150342440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 185295548 1250 185294298 185294303
    0xd0501210f0203190506150316030b06011b0f0c05060a0e0d0203031b0f06070203130b18060a0f020c03070f05061e18011205070504060e0d020406090207140a 69
    0x5946109401089001e40340740e003500d10090840740e1118424120400d02480300c101194180d10103000c0c000780100711103861030468400d40041c000215062040585040702d4032014202003220300100d0070907407091102034000d141c1c0011400090141e0710700782c400046001403d80340725400c08004915454070704201d40c1e00101d256200c010f0781900c00300308150214292000c0f07070f0501c01000400b03800c0b0b40e003200c5922070308940700151007102250301300241010001400001150010080c10307018404220b040000d545680303002e02d407a40400c0110040080041c0c80d0f40d46e0241e0040341000c0f4a0f60700581c1800241c280d6030030307941030207199401d240e5202c01e075010f40000084001030034003c030306100d809000c6000d56884a1012080800002001e81d44061070801d049440ba500d89150f550300044800e2003901035074010130591034500001840390049025480400c44070500101d1a50380c0c1e07202406945400030401c100310355a600c01c0c44001d5003d4041100e10003425142c3c4640540301003034842d035564 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 185296798 1250 185295548 185295599
    0xa0506010503012310090302030d05041503020a03021e0309240606031f080a030f0206071d010e0405010801021e030115030b010302070f050a0501052a0906090d06020d0501 75
    0xf4204100c4c59030300c03000007541d00400d01000b030a07102681d45c1d40c2100e000c940381684842e00c1d43d90550041c1410182c141041006118041004011182c85640a100c507600c15140040e124000920224003a101d81e0407620980410404e0b00c80b800300079180210300841901e0103c03403505d003c01a1a045507458004002ca0740108000090f0301c6050103001560303c29050020002045a0327160081d00c2041036411400f00b681c0f10006000425810906541d21036000c1d0004240d1071604a50040c04408507040750020b03401e00084103006a400ba8401800d00c2d00010000d000543e100d404840c001d421a0320b503034800040e00300e442e000060500b001c8a040e180070a002900300e01c80041306a020b86802807240341019800c10188000c0350341d55242c0321100340f152001e04040161810a5800d40c3c102500000003440d0002c0c040500c549039805280310100c600075029259131010340041c00038010081002d40017000c50341040100000340e0700505000c4184c060410003030343c0313607241c21100c0c1c828180303629000c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 185298048 1250 185296798 185296801
    0x30a170a09050c040b0d0b3108030a0e070b04030528020105040e1e0403020105090f1b0f12060c130f0b0a030207020a150e1e030a03080403140a0c0204050a0506010503 73
    0x14149034010001242001d401b045403903003e90748050001b881124045c6c20700c03070407041e00d400100c4c180040140c1c3c02c807100a044d002c448075803654400b500c406403400211a948031300348070362100203000b020010003203408615210755230f0b0308100e92207400791100001c104502809003040407885104203840300d40c040e981c05050a003040010440c3e40c0010b012080105103503d2002d5600b118071480c0c83c4514801d500111b05800c120300b45a1a201c46032010340e10070b81104207101e818400c0c3d0940e42c05062030448160382108041000301701035155801040d80c140c09180100711080245030010000c0d0145890346841c07996940010003440480f034010aa0074010400050091505c41c0c0c02404a0600040c40c40f103246903290440d0743d210310300307110800c04201c1210803003046140c640084c1008802e00843c041d0410f003080b0000703448001c0f042005041c00009004201858402e10115003400b030240c2c480b41d6500715994025103002c5112408030300c554203200000f21440400d0050a00914040c0c4400e42907 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 185299298 1250 185298048 185298073
    0x91d070e010b1c0605130606080f06130908070503031608010603020a08010e0711011e0e010b030a060c050408010c121b0f051c060308040801060b07030c06091103030a170a0905 77
    0x103640941c03030003000321138032003101142ca43d56200c046200540450030014465240030300190140900410002c80da040d10310800c03941d5101c8814a0b1440c91079444000b07a00c0059103400b10304e602594002903c18440441049400102c1d1404141149029220039096a9961004070181c0c4a01c1007038a0019004400403c410800d80346c0450b0041418104000c10019584a190840d0184806040d03410084559459103811034401c4d07500c044001402404900346920102e1340c5ea10340e02d10000d0903155182c1c4548000c03031260096034080c00c0b010000740f1558030300000044c1505100708103c001c4c03030324095a07030b04408400803940c47c2148207a1030301a509052048162521740224100440900e807a14140900200b03501c2880069481603010f1904c80382019420ba003124143d82010784980401c010110200360050110400964050b5000c1049640d07480d00a0a000300032036034036054400819408545e903089148541b01480c2c4840044459548642c0d102c16185480c00140c07264100102d02c094 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 185300548 1250 185299298 185299327
    0x1206040507051014190305060d02060f0f070b0c180907020606100908030a090f0f050117060301060e0f150f0a03020105071106031e070c08090f0406091d070e010b 71
    0x400214608001c0c10701454950310f1151a4171074104000744a0000f20100d0390382e0341622404e500704400ba83e500240a860342e022864501c03d41702d03210a280e1010415201f1a0310030402c90310b01c150f020f41244a1403d00c44aea4500c01c0d00605084140705c0c0030154000200e05286070701921600c503640c010b1903d92514000d00102440e51070050040018240380840c002600b0402004a42070a50310818120314040712030600721820b41000401a41088040100d607a100d0b000381d51003520384941150944510000900414859010f03103101c0b03128000300203081c00e00c0701c14103224000600e4196403115280081000130500340c11324a44c007013004d1100703201551003140548002c0d8450060442c2e9016024009200c42e0000c0f58005414440007404601c07580c80f00c081c143c0c110074039042c0801d00c1d00340740d500c202c103074000c400f00d481c022180c3d5940d40c47d055403150000307402441030000800810f90b840f51070301103003240007100b030005204071040019003544c4082e03914103d8880403111810010080c04011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 185301798 1250 185300548 185300569
    0x209130504151b080a091718030607050909090601030b0114041d06060a0602030a080a0b1c030e0f010804050d081b0309060a050105060304020a0308131205010605120604050705 77
    0x881c44960a40315804440591242c0e1005149200c0301400d414040c14008011890017802c0030401c41c145a40300e00003480116485001c02da1540c50b0a8580300c1e901301c11004286002c0070540c3c14441c8400707004229400c040101605402900c40000c03d40e01c0031130081e42c0c0c070420712004207a00350180040180c1c403c1d0044030401450018004900c01c01c0c0c0c910414469026130343d41c0300340384c0c0001040c02010716041602c0401001c00c1c0c00610b09014243c107000d4482040101801c00464035951a800a5580c1c4403000d0820b02c0140781440039a030312820001d10032282d4114141c060310382400c80316171642c0078980c014802c50f444002000154111441201c1250003e49104403854003604440140c95034040998032038003404005082a00d0100c10340f0007981c0060f8403003030103244104180005030300c90610300c805032508800c6840e0f5490081c0c400c0407001015522032590780c010b1951190801106411800890303504680c1c40d4207aa0603444002c2d01e40d641502c1c0203021781c1c410441001a03003011031140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 185303048 1250 185301798 185301803
    0x9010f030b060d020708040504050618060d0f32070f0317040e0403121b0516030908010c0504030c0510120e100c0507020405010b0306030d080c2203150209130504 71
    0x11414a94450f090700b050b600104030882e0031407400300e004e104504061103800e5100380110f03450030380001e12a285921920307014184500030340c443c120302400e00000c2001352042c51b0380482c0d0507180751a844458490358105d6421540c444451114001a0040002c1e04600b6204104540260340789150303281840701200e0080030a01c810240070004002c1ea518980a20827170198a5072000c00760f044100d80c080701c080000b01148040807840303901949501000340da41e1481c41042c0700c0382020080c2000d640d0048560701920413582004800c40d46d0fa0b51210140c0106c0744980302001502e515001040b000c80702080345000052030940c40000500074a40210300f00f15412030580d01c0c02d21082c1052001d0394890708815010800c0003486004504040c032507030703004180d4010124118209030000940b6030314600c662408100d1110049550501881c0481c0e24070b40400310300040070304184e249070700d441070302d44002d469011032801035034850030140c0201c1d0341150000740312004210b00050394400500380900203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 185304298 1250 185303048 185303059
    0x409060b0a0602071a030721060314030706050901110f13030b010e061c120c050708150405070b16020103020c010b09090319030209090a0c1e0504091109010f030b 71
    0x3022426103032914540050411603010306851030034071403224000c1001e080c01d90000542042040412a8008042c41400c2403091b0f05c010f0090303068000b0800780180c0c0e00040c01000c0207801052241c04000010000380b403040c103090103079545800c001422241c500b0140f9001100810071000c2c82440540100030342d46a110740d02d0100c40c1c498840ca41c003004c00742c02c1096140b41c010300b402450700e850f001c214101160030500401011007075541034840c2e0030501a0606200c456034524003004020700035000580129030464080314aa1030076890b040c04243d9080c0c078140103055012036025158011180c3e80c400c00420141200000d600440080d032100740d8000342c035503072500558880c0c1c1d01c0c014154050817030003008581f01c40144110141049004107001c00b4188100042c002c50340300d00b103500d944000519800242c403201d444041c0c032250083c0749403910a21640c124005540d03041005001500d81c0c0a000300a00302d6580d07051403607841031035071031400704161120b025091f9100c0e801c01d03050004090607 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 185305548 1250 185304298 185304311
    0x1b0c170a0c0b070305040c080606010c02011d060f09010e010807080705072406050f030318130207020909030703030b010f020307120504120308060f1c06050604020f030106110607030e0309040906 85
    0xd030006a04410f561010000c3e4450041c40180455559a040905a104054151800e0120000e40100901c41009050181c2440161445901b5148403034170f10401502c0700e0342c1d03052003402a0004d41c0c0700745c809602040e2140e208450551203030515a101d01d03201d0716852295210b000f82500c0c10b4000d681c0494121a07400210080031480e8000c000d007042c1e901501144031400c2c04100f0140000d8a23080b00e009034010b000e00c030300403000251450320044042e6103a500c8040800300d040c0c060f1003140b00181d08000c4420a000d42c0400000040c050300703001c1d60f070800004007004011105c40c4600070210740141c0c018401800424580c6802c10000241428207515042d900d890603c43c01d01a0401078011802d42b5040052a003804100b50880d56800c0303441c8403550601d100c0c80000c07083c44140c082d08440e50340300014001e8803035504440024804094460701c0b0342c0e41e0350000b8401300c0c2e005503010103170103a10081401c0d940240a000080c0d03005002031410001c200040c40001c00c0c080d002540d5441c0c4a08 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 185306798 1250 185305548 185305553
    0xf09030304151517060a2d0204090507200106030b180718090c0b0c030712021f1a09091b0a0e0a0209010206010807050a0308030a1d011b0c170a0c 64
    0x42000004003803544c070030002e8061080c451814900020f056000d030a081455003603c0c0c9a612810500c0350b0343c000070310350500b0907440c0004001c2c0120703040610002e02d8203042c070080c190442c920441202110040030310009985488600b41c40c55032000811400e40c81001ca14409940d4601c2401c80b5003910884078a40d5480d50448601f0300b9015240c0440e03581d8464440c24041c8180e0790305d015140040c0a0b40c901100301e41c2c1603a488c8a0220301800c22079040c01d02d5800c180c0300303200780f00e00c5003108410001e0f09001062a140180242c0180b16800c60300300310101c6041c02c00c044500d101d03c036140050701000280c40c02c03d07000c0c54214501182e1015100da00031071a200c0700d408850140c0d841180041c5c80d01481d03400079140a0068010f04110f44c0941010800c40e03403a544250141e0340e0000c0495220f84481c2032500217000882e144080001c0089000030b100e05056200c0d186030203280100c02005a440310060703500801500000d004c5101c01300d03031410840241d10080c10140100c0c82c00000030640754 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 185308048 1250 185306798 185306831
    0x316050a12030e010f0504020d0b1b04030303061805040c03080c010b03030d05071b21090302041802100e06030105091308130f050603150d1502070c09050f0903030415 73
    0x40301c000c03c0c0d0340c411103101410244154134000800c880c00b00302c242402d8000485440302d40340c1c010100d030000c200103190000d1a2a00d60030b0038000a241540b0b0326107916000c0c0c0500054003c0c0b4002912800340c0003111445030141c5802150030815141541d42951103054040d406072104081d030b5901c0b20b29640181d01e003000100614a0b00b00c5002902c0d00b070a040c02000c0040c4101c50451105103003061901007921076046c1c298040d0744410000c640324294900340c44a200c0355101950161070030311031004070481444400d8016100701d590031030010381c4180075525601d001102e1500818244010f00150424000b1a90001c0184442c01c000000d90760341c0310040d902c07003c001c02d0084d150a8040004480d050890406060225910341c21842c107805200480e4400c0c1c4115846401c0380c00c070100c01d100d01c0841c1c000905041240940d1740390b00908251300d51030002e2050310002441c0c000004e0583c15500000350254590308051480d5441f103444104c1c9039014801d102849556807406088644c102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 185309298 1250 185308048 185308073
    0xd021504051e03060702060717150604060f1107260c0d08071101260709080708030c0c030307120507080918071808060601050c2a030d020a03020316050a 67
    0xc1c500c040411031164803d05007007210103004501554440000d015100360488011601c001440280200700c0e9190543c0c01c46640c0f40d82e6a01c1d411132000600032400e00e03440b5203c4613400300f00da215604080e8000b1045550b80502d07210303007585a03481882036801e54144011081088001e202250156814030700058103081460300116010040011801c4c104004a1200c02d00182e00f4240b8200c40c090070f402c6400216020b8158004c03516041c4002117510303008003180e03000f900504040f11503480e21081140d542e944119158159880348100b04000b0f454000701b00c074001603000c2c003002c039030008011007510b0b5504000406c03034070404144884106600c40a0b0804110304048041026034100b40c28050055942c0d04804003034108a031005221845000aa00750080340c28a8400c2c1d603110643c5089090481c21201d100410b55083c01b40810b11100003602d84184108a060f01c00290250b84143ea031100007400050240c0c00034401a0240c40500780e80810b070300e0059066030b81d120000d58440000c0c500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 185310548 1250 185309298 185309329
    0x907051c061229130302150703060614040f1e080f06100b0c210706020309011d0313060e0a051c150908030a0504020102070302030703080a02060a02090d02150405 71
    0x20035031049800d01080c8909280c0c3c0742030038510a20050001818080c1c0c210340280310406000300b884410082510030003070051604151410001542400c40000340900600c0c45a02c00080828696200d604c80040880b011a900d40701c80e01502031911844405055101580b490070414010700080c5042c403e0045004000c214009410545000f200d00c4208071055040610012001d20101c01c00d880009400d00040404170014005044116640100c1c2d2189280c0100424000b00030f228034807038150403008400b1680301003840041c1501003826682e000b0315182011402000ca0100b0800e406810f00e050300305c401900c0c090215440b6004a004c02051240c40f4100c0325018402c0c00a10080e82e80040790490743c1907040c00350302c1300c94444d040740d4000603218031803095440000c6411a8001c019a034000d550150030f44011940d00d06104030303a5000a0005805409a900000c505085501c01c40c1c44061004016410f8900c01d602440340b020011b00010000c00003c110100b11640d64441340300c603144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 185311798 1250 185310548 185310569
    0x50d0c110307050d020613050a020d0611040b030a050f0609040308071701031211010c09032d03080417040614070213020f04090b0d020a05130204030f03050d14060907051c06 76
    0x181d9845001341b820038010f01c2c09510a00c2920143c2c006240030a281c1c241035011111515050140d081807030080c07400640307000b01d21000140c0041d00d50040000303944140c58641e4100300c0b0b84cad50a00c1240320040200e81459010055800190000340140842c50300205580f80c00140004074080003585070b0801e80054800400d0080010040c0c0d600200360089003020038000d01901011440c0039009800350f0100401c1000d1080410b004241e00b007001c0c030741c100c4041110548440f20381c20042e041c3c280603034058070003414880d00f0b070104042203812641240d0051307490061203d00c54404102031303000480100da00903807640e22200542c0711400031303084031041c00740416515890b0003402c4c8125048890f42d10f0152a620782c2110250f81c0302c00300b100c212503041e24400100203445203040000c2c892504010051020042c82000b4154448060301e442c0c5c60410301081451083c01c40e01c1c07040c01d4121403441d40401d580c800a002503110300042c040113890006940148c0c21f00401200954056401124014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 185313048 1250 185311798 185311813
    0x20603071e02070b0d1a030d09060f0c0203120a1107031407050d080a03020c0a080c0a030305090109051b010c380705090d021516020306060a06050d0c11030705 70
    0xc1e0110100c1c60451103941c0000c2c81060f140040208440c0100f00409000c6546c5036030110800f900c0c4440f4120b030100041c140d80c030b1080d07071100107058400b00b40104000203000740c51710b0000c1402420b030f40c545503400600030301c94441c40320642402c0d0b511846a1004201d481d600310602c40348104401005184101d240700070032a003110040b490a181940064801c440d25907002c40400c405808481b400f00f120300e070160356840a41640c628128401000400d82080091408840c203070103d07001695610a80d0300380015150300d0300907426209160707000381150300526401c8a0307807079500141d0a0f207a141030400300b50a4106888e4041043d809407074004000c07075016150b00c4001034450010101e040f00c01254542400c0c041d05c0204540244280c4601882d00c800d88403080d035a030515128035101207461819a00c03105d458080d41c49a04480d000c902034840c00d00410705074940306280d071040d903100740d44903410040790345260006013440d42038440a001424042c0c4025034802d01c02024014002c0d801013105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 185314298 1250 185313048 185313077
    0x80721032d1103250c05090c180d05061501090b0d05091204240309240609020f0a1b0b04030c030e01081308030a0e0f07030c090207031b0f02060307 65
    0x10703216a00201030b81e0010052a415140145640c0030f07001c1d012010312854100e5071a2120f0400081e400c0b10390300c2078405080110345c4003108001e1400f4803a9016000b03009a01c070061146400000790300420b19005840001c403c20700c3c050036030a014105261a103211969451081d4087c0d01100c51021100d13210b10401c04154802c204040e9440e80d40409546400d02d0070240701e400e600c6943d2980900300c80b140110b0584d034407a400074100c4642201160720844021100b400590314036409482e051070801600041c080424801e4840000304011404d1404500c20402c888040440f110804803400312828480429031403d065032155100c1d456090000e241405c2c06050102006116410404071804100110421300780a041541d8071030f132141e440e40c44a0003043c0140848500861061240440d1041da40800040c0c0e981140d000e944090358842d110038000741640301da83c3d0040e01017124840c058060550307058080608501039520b46241c0a541d50001e22a58800c0c0d91000c001040044031111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 185315548 1250 185314298 185314307
    0x1306060201110705030a2106060804050d080702060c070f06020c030702130c050702220903022406030307080a02070f0b030604110703020606061e1c06080721032d 71
    0x50015944881ea0f080154aa8550b541da109803a040010418801d10794101d2808002c1d0181d6152103600e01800480d840340301c02041c4480440701520503200fa00c1198908034011010320f809650941d015004658640c8500e00199100c400110f07071240d14989220049001480905502555003014550b907085c1e50040202d414100c4650507951850b00d1400c03003406800c4001c54900d29415590b1051241c9043e85030b4000c98a0142c004528908180301481050750203da01282c01c903010f110002400c2c3c2c80d00c844080c9a6007140d03641d03050b81c4100700b8880820202e4010f003035000668411104400c0d1903a42803a480d40c0c081d031000f00342c0c00303001c824464030f0301d0980101d00450002904d014100419510004e5440c1c03005000140102e6000813403e030b03000e4110103105800018035800c0740d5038804090010000540456003640b5072440d01c200480c3c1c000c80819a0760032648107d42049180c460a101c0b525000300103c0c0850038090f403000d00321034912030501e40d44003c03400810082c020703c000d580040d2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 185316798 1250 185315548 185315561
    0x3061608090f0604031404120f0204270b100b0f030a0b0108060904060506060d020c0c0306010e01150f031508010b0f0301020f0d0e0309030105040c14010c0b040b0a09021306060201 79
    0x40e641d0001000c1100701500001d5280c0c4c00b80d0076103401d13080036104d10001000b92286410151040ca40c3e10121018007054164000110b40b0070340741000002c1c049590524894040b12440c0c00910b0070300054030204206603500f9402540708020404815071b10501c101d442e034001002c0007c4010084100302160b030785480b40d04000b490a0a2800c050f01e05080004c0c0803c2005100030035440c2e0751400b01d003068403443e05407048441802003c55946090b00b040595600b24604164030034460900042a12140028a84d040780c0c2e6010300300d03041c0c3c04502d001361107a21031840c040040540d505d820141c0300e101c2e0014400146494000001c08164440034400140180055140240e00402c25000c9244c03443c3c003244c0152a01c90000103202c0e100d0310301e0300c0c1544156500c0e1641982000d040c84248040d110000045944201a15540010030801500c000d101041c02400c0581c1c070100040c00b0a11010209030b20238241d08001a10881d00c3d400200261040004042c0840da05c0405200064091250701c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 185318048 1250 185316798 185316811
    0x150f05090601150807090b03130c0f090510031707141501060f030b0901060c0302072d090902060d091e030201020a0e120705010c020d06020c0d0801050418110102030903061608 77
    0x15164035100c4c0d400707444100300741f0424144280000004d90b1074403000c081c0010540c0d01c42c0742d0000041c2e44081e201c2074440c0d81d020f003102c0140b522010400710107182c8011012240d01001071a207124280702c08401075004030005036090710501c006100386820a00c0004044280c62401c50030550520000615070991442181c082c1481d000c40341c0210781e0742a0303120341150315900d000802134845140890908450780d100580c40041c6021180e2210710039542087d809200000d1104e12507030302e199000c1501c0030703080042e4000f4020054101c2040c40e80d0400d40b982c03030260010070016000c242001d424007548175030a8005035404a00300100c2688130800000d2003004890301c030801d030340002c9541d844e600548141e03070610140050b0f110442d00e401d0000318042c0d070459030444d114200d180c0304ca901d455070f45d02014000f99642c1c0010420786040c3c0704599034880c600b8803285c0c40401554942c00104280780300b850641c8014008038006a5080207442d20541c600410128800b02c003000240101202a114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 185319298 1250 185318048 185318057
    0x4060f020c0703080306031005100614040b0304021c0f03021606030c0e090403020106050604060e0901050a031119052e05030403020604030e0f100e01080c090d150f0509060115 77
    0x2030341c030140004120701074a401124084da6500d410000a1409030710307213041941c1d00e003031408105803108204c0340c1004840040d00c4440c4070f07680006000380c1d9440b40b40608ad428900a1011030090308100891000d84031382040d400401c03c00c9912441041520108210016400b09600c5031280355510010001000907003018003500901e004090a411160815540910000000602850b100750050002090080c20142e60341c0d4446030000c00d103003950500c0600a0f10a40f00000d001d082100000d41146c4d0816182980c05e040740080051000044040c8403c00c144030300081115aa81142c440d00d039110040d48201d82e00440380002200043d28410b03600b404411320811000c02d0300460001d030f01c60f506142030140155907030f0002d00c0e02c139001e00f10140c1044a44994505e103581200102070341314001d0300c650006589036140c103d864811010b820303821181d0000c00c0d07030000b501009001008004200301185400e0b04415610888600302c85c01100c9600940c0100080c05000a201190701c1140ca00b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 185320548 1250 185319298 185319307
    0x20a0902090307120602120702070303030c02120703030b030109020a06050702031203070e01081008060f0f0f1911220e0f06060301051e0409080c0706020f0a06150e040b04060f02 78
    0x2610b90f0b8107841601c80541622000c00c040000c964103c600b1f00429140d0300c1c66038182140029522001c500080703002c64500220303490082e000140c0302ca465a40c2100c0a0700e440000c0e5030850143ca849004180c041d900d0b0298400160390380e0748030030040c161598600d034840055004140c80d00e4607480301c0c2d00f24a80104140301c0620760107204116007200030300b009101a1140c80030078160009585c8450024003401d418013028990421060703000300703a0b45140200c16191055008180401035032505e1640381c80c000140041060754112980c40c802605c0e14609002d038190060a072400c20718111940701c06030400500044000c08119034000c03024581e001d01500d0510041403440c80180a03543c4100f074543c00d036070808446028039103003c2002410a00c11034040c0d15103c8116000200d00c040c45014038100860080e00c0041d034040e50070080401481641880d4a524006106c84804000916101140400d00d1840c282d2628050361244800407035628040c00d1000454081c0145425118010030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 185321798 1250 185320548 185320567
    0x60c09130b0d0813030503040803030601032d0e03090925020a0b0c031504020d1406030c010503010b1608131d010803030a05060102102307020115120501091509020a0902 74
    0x9041000143e8031800c02c5569507018040303030281c0881e6500050292000040101340784202001070b60083d07400ba2000d010190050220340d141c000b01c5111240709407a41c0013920003501d41504800c0e811001c000c252450400e16001154081e02c0072500070b40c200500c0543c3c10200800050300d0003214841d480039040c407419a07038940951910207403c0001514012001c5500c02651140c0304861200c018021035803032200c114000085c01004000001500d0208001440e605001c50350302854941655550b14503030a004100a240d00a0040c0c400c0744006140205d000500c10001484a0756100c6030b50300710700c1d02c1c05601d59200c0300718401500d1200c03505001004580b4001050701d420458143e0089440d584001c0100d00c4d10707481c0007076614500e040400c0d01c1e1400c02141040c5072000b5214800341265995010180d09840103440c0326203004403010400c000b10340308144c0f030350802d41c0310b9400450103107896211480d40d02d800d0344003140017030b41e41e1240d07000f145000703040390f030050140d49070940c00c141c03141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 185323048 1250 185321798 185321809
    0x9070e10031b0914090609030a1704060b060f0301140604120602220915083004030203011406040b0a080606010e061b030a110a020906130e060c09130b 66
    0x10300c4014100300120405040c80b120044050000c2d20102d4820014200c80c07010f005280c21041e00d82c103000e4065074022071254100841201c01519243c1c66800c0d410040c1c4920144120008105855942e6142251891591880000c01d0055806040b650701c0394140150350358561803640010b88582c0080100b081001009002444000c0e088507005840300c000c0c0d48104003000403034154450007886200b02060441d5554017504181d00d00b41c0004100b941c50f10340c002c3c0e0f107641d44202087c0d111096074010f012040c07614103c070000054000e2280c1840c0d640d0b8003003420b507401034400c08190880c0354100902d605013803140c1c40d2034100880b84041180c0c901591f05440b4007025100c00d0401558803e0122151140741c00c40c0c400501c5031229801602c6a428501e440f900071502c1c3c400014210550003608a5001901090003500109010901c0d100c15040184460308000e20440d40d90b00c448004004000074442540f19a4001400d40d903145020002c2100050060444068852802408155075204e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 185324298 1250 185323048 185323081
    0x60302090a02071b0603060801061d01120f081201030209090a031d01020102040308070b0103030201140108031603110a0302071e080c0d170706060f0b12070309151409070e 75
    0x22101c01070380c820003402c19042072024504002e008200f02640020003d60550000b022510014020882e040d00d5651140119a00140382a18400d041c001030000f1360305200441c960303500c906413005000e011541e9042040d0460705850103d0101c010042041d800e100ea81d140e405140c0300f010308a0f030100c542c1c014140b40c41a9503107541400038039200143c2079000358100c03009140c100c459280c4a00707081c9008540140d00340401c40c010b50030000b03103456000f400e00343c01e0b041c0e600c400040c6003020300202060032825410310081c1c00f0010b0b85550540105024864400018001d60207021214200031484001038010711b940145a0200c00341003241d8800443c1091052000302c510f52024001c03405c100d03a9654188100740700c3c2e03000c005000130800c800c9504c0881100c11080d0300d4180f960b600d01604506c0d02912108008c10200400001d0003a0310990201d640c462090140d00703002804000c81c50111050300e042c03070138090a050705000803140e04000d280014406503149035110712b401190105944e11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 185325548 1250 185324298 185324311
    0x5031902011709011e050907080a0201050f160b01030501090210050c1e0a0204021306030b010518010318050106090207020f060403120f030e0d0914010c050d1404050616051006030209 80
    0x409a001c600c8100c820f4000121110001075a407205e0401c1100581c0202810344242d40c543c8500080000c0300d840214440c045c468050b19000e0a241c9400502601d580c010302c8040c00d00030961540c200011b01ea105841d010b14003890000644406920603c6070050340c3c02e50380403d1203070a206840d1905000641c5030399215108209052460b000c04105180c82c202e441c0083d805070010904100c9a81e03400b0807501282c1140e9011f0011650100055a852150b45060300481903800810040b039401ba0b08180303c0010800240092036425454035821550b45d40c000e8406250006000d409500d003c0480e40b08140040720007a00c0d05195035520581000306030000000d018142952031002e50280d84031440d40300d0301c07070240e45066051543c0100b01c40380c0d5004070751f188036080d000681c170b9503c41d5040541403a4004000c0010802c00c55041c2c1c0c2c9a940182000c51a01d4100710108141e190f4401400105034020032035603003450b03245031580c2000d90711214032120515043c810009030361401741c8143c1094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 185326798 1250 185325548 185325587
    0x3080418060308180102031c0b01080c070b0c09131d1b06040e040f0b0708041403070b01050103020d4508120a020705010c11010c05090303180303070203160503190201 73
    0x13642d040040c2d0441c0035001c40103000d40382d8540d110701c980318560000610321000341d03900c0c20070380d035000c00110190080200c00f408483d1f8010004030420b011000034541c80b24020a24480c0b4055030318508140c0e6141d1042007041c41d500282c0d00c0d5261410003035942e0460030140e6004c4510504c9020882c0e40c00382d442845c0e140040c2c0d0001c2410301c0741c082c1c4c40c09031054105030007195514010380003400b490780c1554222000c0c40d05440a843c05800130041d00c82407035100398003210b1646001d0044010790060340d66040340076562031114590f220030846888190710820041480078615510400e0041c805098240000701010b03000800207100e070040740c0b280300340001c00c89070689030065918000c0c007940d00010300030740c03900e403a042c4001c1d0400360200c3d0302e001100c024007440c1c0b1640d104807001e001d42090785405600c14000011a000c8612010613a6980a01161704204080e00040c0c94000d480c100c0c2e02c85000d00c10004c0c840c908040c4004030a03003942c948949018020f9a0000b8101d00000e4050440c0c00e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 185328048 1250 185326798 185326837
    0xb040603200105090612011404051608092e0c02030903070603090c0e090604120e010219060e010c0503150a0f050603040212121315080606071a0103080418060308 71
    0x50380943c0c01c0d203140500c05480d260b15103103c014101080078003030281140640c07220f441c246103864140101c52180d00c030300040c40e02c50090005d0503202690064101d20150180e4410300040300c0b503100180320a000e820800800301c45109247c641201c041e00030b0442150400c02805009450000c0c10208448141c900051111403904214142040b03507007100284442050034803503d0003001031b8081c0524081c2c8030b9403513801807441091f5100c00e0032450003405a0412440c9010b508180c0412440040c003511003c100c080456405a0031130f00c615081801080e4007109203d0003000c0300ca803024161000f87c40c00c0039072500b07004000040c1442d6226083c400c0c039000000070110340306c030320560000d1a1403504494580002110840305500185d48012045108007000114020780e5540c07000c00d01550740b5904c04d20784a520501c80ca903030151005481200094140d840c2c2c540b214046030b80214040c030030017600d0f281810f1916081c0001411000074040c01d106060020034001d500300c88041b101d241e41028030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 185329298 1250 185328048 185328113
    0x100b040605060a2a0c0e09060708060a06120e03030103120809070303080a0b0105211f0b12100806010f1805061e0118090906060e010b0a2d02100b040603 67
    0x4e20744481c0c03009244078000307040080c103e4010700c0030a01505034901942e40070b641c3e10200302c80040c4101c0b101d87d444011180c08008490142441e100c1c4156441c0c001708140c010221344ca4919170003030f80222110a00426280c4045600549594000c0702c0b840141803214550f031001460404081c161003549035550b51510140d80c00780e021101c0001044051308540d05d440410b80c1140311088034014400c081c800562003081000075541415600201d00301414412030b01c0361000704850051040c01842440c0c14003103007210080105034024080b11180030401c03402d0620389103161405404030685c9504040038062241d0f16481007484060b01c50017080c16454800004a50a82d0b400354401c0c500400c26101141403119900000860390080c102440741e26a98950218010070900c00c401e4095411300c0b40c1c0c941240308503c0440b01d01d500422030b10f00581c400100301107145810b1040400350340072203100c1241403828010351007401d504403000c00c11a4510f0303ca5421042090040142c1c00c40300c18003280c1e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 185330548 1250 185329298 185329367
    0x312070318021f0809010209010c0f02010c05030408060108120406021b13151d090d0e0604050907080a2007080d1d03040303110c0f041d100b040605060a 67
    0x10180d07002480c40072500e5a0001c040f00d14083c148514002410480020b138150205000b01e50200d101039503201e5403e003140d220310315410240c29040f41040460300700800400d0007000030384064140880540031035407411030f60740d2529040c0710032507001c01d00a02080200d070390082203070915658150340401d10401c1d0000010180307103600c607050b00752a1605003504101d0300491900c0c810744880320002ca400700080c0185525640085502d40241d521816074404003510030403004585210103003505080546400000320302d494100c41440004000600300181000e01d80035940300c10001080c480844000f824002c400e03446895400360980d6400101041040440c2d03102d050f11440c41c5038080712689600113115103d501912040c6e0018040d503900700f040e400045002d20030290010300c1640d14158210900020b00001000b501194000001c840c40e41076013070001001100116100254100147c0108002c079181500414004e071070505c0450031907608140c87c28801c100410801110200b5a4660362 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 185331798 1250 185330548 185330591
    0x3150b0f03012d0e0d140f030f150a05060f0c1c050901140c0601030627030e041d06271c09050d02030a06200c030405030c0303120703 59
    0x90309586443e21507241d282e0400c0306140d0b032000d05030041e20b11404103100d202c2a40c049818900c80d54101d46520400c40d4041c00d1040d00100004942c1424174040c004010004d4104a0703144c410f03034844108001e40c1c0c8030f401006c1c5d514040c003290300e0000c081c14100815214060a00e010001c03c000144a0603011002c120b1010450605040c124103402c0c0c089004019411220101e80482c03140e801d100414007508040d0340040c5400030041003640e02c0c54607184043d1000e1000300c0b8000034420162600c00031001800794046009848000003106401c0500048861849254003070a440c040b440d01c440b0004143d05422400400000ba155400505094280d41e8140304030392051048250320003e6401044860310650165140c540300c980c2d03240c0902410394210030009516030400400000042d40a40c0300041c920342540c41400c0c90b121852042a0543c00045058015800844c0402889c5010001c1e8001440183c0256041c008030486000481c00090001c505154885009541e0740c4c401c8901d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 185333048 1250 185331798 185331829
    0x3011d22031413080f0c0a1202010f03020705030307032405010503242805040e15040804050a09020c0705041e020307030f02030f060f0a0614030901060b120a140103150b 74
    0x94152980d1a2411540c40c1305c6215501d00c90301501c00b51b1a202d190140c4014101c2e0826650000611800c0c1d00440b03e482d265400c0206055090080001180303080002d144100341c00c4c1c800103080c24a0650001c058102000c08000441d203d51007803110743d81c4901074a41020402940c1c10307020000401802c1d00c21070780b1079510340160404031120340f913000c08206007400c107c00344c141168094407101400240d0310025170303075001544120303064101d45031060911503009000c1c03852542040d807a940044d1010350030b54406400b041d0081014031002c8001c0c01201c008090072a0100915001803000400d942c14030594400825404000580c10f18060f0b0088080c1d65103c0e08219681d1034021005002c41c2c1d002e0b035110f801500c03041000c00a83c200a0445000e03506143c4500b03002c420264401c21281d4401003801e140395485640004241d10301c48042c0116074940c03002000c85180c80c402e040211611306071050050710b0803000400100744001407017080c0c0c0c1041c00d800700d4040801404541c1c520b844d00400c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 185334298 1250 185333048 185333077
    0x31e062106040b0c090f010c03120c05040302010809060727081006080f070323160306020406020d0f0f110c0a0801020a0201060504090c050f12010203011d220314 71
    0x2120300620001ca48244100e10580e40c0b205581c07140350f100810b0307000d03801c1425003003042c84205415a45c054102168504c3c40b0307140c42c002c0091000c84550603124206402c0d4041800030406008640e04203101d40c0e400300c1000c00400d150b14042400070402180081000320780050028100242d040406841001d4000542242c0c060101640100e00910302e5104a0301140580c100251000c0408070b05c80c030440e60030903902c1c0d0b00d04449400b040c01500071442c02513110710a903420782e00e0040c0b80d90220760065009240041c0c4441c904030020381400480c401d02d008000c80f8010881a840d00104030f81c000c07a0301d52900c450000d269501c00c910b410040e101e42d80d4000c604040024213020305400a0102d46280ea00174441a642c80b8241300503100c01c40002005a00102c2c0140300f14141655540000d0400502d090801008022180d08a034000e821000c0d0054424081016103051001881e40040100f00c020b0721850030102849003410040400404100d09515a04180d003200404e4032550318610b00c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 185335548 1250 185334298 185334349
    0xc08060108071d040c0911040306110a030b0102060f0115030e19050709020711060c120a050d11040503030d0f1b090e0a090c1517070e0108060303031e06 67
    0x3045541c1d01400d10441a241800c00303e401d4083c581600c0803402107a02840700c1c0c0009062810344400b07011450b00d140c421036010700c00000800c3c03044c007900404d1001c01400e65980c28502400130191420b402600d8150360140042c00644030035112464116410506038405071550322a044001e8002c1040e180460303c55450550b5148107405a6407281c284588100c6054507594150042603018940c0c01030052108048404040d040100c0107103039404920b030544241502c400a0080c85400035203c0310001080440c1c8500c001400e442007501080510114900741881c02d000240ea9102c1c0e40020300078591a6159100c00305219044810703041003054071101d03c4155030b0402403c4080c00c0c032440580d0b0384480c02007006404540705c1c00b0809034100c100e070620302d8102401982c20044074a18902000814100710001c58005180c407030107100d1a58a40040d0009203000414400c5c0c0500074610a400c01c05c1401010741020020680068060a00c91000e544140c001507001c3e80c02141082071519188 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 185336798 1250 185335548 185335559
    0x1905011706010224070f090812160c03081c02070206090d050f06011701060f050d03110c04060b030405211806040f0303020102031008011e0f09051b040e030304120c0c080601 76
    0x186140705d0341c402d50b11003001d40c5120404582100c1e0902c14088280c00060601d61000304480003880742c0c114041a502c08801e40e035850703826156280e0300a48000c4004607150706401803240840e50050303654001135040071881d8000482c42d20410080303074803842c114054201040800c1c00b502000f41380750416507065681d10036041c0c0200310b0240d5042d40c3c0c0d5290105c0811448600540c080a44401503ca603003003205594040d2408046ca181c440300740c0c0724400e140b081907a5603010b2100a080c2e01c9000d50b45a050074504185407614091840b4085401c00010300480398220701078070300041100300d10024010001c1c02180303941c452904800101c1041c0080842810380540066004016410800c19410750f00e0314102d00321802843d03100020a10b85940e070f80041c1d4250080c0c07541003202c02c000030301403425607602481c00d03000c0d18544220044003480d01e400c501d000d00c038a284405056002e1451407a00307986900d00f00c0862401c0c041444202103c0405202400304940e01504284080380c6807561200c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 185338048 1250 185336798 185336863
    0xc2d030e16060f0f020a0c03080304080409150302011418040b21010e0601150801180b040e01050403090501051c09080903060403020c100c11121906020919050117060102 74
    0x12900f18040703001c0c900261300e02840012117980c0c040d0410480d560b407604503a220f403613a6001a0040d11441024400462405c86e00c0c810711408005050408042614510000d00000900001c2c0040343c2028081d4034500039803103800c40c40e91001124001000090000099642e030441d804040300c0e501c2d080400f40c4091415800501c2e00ca11001c00c94003160307a2001c10340d5101d1210f01741000028102001080221455071607140c00c0d5000e054049075440504000c80d040b94848244189582e440c1c0d424070003415080905100985400c1c40c20503d800303000c4180c9140303808070403192251f50b9030b22400748051101381b109550001900030705642d41410107041c025078902e8488280c600c65009510841e02e018001d0180d1103203158040050400c9145013401c001000c2420a0346051600500350404c000c40704412155005500c14580180c81d4000740c0b050141501604c81a807510445036081401240e80040c0041c03000200f40c03212480c1d5070b440c0340040b41001005a500110203002c1b428001e09442c21 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 185339298 1250 185338048 185338067
    0x10e10140f07020f061e03041115070605010510050418060f15080108010203040c050409050a1401020a0e03030c0a0b0c070204090c080d030c080c28030c2d030e1606 72
    0x31248128692050342c05c1118511551a002c2c1d07819009449420380c03c03005801960344240150401d0002000306800300c0e02d50040504c6a41d180480060319504100491103440e000d0003080d036002da405c0507100b0b006401849140507103045465852510480e4100c59040304019019580341d01c10260707564020a08c0a080300c015501c0070032901000802c00543c1482500e102d19085115001554608014800106040601510140103402d03400c2d02141d03840b810882c048031190b00040e602c3c1c10b03c0000403e003039a040b00b030901c642c0040103004400f0318009110756040340c00c54a5407480d030b100c1d4001c5070424841d5400080d0003d08141d039003418440600381200843e8511001e90301490110242101100c03070031820440441c03014408101c007442e810b00600030504444c0304485201c5090b40075000d5005903a40b00200087d1203504904100e64083d0340c0a1060010060284220310f10034411f90f424481004c0c03820801d86d4801003d00013003000c0041e401c03007034448601102c0d11501e461004011a00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 185340548 1250 185339298 185339303
    0x3230105090a1131090b0603040b0a020c01050c09012010181b0e010504050f04080307050904020301030c08070f0b0405090709051c0b06030a110d080421061a010e10140f07 75
    0x16001490007506e018540c504800100708504d180e07910340d01e0f14405000600440040340d800d000c1e0443c441424411540101d01d8006941e480701c1003140010b014520110388003142c65026400c0d10f0322404000740c03107680c00c140d401d000f040070b140110841303c0580c00c1100203400305a8080020340d00c184540c840300b003903442000400300160380320381c180800e88006480c41074210700d15500140204bc12040616000080f501d40149031921b081d0000741079030802e80003a62a40b015410400940c6000c000103401400440710102c030351483c140d03107210940220b00c9081d0003404400c0c0051913007442862004094600100070044c0c43e1540c4003990301742c4c105550110b40308a001c8011803800e10f070018100d02c08941c02207001443c00c40da802801800ca1343d511084501903405c0c800860006040c48011404100240c0798003100701442c02c000c410b44041040c0804051071600c01149030f0390780040d41c80510101aa00d22008030f150303080890300310741d100440d000405000320364030070701180c3e0000501d545d60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 185341798 1250 185340548 185340637
    0x60305010e0703090201120504050102040b040f08010605010e100c1b0602010212150a0303050d091208091006050906090405071707031703100e04050a0204050703230105090a11 77
    0x5482c40001e0b81168980d0340040e0118961000c00010801c041d04226401407141c00054203059031148529901e42083d0004013104c400d842041c06200c07401d10035000108400d2800054580300c0780c0101c0c10b401420384030001004a05803240382400f01007981c84140005940b03034901c1043ea0340b04024001d4000070000010070030b003840452202004400911203c2c1d0000740a00001c0c0e04e10395040d0b81c56031218079881d40c1d83d42ca03011100c010604502507044038000030b8171a44005e2034144509820200c802c400301c400c1925002003400326850350291143d0110054540568640351030624610b040003170751084d004480d1000c41d001c481c3e1804954002180e100c0c0a0141c0c17030030402d060f130781c0b11130204580024180c0f80e01c0000304010500b1114254001d401002a520402459004034043da002200e200c0007183e124280803c6030b03030301d10408000343c00e07080f00000c400c2d5041c40c001410145000d8810451075841c1c0006400f41da0048003100c0d0114454003040010b8117108800400d6003200c1680030207400d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 185343048 1250 185341798 185341801
    0xa050a020d0e130c0309060c080601081008030316180f170f120708041505130b0a090303030b0102032106090906090703030c030e0d03030b030c1c08070201110601060305010e 76
    0x741c000d9001c812802001001a41c0982c0e031503050100406540d0760340380426890385060804174070346104070519015141e850301414545440050103084000c0c0c00070444132280349003000041c101005403908200b8444c0c0034000341d60a11070889481f5551100f01040f141403140c0000e02031040c4010328112001601d01c200c2c00750003a5078403030701d40011210303d41c0140c0008003550301058012008003034042c42181203500307241d00c0310a104000caa407901110049140000c001944081411400c07008240c0351800910f40560220028910022440010b06150f250b1070380c00f0290380203001355418403c5c0d2140400240d90b101c2d141c03981c268010f40341140200c00040100c1d24803840441c2c0c11b4451810700009180162841d50100d401c140c0d070341700030340802418500c07541c0d507aa01c0e20805401c8074040c2ea030120f55800040109400d022181700c04d45c1c4200540c282c481c40d00300100108081c9580c204206c19100c03525400140c0e255505100b42c200703580203a00010920b0742c0c0542c081030503074488001c5001c55 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 185344298 1250 185343048 185343073
    0x30c071e031b0203100e07150908010501050a1401120e0102070819030603021f0c0b01080a20030712020607080408061609141e0301020307030207060b0405060f060a090302060a050a02 80
    0x402e1403801001c1d425400107420900d8009040d0044030b40301050320210740581e079444c0304010781090076502da4400034050707030400c1103075110900030540940001c4840c900718900e082200b8440020f078181d042d041c040090310703161600203190f105519480e1010029545e0303a01629000703107030340d0208116030b58840310981e50081c840d100303121390f000751380e8050900c481352400d0700070450540701018490010000c100b00100001424041114024a0700100070720b00480307686410840c0202c07209144289105650202c2d015a0b030008058003116846940541142e0150011401c148138040010f00b020500040018403080f0001c0c110784039000d0030ba0000340e1036000302c1086038030660a01c0b4051107000e00c0302c0010b00d075103041070024000045026540b854042c440c0046030a80e001150214042907000c521030040c00250b014041c200d07a02280e080040f440e00400180000106101c0382d8020940415540007407801103801001a40e00180031546031078078540028065480b8080100045c013072002035a07074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 185345548 1250 185344298 185344337
    0x6010e0a080a0c0f0806310605070e030d05041403030702030102030403090e0f090d051c050c0406032d0b03030c0604060f1415040f06050d050109110306010f0302010302030c071e03 79
    0x20380708140090328071a192a81440303603441e444041c52008041c1c41103100d07040c0c0641c8540307c0c1d00a104080c0442c035441c15140103008055610f094901036082015209080c5d9408011102515100c444440401d1548001b0038a907010fa880001d40542c800003d010615030441c01800c21903200346c080d413005a40d1920100420707041510501140ea10060b0b0040b4914040c2c0007034440c51801c1c655507030015120f9180241980c0c2d00791020b04c4501300001d4284003080d8540915042c5c441c103840c083c4001d41009001500049810040c0c0d4031295886880701c034603560038011101c0d0b02c071011084400504007401d01500500b08906905980e6140c2007419550a100200f2075101d600c495840006610901c01480302525a92145404aa50f070b08404240c940e903a48451010304d004000005038001d09207054400544654002c80c440d611400041284903141018081500c0d420720300540c681d100c80a15111a014042c401400e40c201e00000315060345810318a42d985a000b9602d0060541c12048682d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 185346798 1250 185345548 185345579
    0x18092e050105100207140d06021207020c010f140309070e0c03010f0603050105060a080402060405060403061e110703050f04051201020706050a1503060506060d14160e130506010e0a080a0c 82
    0x1009070b0400170080081d0005a9a2125120005400c81d01c070a126569404120b901007000d04021618030000d0066595041001c00280c5400707003001c40c030110a000000d410849c1410f110000b0210000000b18681c0382440641e00800345500848580e052161030540950000d004d0340d85803880b003034800500c00f4030038000c140c100d5401034a45480d1585808089812880003042079800c03810070000085c0580f0392100030402140140740c001000001e11920b041c9000c080c25050403842e040006035105800da04040710340040d0b25080290b03640c900d000303c0c01007500031503200a5200d4441c0d05051301702d950640040100d01d20079403041126681e20281c1c9411511900b110810b4046041020300000304c0729030142d40c001e04014012030410f0300c0c00d48000e080d2600c145512011152440c180580000c0c00b0064814940071414403000d100144c01c0841c860240700044001141d88450110304282d000360713852015118050800c0c102c40d500d5540740c0d80c0e1844000c10448070007092a030b000402c03031254202003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 185348048 1250 185346798 185346829
    0x8070e0924030a050d02030702040b06043b070905041b090911070803040c031a070804020105090409021305160815040209031e06010501030c030203040218092e050105 73
    0x44403980e6400c81c502641c5891003016a800d841040c4898000c250200701e5043ca600c943d9004503560b00680c4140416030310b0003180309009050500c000e020410801c0601c0c0301044082c010b90b601211f8481c1c010340407040240052030040c8d000001e102d40300341c1c800d402c40241e03001564180700c0c05141740640e0314000015120708000031f074050300600c00142e09410141c2903003d030513034031420406d0382d8030f504074168000c0d101140d01ca10703800070800070040d4045400c04c1c21400086009620315054101508441c40180003d041010004602c24241c2d940c1e40654007454001d0012030f1821011801b079001440142d032451015103100380c10060351417080007501c1c030030702e0b03003141e01c8208400746001c3c000071f500095011940b40c0250040215040c07540c45640c1c8146c1d055000400144d4507040000d012251038160310703410540100708120250f21640c1d407054809924807400031855892070b01440c03c04c2c2c4480118415080301d8144400c8082d041d10380e5000d5800020004c0116907079a400700030195070803060310b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 185349298 1250 185348048 185348071
    0x30c02120303040b012c0a09120504080a06050c04030f060b01020709150e09030f0d06060e09070c0f03091d0402040b010504050a030809010c0204020c03030403030524060d1b08070e09 80
    0x43c441448030b059400b5003030584c00005c0140c1c2101e01e00340c6405a4040b54031440007648c03085900c0500901c603131189403400160030304d20303e803505000209459201e60304002c0c00c03e079103400124020341c51880c2244c00858000c0418007040e0403614140340507100d01c4d62032034014400d0b40310102c3c440549104040c004810184c1350018a0b1410010101502c0000e001652502060106296840080000740b01c0c0e800c4450b80010300604180c4054007910b150f880342c130b000312070380780c1040403803070b00412031030483c58102c44100440c0740303549001c44450700310350001d044100114024170000030b9076031003660113203100311014000c103505030700119801e0046205480d1b20240f00c3c141000450404e82c0281880d2006240040c610419030f0042410399001c082e60354a551f03c00010001450350600c81e55030004545020811a540806d40342c1402a40402075240b091000180a181d20030b002c0d07000407401c40c9081400c92600340d143c04040d040d4841140e1040100b44064070248240c03400002851160f40f500740d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 185350548 1250 185349298 185349301
    0x120b0a0302190305060f04050730020a030c0b04170f12130e0f04030f0c03020309010302160f06060303090b070503180f041104090606031103010501030510090504030c02120303040b 79
    0xc020201c1816408a0b0440c9451100400440c20510816100b003440190f60346690515140c91442c0009952107003031056034000108511000359805968400070405007842c07043c03020b00015070380001942c0010160342410b0700018001550304098000c07241c06070383e0809046003030400f280c1c03102d201120150042c0c010700c000f204081e4080e0090310a1415003c200c11106031200a90a03800b44240c4e00b080342c0c010400200030030141d01c1800350440d07031441e10b01806810500d560180d6240500d51106040c03603004180b180000d10440700c0c0c45580d030340040d400021200b160801900909440c00260001400010049004200d010884419550000056203030588000c030100103d00a02e4155a00003210721840c1c800c1d81d02c0e0b008400540d08211304030f5640c2c0340742030b0f50305045451550026007490f040c500c00d500c5a00d0390f001a00e04448081c2400724040e80c88015010a03060070340c1140d2036081c9000c1c140024158880120080d0a100b51650b180300d06580c0c5542d5941d000496008005c0100c640 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 185351798 1250 185350548 185350553
    0x90c04050606070201230d0b130905070905090c090406140c0a050f0d02190315080f03030406390219080d110d060320040e060c0f13090b01120b0a03 65
    0x1c1051188100704007040c05030a0140c00340d50b210b034005105011f45d280ca070400b04d203803441c1800c40d020422120820821056000c0d50b80e0070340341c0741c01e4401e40d1066507440000401c3c942d814000322984900042841d0031038605480d00030014602c40910090710a03034540055a404c61183c2110300038015500d440d030a003000c0340741d9080e0690250b072104160540a0003044401122a580b20741017140313503180800d2201d00800c40030040302460340025201d910410500c03580b0000401200e4001d5004200450040c00c8521992020300c16800706603500b024111000c81c0d005040300202d001d4140b10303400d94005007a040c500c01c072214200200501b8050007040420a0541654000c4400d02800c126450818203a04149002c81d0003541c000c0d81e5560314410040f9450455246045199404030740402907440d81902503507480e0402001c00706180e00004412040800000641d4020901284496070f0076869141e000080d0105035082c50126405807a50b96107034900c0d002d116480a80904188017062564 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 185353048 1250 185351798 185351807
    0x706030e061f05150d2703030e15040c061202030c0d0207030c1407030b0901021201050108040c0e0c0c060901060303050a180b03130201111b09180105090105090c04050606070201 78
    0xc0c40202d20705881e041c000500c64551060806560440811071500c640b80583c00c0c10a84030411300da17010703400226920138009201d13044864882500351500061f000582940075183c1000c41e0555000550010200b0080200d021401000e03141c075962000141c40c51075102c1c40c20b030300040d01c2010f50000c050050b06143d540550107040a01e001c0c3c034000d106201c60303403107a13112038041e641c4a0865401441c410b009103d03800c00f00d180c018002c1d400840c68480d2601040240100c1070180c181000b40600c041424170401c1c0740300401400180c12010380a0400402644690f8412080c1c07d045000c0e540000300280018070030201140d80680b6898942054000c0850344629551104850484c0c01040824030002200203184140307a02000450f4900d294000549182d0000006200b103521074100810315100c001001d01440301d0039105082d083e202c2100e078650200c402030a41110b50318003810050007082c15040203000750703580001c0da9841c111420a100c240c4504454040c2c00c100d04201c0c0c0401540320307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 185354298 1250 185353048 185353081
    0xb03160f150e0409030f26010b0c070b0a0c030f0509090a05180102160512070c05010c1a2712180406050a0305010902010e10080a0f0213060206090706030e06 69
    0x345000c2e501c10100200090807070380003540a0f000100e070594603021091700b242c2d611820450000c64140e00f100040030401c41090140524120440c0c0405d40800543c410041c4c44040d00100d40d030103444a0301c03540c0003000c010700d0210903070004109005000401d40a0401c80c0e0b2244406892031515a0360171011002600003d052031088441d8400f821140c00401c0c8043c1c240d40003580c0d2100501402030909500d041420700303101038420b20810603040004c0700314124004407103082c24142c40c905264100107400300300444045998801007003c00c540c1840954140c070342045400d10302040c00c1070440b1903030b0381c8180c00740c201c3c405640308000c0c04440842450b46a405110004e0000c5516510303000400c4060304554030480c0d0aa44481e413500856030891000d0b911a003081d92202806a45201c0040c00340c8806040c201e401a40c031a50969000300340c1d0100c881d01b4040d262006116a0340b80002950b8000440b0b18040c140a808800301d1030620a01400b40c2883e5071000501154581000458181c1203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 185355548 1250 185354298 185354339
    0xb06040504030e0a0603090c050910090504020d02060c0c030715090324090507150c0c0504240b07032604021002011b08160201050609070509031f0b03160f 68
    0x7904550092a6240d44e012805484150f50208070002145004c40142e440d40e048948a0f0300034034100031000754a00410801c43e0218400407440e5180c070300200d41807210401d006504441c0001d0b41602000d40003500c1aa550400e038111440540e4400c0000302c0600d040780400b000961180301007011030907804d1140c207018040d901c1d4600000340300503000101e038a81e60048591b03400403c403c01600c144081c00507000003150404075201d5a0a81c2e030000d4180c03241c0507061089559151024030050103140c1400c0301d4620320a085921912885580c1b0b65030000501100000c550194809005032080e80c660001466105420141d4a45508100c1200c1c40e11801c9001c5650340c0020710b14032050400c0448003a02c0c1c1da100d0440b203040c02072030341005001a44800342907a0621042c001e10f0f44840280c142e00c070308145040c68407250704400003070a1455400184074107240e00345001d541406960701c40c104d040030440c02c1344c0d5140d005101d60b032000d030000e2044103610300c038940f4100000c0c0242d01c4c84012956 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 185356798 1250 185355548 185355557
    0x2010e06070915020d020715050c0a0501270203060412270f0e091b03031605100b030f0303040308040602040305012406090b04050f0102190308061c0b0604050403 71
    0x215411081403a040044030128005518034008004180e5907940d051a20056803004d00700c64103644101039640c80c1140b052030b504552903e44140868030400a407543d01d0615020398a5044590a009000c0d12804a000307480b00c60b080c40070359680398500041c01c21140e01802500c0140c0d00e50b01c9403503c00221400000502280d03480b52640b191410038030240500221010030222410301d001015550016008040002501001d019040c1d20000c0e90350401c5040d480c1c0380364ac010032000420b0540c090000b0751110480451520010040c0204e528810460482800c0051103091700800d5075601500c1e0600c22160410000302d00442e10920b1315582c894028400907150603a66640d080c00c58812140c801103c15010322003008900003000340900030001454000d0a41d0b0410382074030083c0c4500c0c030070070384a54514980e10051b07034001d0243c50034102480b0070343e40443c140c03810050101481100e11f50302c070707514410343c11a0300380310752803e2036529400225000d40f0b566140d050100901005e4402c0e010320 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 185358048 1250 185356798 185356811
    0x4050f0f0d211e050a050a0504050303060f1309030504090e0a03080708040303090803010e0703050601112d01060e090d020d080106030e0c0a140909070e070c0809030604200405190c0201 81
    0x4280c103e0306480703180a00704009036919004a5480c22501d0103003c42180380e0900042c0404103d0000540e078100f04100c5503d054400742c00001440700c0c056242040c1300b1410103100409040d0454007034000c0b10004030702809000391440c02d10343c0711030140c8401804242e002001c00e10192240c2c403040d510034840d00f400501d402c016150005207400c02d0b44070310341402c0e03600b042141e407990501503150000c0085c201000348182e54100c8988030096411203074052010403020010404d14070071951043d08014008102c40c80c1c84030f25074101403401321004441d48c86601e0000114920010714259605071607901c0e00c1c00c03a42094001c40152003d080c4081d030500c03503005840510741d900d1003400c006024409040e030528400744140003e801006140784c510b43c0100004100f0f4012070703a4115400810751800c242070412600d40316038280684540e070394151140d0f80400003000158182d00c1d4101d51a5103201c42480c415404100a4590031a40c3c200c8510a18041c15600d2001d5000340d200c0344800e00001c00d4072f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 185359298 1250 185358048 185358071
    0x14030a020d0615020d2a05101508121201091e060605040504140103050c0904020a1208030615341707111c030e1804050f0f0d21 56
    0xc0d610960490310080f240c502c8025100d90701040660742d44050390801400040c00040078400e0024140f8120858400001e21031080100c10b001900b41010441e104105080c1500304004a107245405030201034843d01c2c80c0c0c290889402016110a621141e1b44410142c6c2003d0301c843c0600038030b240614680d0380c0c0caa0260110303031060140001402c0e0344d49d99583c44919100030081174030040b58a0301e1b8400c0b8020010f2004c14030204100101e60030aa8a9007250b0326641b020440d04001a4031000b51019841c02c810100001d20b001140688000c94500c1900486465200c000c0d1003494500c001c0c05140c071001d406107100030103c0c1240c6040785442c190b41c003007054441142a005554030250300c1c0c6d10020324002040a1444039800110b01540c4501c43e076003040c1c01c00300c0c4802e43d0203c090140040c2c0c5c1d185030003c0d52854a60044076080607050407079410103280c903e40c1c81100c1c00404000b03010b8040c40e600107440000362280480c1c0e00e56511b4200c08151521204065034811908444607102c5408514 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 185360548 1250 185359298 185359301
    0x90f04021009120b061c02030c0409030908030a050301080607031a0f06040b0d02030a060f0b030708060a180e01060602060c0a032007051c0e0d1e05010f0204030308010509040314030a020d 82
    0x520340922026240c40c07030104100161461089042c16001050b86c2102c1d025803000194041c2c1d041c400e44000540e01d800c1c2c1000c0d504c1206a034807180ba1484002111f0001c60f07800400b030f50480712043c1c00c58545403035100d001d400b87c0702c3d0300d01d0100d2494000c01002c40f032071801d102c07180110100a04039501d1300d5100d0b0081c0c035860740824403200189400000340041c115407446006d00030100c00c0201c8043c10300305444140c061002411101c100303e001030101d03503d566902107030740040c040f00e11072000031903140301e410340941007080c103241d03480d4a4190005005400414860300c0344240e66005480d000210f0130950081040c600805c0e6087e0720300d03003407210030f43c1b220f401400c9240c052001805131041aa2504608503980c01a400400c031011940e4030b0381d42c80b1349010310302c55a0301c410b0012202c000580150072a250303400000d4070780d41c200301040b04403001039801001524000c2c0c2e55002c807030b80c0300c0090005600c2d00b5a00103002410f9802105900c4030000c01035500541800301c054078003c40840e0400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 185361798 1250 185360548 185360579
    0x912020d020609061b0a0302090a030c05090a0603020105040909080d091a07021902101e08093003100803040b130504051e09010906090507090605090f04021009 70
    0x540d22429184003495010001140d001c54014001c0c4250b24000004005420100a00c16100d000c0070440780ca0f054025016141030040c05084c2100d900c2e964101240b0a45c1d1510810340075488580125a81408600825060741c0e010b85070140b80c21718260026008214002050b42c0c541b80034411031801d072026001d40a407030760098201c0010ba60341500c026508090152100c029513100f0880515201100e92400131440d8044074044840043c901041d03400515026051980b4244100341d5980326400c00780160040c034044003241c0e50b809140070703408039120f810204124030307905c0b00e0760080c443d070410401554440034007485440460f944102c210b1450b001500456007625006c6481410307000a100e0310300081104076401c0c4100d00300070901c1942c015101808044103c1c0e4400069840802500300d0107500e98080700421100517242480c50300c800d40d80c080c106986082020000d014540302d64441d010b070840b20300c0741d12141c03225030030040300646041408090118266000031790a1680b8682c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 185363048 1250 185361798 185361833
    0x3030706020d05070c030914042c120909010b0904020f040806090c1c2d080c010b01020303010303120209010909050906070e030f030d0209150a0239060a0309 69
    0x1d070b129003105403600142c1c1ea000f030008081010304c05404c0046a44080c0c20700c03c50b40250b401c05401c03104000400c024041c060003401114911100ea20030380070021490050228465082d51038040718004a10254400c1e03280b0140e010310008010300480007144010141624010401403401c1c4500204162a410552080307103160844001c00c940c2410600464491030402c03188050328261000c840800821582c3c2c0c00f50000f103030040e80b20481181101100e4100e5002c0c40403500408861501c80001e6026103880e00c0345500b060313410b1886500000070740b070690380d2589400308040108800c000003908042c8009040003092100001c4d03080b040c0c0709081c003034006a806041c041c40e0900c40a82840c44640c100c82c002e62281302d8000c40c100707010007a542c12500c1ca041c05652441c074140041d901494440e004811400e0002c0d00e005156000070340c886614201030351054801c0c2c4091812a0aa103d603d0806401e100032000020549040c1c40180862102e07410001110315040d1600040d454016601 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 185364298 1250 185363048 185363051
    0x40e090307060f0908070308060f040e102004050d0507050a120b1605180f060309010e0d0206100306050c070b0109151e06030914031215030d0f0806010e03030706 71
    0x400d00b40705482c000c94400104072802480310903810740c0c07141c006116000020702008140c00104a05a90340d450414003500700800070301c800603610304d1154507614403422003061540707801400a005449480000b00c03007500f01e8900c0b1300b001d1920f018070640810034141104e4500549074085450b81e5500421070180c41c40c4070105007600700610304140000f801400c0d900b2110180c1d511118426400002c40e1000c1d86405103200180300100c010400400c16807100342d83c0104040104a1b4000b015840754940804990480364011a01c00007a610b40b1801e0707c0c590749021940009101182a9030000ca42050200030341d28580017464031404c20520080c1c2042c0c8141d604d9046804540c280340214002601d15160213952903032540812920b070300c11078815501415102d58100d01801500c0304684000344002c4141c03643d5044c84100c00c0f055030030880f514207241419070b064920904000a580c00c0300010350b180d50521a40b0250241d03030516008208a0410030181d00d07100c0180c4090010303140c290300c900c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 185365548 1250 185364298 185364307
    0xd051c060b0901090803070b07050904090c0b0705071a030c0f0c0a0c0f05040b2101060b07050304050108070c020612090f070806041707050a15090b0103050604122111040e0903 77
    0x403e0038026a000503202d500c1440341f07034041950280001d40105850510035518011200440d02a0070702102c06420300104a50000760800c4150041500d80e21442c1603c11168864000c0c20400c8140d07000303001d54440c2440044c420141c0000200017001c1401d544500700581407041c60300d070500341c403811210780103d1241009030b03d825501800241404032800e0050211071000705040300c241c7c100c104a040f41244901c48072000a40c06000902010104103503641d0311410b1840c1e41364850f2080398005110b12000404c03081c464645a04280d45c01414185001401d6500b8919a00d01400044060080c3d2200031400780017000208001c0c0780c1d5001411481c6810304007001244405072023070007841d80030051440091000f041048605901030880784201140754241402000d5001e13004100c205560004024003000041c41440340d8410680c0d8010200d807650110b07807010702c180210900302d04c550b0780310511100f580c0010340f00e08098410076003480d40da807800000d004800e840039002c4d40c00008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 185366798 1250 185365548 185365567
    0x20a140c01020601090c05070204110d2309060105010e04020706060b030112140601030309120809060f0304110f06090f060d0908030f0106030e070918060905010617010e0d051c060b 79
    0x1109004046045c0c0400200f113003440090014441c4260091090307599254110303c00300c03000706940d056070701d290701040025564202c0c1450b2440814091203c0e40180001a061741000500350303043e100182c1d02d0001c1c10320544103100203074102c000220f4101e9224980404c1810303c02020f58001e00c0418003803400307a03072141485854011031120b01510f07600800d006102017600807804400b2541e000c8620002d85140782403240040c020f41030303010303030180e800500002c507424010055806076005c6c0102c1e83d407079010344081100a40c2503c9025802050900800d4054902440c3d0907800710340c080d0015242010300c2c00800100c0d461488119090907010082c081803000d51025240500172a080030000d074414140015500c2c2510700c941c1c100c0da0f48035039030032401c00d480051420540b80d21640601c4612041d10b0014041e01103070103203400132100b50001040001d01401340800a240784006400148081c1404a0340d80c0d11030850f070984039400010704a80c1080314480d28000700582c011850310f0b48281d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 185368048 1250 185366798 185366803
    0x306130504061d070b0306151306090306050f1b0a0e06030f04060c050c210702040c0809010c1b0f03020a020303070308061801081e07090c05090a1d0f07020a140c0102 73
    0x1910103003035a4010b1800b801300c40c403017a00722600007004880706c0d22041180f540101561040306280c00f250b08030024000348031500a01d408050324400e02d0f09100c5039503051300d0240e031250211342e0401060050a0403808448225001702040c0005140c122150240300c4046402c95005031011352102180004001c1444505d10491403202914a0003900e0301e25508041550781c4007200c1104001c01d00311681c14600403410085442c4980e011b0b000b44001c0c1402c043c06000b03543c040342c03000c1095081c46560011244141000c0360364200c0315151801c0c80071607488105280716092401c4043d40701d50441c1d40007503035003007001c0e0511600c695036a054600d0701c070040c4030485a04c0101e407a100b4074440c00500080c00041411410308440030700d1403007945660a022881c203410340d0300c818105072801244002191380000201980300c0c2c16212030680559030104520364101000c0050794803000e03040460010201c03c0d88d40c0f07800028510413288020780a4485d04000080003503800800c0e4005560a6a2540c05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 185369298 1250 185368048 185368091
    0x4050603030f032d041407140307030308091005040c08070501020c01050a0c02010c0b010807241715130b04050709051c0203010e06070f020712030212030613050406 72
    0x550155052400941d070358103032404040d00c4c01c40d007608a880c04401c06080c1261160540120f01403413503450400c0c2c1044490902c89030070001d07060080c01e03c0480c0f400840080e504030494090001e210713a51450b10201e56004000e0103110711402006204c02c3c1006003802054021402041c55034551460407240c04c2c54151183e0016056422641d0120b090380c1c0c100d800d40c0d55000c101c2c28405940b811901c0102d0704004401c0004207440d0850300041500f0500107006010351b4041011001c0710814074030003030542e8a010402000107034082c144480c8000799004e9154000c01000442c0d05070043c40c1c00064401076100075103025041e5102e0690f011440c20740201d40d0880c4407420902002801e00300441d210b40c120503048102840241d1a074021524254042c2d81a0314008003951007a04051800401054185010b107006100b104804079580c0c480754041e500082d80340d001000f02d0b00041e05080c1d000e0b00020000da0b0b104007074800c807003000c04450003418440d61007043d0000e10440c20030f00c1619103158 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 185370548 1250 185369298 185369311
    0x120f27050705041d1b0a120f300e030a060c02070801020d020904110711060c16030605090c0316061d030312011707060801030b040804120c0312050a021c09081504020405 74
    0x42c1000400c54607210065011b017511740203d89000c06440e1800c0045240b5400000107020254807103001800002405145141d1026540541110302d000d00089030034a040f0540e10f94541c001210380800580503511032056040c05005480c801561520041e0883e085008001112500000c1480c41ea1600303220f001c21189400b0720040c10450152907601c1c3d281d1108440500406001076000344901007089412000007211a100607010344901d024409410240d407880645d10403403000021500d07000c254034442c6008810412113040c6000000c50700700c1c2480c840139900600c04210081c5a45081c0010031510001c1d07905908154507145508840780d01c1c00181c2c4081c1d402030001403054552250b20300c2e0449030840c0700c0d01d04517226800c01001900c9958400c400e0554501ca88004000c2640074200c00c4a020ba01e01b0b03403c0807a940c005656034401c601107200181c00030001c4520741041541140c28408041c40c1000d6499181c1c104e040c600a001c031422120322084104020451800e40a01a800103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 185371798 1250 185370548 185370583
    0x9050d03051302040c0302040f0314010b0f0102060f040f020402030708070221120c0f1c0f0b090402060d0e010c020102040810090206120c0c0d120f27050705041d 71
    0x50080b00c452080d0344200802442aa11408034580f19031298042c0d42c05030020440c050a45596490100702c24a00d401f1030039850b50070802c070010b0f40e00d060410742e809904180c0150581d40d852004265203100003c0040320352101e0305410030056215031000c0e5114502607221079401c4d08200d00c001c0d281c03000b0010411007403059100d03a49000c55180c01541c01c1c0c510303540d5401c1921b4423030641035200c50058004840c1ca0b242c002c81c000440b000c6180c0000f411090030881003080c0d0002c40410f00076501ca42082c560802d01c054081001030030030b00c0082c40c50742008800001c45520381e0186034292143c1201c100012b0390089402e004040051221094149010f6020000d060150f804a076040c0101040c60614080c01000160140f25180807104034041d0b01044d65002c00100d01c002c0c1688803203012030068a494404046a80c1449101c0c0e2020648241100b0004c1000c4000107207005240b40402c07a55802644030000340c07604d42e402150440b00340b200356542c1003c12400480c1c941007071141c2c1e40c030307101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 185373048 1250 185371798 185371801
    0x1206021206030a200a090c0c031202030c03060108130b0a0b0f04020717030c0c07060206010e090f0c06090a03020a0f030629011b02130608010e0706021209031203070309050d0305 78
    0x2610b244104c076060b660000202203504403503000074060000b0703910002005042c80781924207242d0141c0c05401180c03298499900c10f07079400c4c0e5060708030700003181c40301050501000803a01c158042d11050754056200000c1003241a184d80c0d40c00c18001c0c00703440d0076814546429141c1c416180424072804105010b5500310304010850300e40d800301c45001c4a0b0341019240001c040b800d00004081114010300002d011140d40c1942d030b40300213550b9102441002c20303c42c581e1011070f106100200b102c060005010700141049261841001025441040c9841d4024001d04d400401619480e04120051210b040901c0015285040010a9401c80c440c0482c01c0030441e044540003035020309030500304007000c1c079101508909604495102d41400c41c4082d40c40450786052440f01000c0350014130a81e40800024480401d140103c160741e000342d8064900507802c181030b03254034180242d01070107080300000c0840350040c250400480300c0b0303401914140d00094840b9112400d200c0100030089903680d0314074041216 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 185374298 1250 185373048 185373053
    0x10303021011250803190b060a1e031803020a0b06060903060403120603150917090102030d02030402130204080a0c06020c130207060b03010606110f011401030f0c1206021206030a 78
    0x3540700700300b40b81400001c0c04151150711100c01e00e2211807184e000d141c0c1941c0c4d00380200703c030320104004e641605400c0d06010b6168080c0c140030040c0d40c0700d07100a86070034440c0c803e0a0000425603000c011520209a074510110442c00501468000428000e070080d00440425062084484d480140103a00804040094001986000071340c9584942c051803e0b42c01c45c045039030040c1c06031a150340040e10304105004410703194440380d4025181c4501c98203c00041d184002d00d40300e50750107580a090f0250f00140a000324018003500216806480201254440382c0603010b800102d822a810508156200b04600b208014500040102900d5140001c0c40340d02d1203040000d401c10b118402c0740d62a250003190079420805650040009400c00400900603551168402400103901080c101820700c01c04810351400c2c003042c415500070100c1d11036510080da0079502c8000b41d04120000c11200340341da9400c005003600c8040382000c0c8281c8202030141c1d40c1d1503a901486002c03c00542454800c3e0850a0120300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 185375548 1250 185374298 185374331
    0x709061e03050c091f2c01030302030d1a0d050d14030c090d140f0f07090e100c26010302040b03190615030212030a02060c070f110d020402120103030210 67
    0x191000101c442c410140c4c1e8141000301144184e00071820720854850002c2035062100c841010300d0300760420a0246e258050044040c3c2d04d1080c40040c01503081040010a41800da8019254181400d03203000c030124008404104005d940319010740d46a0020910b0101081d800008039400d074449004d40b600314108040b00160034400e95880c2d038410b6984801080400c100006000402c1c001d807003c1c0d440320f0440700302244c0c88406d01b00b506101e500074603c000c01e01242230300c80d009120100c20002c0041015400812008100032910b0b0024081000d14454001500300520754420288007140c060952441c4144000e8900c034109862181c0c001802c6a088806d0181040703000541184002c160380907420b0b210100c5151981011303401c60310020a410391880004000d140300d013510360807110203071340e48040c06066010382d4000401e00c0d445c90303803084085142101c40c078000311760080015110000941c0040c0c01c80c1e101ca4001580940d09600400515405010f5080703c0d40810400f0f2206140c001e506c0312 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 185376798 1250 185375548 185375563
    0x405012c0904141b01080a06141002031c020403030f0813110406180209090601020106050907051e07030e0f0109060504170a060c050c0706090302010906030c020f0709061e0305 77
    0x103005141401c00101440300e0102800340c0142c0d040e0544840351110903160009a0020100700d01141c5007502180040901d80b05034000c540c41c4078a41010082d126040108040e044504501148021700c89441e03a03819201b80701118007802100180c2c0e4500c0c1d0f18014240014610360181407145080400116411f40c000f10080d0582c071064130340720804010300240041c559600a4040e44422518401880301d242d4000d281000d02110015a03983d00d80e4012804c0e19006e006803034001e032100c00840c40a5005901600742804058400340c42081c80c0040401c4681125406034000b4030210342d1601541064850384003800f03000e20300040501d080100c080e040748214070828000c10003204542068850502940c00c01c0755100c08203000d00f503244840207081ea00201d940280500407900c0004000340581041004ca036030684941300c0080c9410816001004503408a5055005040300c030b5030710ba0414880000500040d0700c00060203030805117181030307800644c05028000080302d442071010800003d0450f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 185378048 1250 185376798 185376887
    0xc0907050301180608010c05180904082703060408040e070801050915030a020604170d030c02100902010c020a091d0c0a03022404031109060d02090417160602040501 72
    0x41d03c5071a0710070b40ca14002c04482c0c2c0416415403800711140702165102c002405044115201920001c41c1d61003044090710055400515004040004070104080400306000802c03511504000e08200c21002c241010421501240e07400e90008040c041c100c40003c1094000c2c1691411034010340c184070201c1e00078203008e44410340c420410308000600390740401085905c0c07940a04601e4a0b85d641c0e200d4011f80e00880c84c51030690f80602c01d0f8442400d4424442da84503d11190300501d180b03e4409400303002001c24200071b904104050722000d000d0b886901146000b4091003000003802880c8225941813a40341c1c030384826403500102c500791503990f15000c1100c1501d4040302c01208080802403910b0070788800241540e14000c0110300001880782090036040b030781c3c030140ea4590141c0d50302400c01c564007440c1c5000a6004803080c0209002c0303125144108501840150140c0c50100b492201c80050412080c0460301c0e1a00040c0034002e40d43d00902d6481d070012041c420b254440a00b03080c28482e4030030344c03511 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 185379298 1250 185378048 185378069
    0x1b0906050306030a05030f03010501091a1c060305010203090c010806010f0e091806040f060f0c051b0106120503030105040617060c090a030f060209100806060403080702060f03090d020c0907050301 86
    0x8501165001c4c0702c6140000e9002040769580c1880b511440e640360024410580450039450300016660310088403421209828868030349062005403000c040c00c582c0494414445649040200000b80244020341c0aa0404001000b48107411030004040f64401800c0310304001c81e0101d07220400780c02014214655a003201d80e0412640d8900032011903450705040044144240c0007440180410910300100b511301030f4806201c1c00e00c1544d02c1070700762900e10f804403001030001c01c41d188071010701414400010701801c00101d030455961400181d000584032040e2600e4000000410591415200300b60052000080980040500320080354440f031000703103840c0740d40800140700308043c1d948500b0075001c0c6a1001c3e403901481040d040040083d0024150b1500403844070341c803000020b000350451449500000c1280d807400b030440d5a441c41507044100101c1c0c01c1281409002c8107411004055407098441c00010904d03d00104002480c01c0041e030f8072580260301400a1101e460740c084c0032281034031400b104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 185380548 1250 185379298 185379301
    0xe0c010e0105030a0e16031406011410090305030a030e0f070b031609050904030801081e030f0c0c060708032203091a070b09010b01120b10031d03030a0f1b09060503 72
    0xc00005444443c241443c0ca00134401b1030241c0d402c0070001202031300d00400b1090300203000440e40e150340d44405e0044a6081030701d40398120462410540c1c203285c56546141080003d0744c4c982c0c49034919080048550042034460360128120407082000300d099000c0400204070052a100d00d580706ea00c03014007031314990310700c2043c0c15011324000e039101c10003404040e00710515841d190a00415403002030150038458014440301c50040c03c2e000c0112428140d203180510320b04041d80000303007403a50010b10007403058040d0420764031065403000701400c0860f0150545960703c4c50182910441c0341030841d002180c071016009280b01082d40266140c040c3c410f02ea9020104640500701c00019004086004004c80c0d9040208001980190400b81d201c103800c1e22060009446c440300f04098403208100250401030000303c0d0180180f0940120020007400e130514088040c00750300290566004450310b0b0021610741440c0fa02e115241e216010b0302d600c85e43e150000e10f405600c0000e140589900c03c1c0c8042280110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 185381798 1250 185380548 185380561
    0x105060f040f06020102030f0a09030215070e120a020907021f0b130c0c050105070905090a0b06090a0e100504180201030b15040f080c0a180504080f0304080d0e0c010e010503 76
    0xd045801909520b4082400c40d9030355503009000c1d50086510882481c42540800d9023100345002c1c00e1085540f68019080c2602e039462200311603c4000c001808008201d40e003154a41c44e184440b1035192901c1000e0640610b40d40180103003440007401c0c880441d8450080c1c04952400340500f5100a500c410003c111001c003903002804a07140c010103400700c01e103400c8499441ca5000381401c030710f0903c14402802142c1d10150295001c107480d02c1460f800242034400500ca40f440380d40168012503005040c6414450804081090313001c09820244508024034240901d01c00311844203170090031300301c1c1c050180350341080712000b5441489100a041c551600c201d01404c3e552194140102d00f10301c1741c2e0544950b55603c2c900d114440912558607d80201c58900900e0b0920074504002e45541d8850b40080d414044260802010000e0003585c0c2c5080070b00a9104d00d43ca240019401035010700d18541d102d11082901c0c2044070800381411406a000e182c6100c002d0f40c10459403080c9034024240079031656500d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 185383048 1250 185381798 185381827
    0x307110c040f090c140d030c0f05070602030c0714010e0609040b041109090a0c080115090803040906060f0306030b0a0c05040503070f0303110606420d0c0c0b010506 72
    0x1010a954407500b0b18240d0b1403201d42d25802041218010030302403103280d0756032402c0019081850f4015401030311215000011074040ca072a500e000348608002e107003036411600c58900b440001d800c2800141c00001740c42203080e1003040214040d05c16000907a84035203c900001c2c0c081c45a5070f2006001d075001150420143d07959070f000701081c41000d4001d10140c02a500c0e0a0860b60042240702d110320000c201042c000c000700c1c800d4402d00103150319140e00c83d90a161841910b1405100d00703600704003040201189108060010740010216a02d01050707071420454047c0c10542146080300030181b40240400204a1200845401c00744045000800304545201140c1c688200d03004a505446800800101b40c040317101480c04580c069522081a212564025a00c0785410360300316600c4081c4036804410b48055021501000d401101c26090344100c1c0e240c400040700942e11024203080c004641c01407a90034034019118a005039140c1940c200c4e800d9039800135507400600a040c000c0b0000300f00c220030742a41c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 185384298 1250 185383048 185383063
    0x6052710050a0b090a0b01020706020c130b0d061103040204060b03131104020409090516051905090c0d0c021c050c06130203030417061f06020d0305060301060f0b0903070608010506030711 82
    0x1e03040b80481e11700488200080e03e00582c81c0c60040c0304054000420038808224100351500051819401b652040c2e940809080e10240031a0f01900208210780011a54810801e01e10102d410b41512890b0600420044440d030382d0004003036520420402200382c08081e05d1202c496071207812141000d00044c00f05001f4090b0350021012549003816440602400054060604804004403600561140180580d0150580d0f4070340c2381140e0321109005610344540350b10b0303200f8060500d0f10b08040150341d210003941e525401c001e0140c6c2014131224040d500e000207041000d0030b603041c00f524080203440c008c0d90310b94000300802d100f01d003a2030614085650502c112030041c000d1418101401d5011a02e494a0721015501d240400c2c49019003d9045040180c1080441710260003514242c2c421201c260040c000003070503c1e6055507105008103003a8410b0800c800035226070f040c5140c80c0e00707200091600c0c01d03410b07800039424484403000400c020f540308000c60394008101c0c41c154441e002c1c544507003407800c0807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 185385548 1250 185384298 185384321
    0x507020d060e070e0f0a1506030c020c151e03070905122508100b06030a0207020406090e0709050903090d0f0318180b09060906041d06010306052710050a 67
    0x400400103030506082c15550f00805d20301410807074645a49000f081103c49490107034482121751101040018080d0703014150019190060341c1c08814031600150300341e001c114402a18082c08070b016a00d1001100050a038120441040d40c55400c1014000e006500544511440740d01c8561910003502c0301032048035403003040d030007030000c01c6880280307140d440003107038020419644265481d051650280d0300034400c414078040c06052441e21103c88c840082d50040c1d50983e001a21084005152a454441c9008910880028002c440d061487c0341c4161366004d028000d09034000e210040303441e941e0201c404d006550210003948040c0c1149410b071003075400913001c0d0018143c980c000242003140160340450750f5102c4002005000c12800800155410954030a50080e4a0100040850406078001c84c90f0002170500c1914420034443d455103001800d030030403103a0680354800d102403031540800d111a00c00342040300f003181e0b20110016a645008507800380c0d240e180c5038804500d04015940c014a0145c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 185386798 1250 185385548 185385553
    0xc101d04020712080612070303080c0327011505010e03120a021f0606080f090628020d020901030b0d050c040218030616110f1002180d14010c0f0507020d060e 69
    0x200c3d80580981401c0c41203a01d103006008001505004c85000f25141c42507942c191a07034401621040c07001040f5400061458200228840880c0c41480d41d1003900b200c68400349001194480c01001707403010a041c1544124180300050141d0303811aa400b1982100603911404002c0e00d039040990105c0c41d0506143d2156003180001c0140602a0402d402c00416520760761190031081c0c68001405998407001c03109401160008404078901035224002c01e4091a0484054800c40c20324603850b030300300d902c00440c0491495001802440958242c0102003104030211141c0051000c140c43e01501d0322808034030944190390004400421484041d504404620050105c0b0780303070314181e0302c1c1001d200404118400480e0b150321082d0090340c000500c0540700b2020101402030406001d540c180030b500503000001d0710313000030a0040d103030351180010300d1140c60042e1414013a01c0354000005084a44403e0300d80100401f01c0c85e180301740c07034102d0229545e6541c10317561448601080d05001006140c001c540300d040b030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 185388048 1250 185386798 185386823
    0x6010c0b0a020703080106050f0702010e01020f0d0203130b0a090603020d11040617060901050a061b080a021b0a0e0601180504110c0123040f06060e04030f020c101d040207 75
    0x24000c1c0d0b015000d41482034482c40010f0741c0318002038986000b81e402400203843c0800065006501c65201c881c1818010b00440ba08220307000056070422400061030340040c0d10229424400340c03403040c2d074800102a2151000d1410004440082203c06103001d2a13091580000c1d100100080d80e5204604042c45400103940301d0f03464640040981c0203a0b040039030b6a81e06030010503002c0c50300c1c00e01d207070403141c4c002e09006000e468100c0550b1600b080c9400312000c846030008880200e40d4107001403882c0c4079242d01800b1585440903485000f9103500c90041d0290712161820f0020411408a00303400030000d081c0300e441c0109481c03520320080b149402c00f40d0028140782007419416090000751006c04520301c000e020302da032900500400302c441381c0018035002000f240410003250619401f070402030302030440801d00d603403900f03100c55030000d0940d000c40004151800341800264180701202400340115020000804e400f00010706240350800b0b50a10040141e410169a5440e41d044800700daa000450907440f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 185389298 1250 185388048 185388061
    0x14041211030d0306052103070b01080a0b07050a0801180b0301060b250c0501030e0a060e161d011e0806011707050111030708070201030603021207090b01030b0d06020306010c0b 77
    0x10500c0c503110490081c800c0312181041e41d4040d01038001540d1020b84444034090b200e000c84102c00c03400f04094400c0f0b0000304603c401048400c0c111902800d1100c0061800c50407924049111740c0b00104024104002400300c1c683c0b09910007501811100c6200c1d24084000d0704101c0c0a0060900c21401035041d0f10703004000445e04882c201921910803100d4901d5844120780c10804240200800700510007800c1d00303c10b2000303600a81c03103103088808450450b0000300303581d52084100c40800640c030400380d22030342c02410207280740c20440c00505850310fa85184100c0c40124013a240c40c4c10300500310150110014000520b00c0c040501d80242911412511b080d6034520a0f0340d418103001c0341290460040081c04203155000e12041207012040a0056103004810b0700e07410202d410440d41241095140c05d000009a81e0700049040c02c0b0122002602e0150700c0c20004034100c62581d04103a05041c20903003c980e0070b690b0f07082c1c1158065040400540c1c1d80c1e480900403901d5260011008181000d590103200c0c0c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 185390548 1250 185389298 185389313
    0xd0506010603060605040303020703060203130b01030609110a0501023d060302040f020702030a030c0501060504020c0105090d08100b030a0608030415090909020a05130b03010509010c140703020d140412 88
    0x4071201ca03182042100d440d0700084440340720f2404090050f9010002c20800140719600640d40b00007010b50003803480c601c582e95400320010a074000c0d1007180d04c4003032590521500416070080100210340356441e05203003c0000c0d441e040d100b042841d8420b80b09802140048205000e21952410f29040d01840440c1c0b80c050401454180401d074019450321a40f5081422188202c800e01038005004203d28140c9585c21641c8140c1454210340c503540302c0f440051951100e001420300101d1400002c40ca514141e248546020060060402007101020034032080800c41c000c450180c804007000b0130f039260740b44200398002c0d240c00e9122000c140b1001400081030403190080f100d00c0c00c141d0b500e694082e40d440002005840003040d0107940001c050500b0400703840c1101c55015424120400400d644400b000003900f1144c080382c400d80103035183c0104451142d4803c1c90080c10f1080c0c007001c2410072400c0e0318029034500c071546644040c08500041e60158482c100b082d01c0091118103100c4902c00c150b49001c41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 185391798 1250 185390548 185390551
    0xf0307091401080a030203120702070302060307090501300b18072706210f090305030105030708060f0412020a050a06060e060108090d05210f061c0b0105090606090d0506 74
    0xc040d64001c0d002140c01200459807100e5903405038015801d082c40d44010130010440035082c0829446502800801600e680e4080c52140300d8603100c1c170078000e203000d00240803c01e0150100304a0901101c1c5140034003045250b2000c000002e51000034134841740004514502150000307030146038801320821003000c0d03000c10101e4001881e55200c0e82190341b082c41d0703222030303800314025480860402d04084404140084901188450341400403c0c2003440340f035030318215074080714168001500000140601e00f0100644001002108010021858012222110a03002510003041a01d0107000d0400a6108209c1c2c80c54443d08441a505c40500368a44000200014030502c0701c510800c1000603250340c05440f003030348910340001c00380410b003030014001c0b0b40aa01014882196031200709844150380318044a03184145034503040c5a5003800e1940401000c0c000c100c0113048095841d0580b40c1c00980c608481904452040c3c41c480825100c100010f08913005441c0501d8120804840c20400d00a0011707046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 185393048 1250 185391798 185391821
    0x40f140121080c0c1215070813080310051c02010219050a150207030e04050c072613090609151403011b020105150927030f07050a0302010501240c020f030709 69
    0x604c101c2602d0682d1078030340b800d403110403c86c54102c400058909000380c190586c0320a0803c40319000074030310340da80c1903650015945805469142d0000780514180642e400e800c14142a650703440c1c2002d0703a40001e585941401da59510580404010302c00c021040242d002c007103502200301c81c0c987c903419035203d00a40140f44181e0001d0483d031100f01c20b90416200741400381950316100c614212160b210000441c0d0380c10300200400300c0041260b0a20038158001c2c0008025048030401000e11303014600c41960400d0308881c43c0549400b5881c422481440303690021141440c2001c01c2c8590031000003401004070001d4166000700001481d0503150303042d0b200b94440c1404c1150042ca40c0300413001d1203410103045565032a40388961510a00c043c60030340701440315076a0b0700c0440740303040c403400383c00c020640114204541381d030b0059201c0c400301602800f03010302420b0504c20740000c1000041040c0308a181f024071103070600140d00c0c07184056407119030b4000d2051078084c080f07a60803952901c5034030007800c140c030307c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 185394298 1250 185393048 185393059
    0x2415080a0501050d06230c0904051b0910020319051c0c020303060d020f0604121a040305090904062d0f0b09151c030e040f140121080c0c 60
    0x15159114510840b816103a000d13182034041c442d03550f100703002010040f65141500d41c032000c2c0b0340e21800e94103d01d20b2003403000c1c0340d2858a8101c0b26080c4001c1e120701030b26080512426100d103085e02d01d6a0310603900c14540848900c2200c41030000142d0851048008008410342116902021960854000c040701201342d03418458118210501e04201c070b00ca20043d5005070800c00101d03009103030034021402c1060000700302080400c503100004806d948560b104be41c0112914000703030244032401c42001142160340d11340703402520f840c0d07030b0040c81c610440500d14400d586c0ea5001ca8180f080b50351108400f80c40d00c07145807127035429105002e003101c50216200d8000300d04100d10000c4900b03990282000002c8003034005a001d4407101d20392040b40c00d040c99a650880701e8084494034640c0c468404020f61402a1103082a16001c203060100f0f5845401a45503990f06000c500050014038175101411140d0070b85284403501400c0c1203076420001850030290000703d000c156840f0030100810300060b490400c030396 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 185395548 1250 185394298 185394301
    0x306060d02041535101d0403110a0b0c2526040b04090b0f09040606050316181e0603050309131107080306011202070501150b03090c0103241508 63
    0x4000410014400042d080903105071140b5407136004001070550840415030b0140c5080f92074000402160410890441c5400e051000340f00174160804c0034000320f10b0341e0340701030a02c00e82c079503c0746544c6103000f4007948544000010364400d440c0011841701380421340c251110404070818108005051403e01c0c0081d500c0c805c456005e61603c1c0204200c50071941255502400c00d4134140e80000207194402c51680c20004c00c8540c0700329a90f903081e0b514400d40c414080081e02c4c1703041105152034401d005801414041c94a8410f024040c52100c00400c00d1860074030100c3d440019005503510800b40007403220140303080c00e8001c4204403021015000b510b1095900405d243c1c1c28040b01c00588075680401d40041d00e042021201140c101c0300150345c0000d041c1403070607548031411404030490340120b0b41580c40381d5455403280510fa888002c084c0041880000241c114240640719680311480210b180713051507618101c0860002880b5401d01304507140c1a0386011159840c04d01905036081c1c01120030000b149c900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 185396798 1250 185395548 185395577
    0x304020a1a13080708190219030c09060504050f060631030605060901050f061602060f27010f03090309030605010f0f06090e071407050f0304090f051b0306060d020415 73
    0x284d04012980f0360310080c0380e11070302c07202003006503e9035100c1682c000740c0c60140d08400802c250910001507209000000c3d06614201c14201110030a0304140c0c45507040c10280703d02d0800f10030700c0c0d580040044803a81d035203808610440000b0708941c10a00800302441074100341070000d10314600b045030b003da0760501140c0d44050801a08250902445a0000d40700b41d5883c51400c1020140042241000300359a0340070041d0009544c581080110040d40600000c62481c2501404082000c0c10002010320b41500c00c500000780864940c600d500c0e00701642c0d80741180034035100da21480d00940c0c0044041055503101c1001d000350701582e004841c024440340100060081c4600010303000c650040030508059140d26600322800403440c1d001c15450301040c030180c008035405000301002c003241c01c4003c5603100d28003580003003900c0e1800709a003001031424040154282e40d840c12100300030080000540e0301e0340d400001807642c1c081c088444420390310214000c10140140d5001913100c61458071508410490355 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 185398048 1250 185396798 185396803
    0x11011106010e01150203040e0127090f02041e0e06040618030f1407051603050c040b0a0918050d020a050c09191a060a0203041d060105040b0304020a1a1308 68
    0xa02c11008407100241c01000f44880e96034420002000c18819030b40b82c1683c0f6126400f2104080c3c011007001155800320888d40400900c4e0188507c03060b110a220410f0540c541d41781041c44030034043e0081d0b880c0d4a810301d9140041c1034000705803500460411074440c84030700681d600c0b2422a81100c0311172620181405000005138505140340e030603030342c2d003503502c03e40c4400701d610b60007580044c0003005042c8005000114180680424850b1916420b62543d2450130018030388060002428001d40c50400741d1031320b90300c640240d1000e0f80c1412038080359a40b403403c84207026100a00b40504a80616411041890b9000c41c0ba4210306000700e08448212006034204590744005403075420b4030b224480c40710050900c0300d41210541c1d131145240171024010708030215025600c26601000180c200082c2880b2990903440041a18000c02c0c4c2115003618245001070910b02c658003032101c104034084006401c42d90340580840c06020041703120a142c20440c10f641c0c441c2d07085804001d101034800080401d020100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 185399298 1250 185398048 185398051
    0x3060b01020303040b15010e060f0c101b051809190c030c08040308061201050c0c011121040c090f0b011b0c0510021002041512021905030c0c070311011106 68
    0x414030345100d5459040801b984900307014005814080b4000c0e000c0c501c2c2e0780d070300041c00015031a04030300c1b5510741000b01c0342e908104810b000004183c4c50b20840000219415010281010b44c5003405035682c180c51550f5414800c3c42a41541e0100d04241081000711410b4016004200d0f0300006101064940e4402e60958003d0104000012480780025010030320850750680c00180103840351500d284408601425903604545010844c8400518030025640c02d2150404c19604000c115080030300c0000251401103044102c002c02d047c104001c00c0c28040000b4060006110141d810000c418030205460080c100c21407200c1e02182c0f1686014620b0b6100c6a61900e135030750301030742c100c808605250800074205100c2c18030b801144122103804c1c641610b1803009101510711075548040c07014184000600c0d886000d91120075450051060020050808150020401c1c003800c050f42c40b9038481056030381d03a00450060050314462103030000300380303c040305100980c1c110070f0341d91070001c92840300415500c100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 185400548 1250 185399298 185399303
    0xd0e0705120d08061e030d020606011b0209010e0709090e0714091e19020310030b0c041409060103090624050609010903060b0609090106090e0f16030f0b040c030603060b0102030304 79
    0x6024000078240c1c42d000031405c804102020940e01c010888a01207860301d03940d9600c00d00540e000e242404655030300040090303690250b0700150344204065a001c030b1080141885001e5003104070502003400325008a041c0405803141c40c10401c2541e80700c400380c99076000c3c144102940d00150310042440c608112011510410000c03020340016240103400720745041d002016a502c100c04404c0076000800c8a00085000d0b4201c0c1d8410b240141c290b0801d0001107074054541d0841d803100308000c0010240180642d400c40703604985084040e602e000c0181c01a000c410001002d079450400d6541401c124019002000d111220070000c034240c8480601c24140f05154140e808600000010400034000da00700804c1080090306072410b2444080100340407003001e03001080460541c11042c40035501c08600c1c1548411a40c40100e8039040c800c10300140c0031a4203240a04041c0c03100e20551819045070000008840302410810400080c00e03001001000a804225503041c10030441c0f0a5540c40013040c0d82c0103d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 185401798 1250 185400548 185400557
    0x6040b10141c020105091203070b01081504120203070b040b0a0b0a05030c091306092303040f0303121103070e01110a0201080f0a0f020301240305010303051902030d0e0705120d 77
    0x10b5a41c14140c000e1800703a5002c90402c90100000e59454551303070001c000d01c0d42e8400003503446107254a000e00030310303a05070030501c8954003100c14003000700c1b0580842ea402c9a00710940c08800382032103004909502c0b44042c007610590760202800100b10503543d00c240300c0d81c0a030f4010003a29260000300620042a4400c00d03038140c5c82491b101c641440c4c2220200d0301306074800030248081d417142d07907803c0c10303292039130340540c0c600d03450310740260a40c2c010303414407108404064003442ca41820a2031111442200340405000c21100e0200818081c40f01e500c904440d9600a00b81500c03032808160080400c00c2800d07080d0700003100c10b0804031200300000340c8881c0e42a416140d00b00281c0d101360b40741483c113030001c15201c1c8050722454a03407011b520506c000c40c064a1554004c1c001508a001d00c00340c410700d030002e010209440d00c0c0041012030350040a80d80c2080c0b400d01c80080714a0012400c900c0c40c0a86079241c1580762801100380e02ca5400010610304075201903071740c500440c0001400c1c03620b071120200d1000c00316 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 185403048 1250 185401798 185401819
    0xa031b09170d0f0f09050409050a05060709080706031d0601080c0f03030408060f090313090515030a0507050f01030e1207030305071b030320180306010b0403030e041d06040b1014 78
    0x541c000d002c813030580e80d1a840e05d00e4110755507000180550390982070a0365650000c00080c8140041888025032044190904603001403618050710313034801e0644102e0040556600c103c0780c0c800e8907480d2aa804a0102c402c9901a58450030100e88542d0801c6800f8450340240e00d841d20300741400302c00d84007140d1840002c2e00040d40c60710a100d460300b100609119140c0410000c5440c407640c0d121104010342480140012a49012060144000310b0b44400910a500c04500500080c50000d42c0a0aa90003914100007070b9481c080140c014080107106d081d0305006045224442146030306c09440090f0280c1d605001c1510707070b0301055510031402e4481e1010500c1d404d164a0110303010340c0000c013601041641d070403400c9440203601c0c01141c0041d0504101c40b0704298603881c41d85030403c007690142c1800c0c90380ca8030b0070b450340e079028080e5900c2c0c2401038042c40c1c840101c100c61401c0080b2020010501205039403141c0303401d1400100c0044110340e0340300c0122215102103100c4032491282c1d0782024026040a000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 185404298 1250 185403048 185403077
    0x30409110405030f060609071b110f060a030209030d0c0f0f02010507080c0a110103020903030915090414040308070206041a040507080f0d09050306100b0a031b09170d 73
    0x5048112030300c035000082000005101d480070030420350510f03034a902526007800c158080100c0c5901c00f914003000c2298002030170900c00d152030108817007503901a031003078082c0f210702010070130040c46141d104d0780c810804241002c800f9016002086170000071029950300d0003144c3c1041d0b5401c48601f00140015007030b41c48010004c4c0644245662142c0141045801c0c26034a94464100d64000c020a540d2030f0060071040b03003040004809502400c1c02401c0a500700044000800e40e40e00842e00e00e0392083c1001c402c900c0c10004014111142010040c00500c40d4000f1f6030080c07429408103490807000100c00c280028601031012496174015070740300d0000002000b048000c2d0305c030040060400d44650248000c0080e850b401041604a001c3c0c0402c003034850107554480180200e000c96000c24002e400010030001c0001c505170070403042d540e10081880e102c491512044005180011404045c081c81e0030780a40760503040011b840c1100c00a080003150450b05103585d989500d21240c804012610b01d0900c540d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 185405548 1250 185404298 185404301
    0x504060e090703170c1c0810031e020a03020a06020a0b1b070f081603020c0102100203010506030402010c0f080a120b010f0e0f010c050709050f06010c050d051317011406010e03030409 80
    0x40c185820b8901c0342c140244155030340e0800c2800c010394071280607461b20000007a038101c1d0015070300000b0010000e4650303245454200c110f030204126242d0398414403039650308664619a41902950b00500700750940d03520303550080c2da24019140292484081c0034001200000340c2086146d00020b58000c407400e004640d0b40e0781c03680c04c0e05114100c0711008140580e00210000304016800c0034040d500800048002400190802e40340d802484155801040144900d849010840e60060390a10b00350450314441e08141b2180500d0700320007001c02c40005042000142e2016269a102d40040010440c4c5003040e401034451000a0703c110010803100400300256182501c4c05c09010003041c100b0380e81850709a601c1c00d0511030307503800c4001d0640d611414071605841c01e42c2019405502800c10380da8000305501c0d6260b8075140101c0707981c00c1004c002a516109000d6800d46002484000c440d071511410400c000c81c040c000d6011030000d004492000180c580d8481e6800ca01040006800b0314907250030403140317a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 185406798 1250 185405548 185405573
    0x10120c050d0c08030325091413020408100219050301050d0b1012030507110306060105040b030405190302010b131104050d05210a030608030307050a031a15040504060e090703 76
    0x21086511840c00060f1080203100452003a51003c55090038081c00d4000502d14021450001c420851416028480581120411006188216240907a0081030840c0c0700c041c0c4903e421000701d074000d400100040807e290003815119100c00302e6081d0550000c0b1084440780000d10800342e20034200c8580001045c00c0a40381c54001a1040c4585c03041340d10f81c0c1010310000e41c10b01044002600003d2010184000d2155800181c80f0440145c0304505101c00001e10f94003940c0a51840940c000010500b003003c2008000106040c021314181050002d060180c0203100600d5003c1c0562400ea440300000d100520401c1961010202c0c01c90030207080c2010301160b400c807940210b17024840c001c0c01c09040001c1c40254800102d04c014480d50b29003100c0c02c01020307103050340d01c03800c4a07500c28000d12000903000004c0e520800c001d8030303000031042c20b00001ea400c1034440e903e0b507a4026000c0410780710403c034114018025600207480500c4065a45c0120301e040c034104460850460704012014400501d1050004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 185408048 1250 185406798 185406803
    0x1b12050a0e06221d0105060a0207050a0314010f1b0e0102100203011215050103020d02130b0a1e1205191a090a02010f021b09100305030d0510120c050d 66
    0x4042600307510081116940140300c505000c44040001400e0744810156060240540c0f01c2c4400a007080d039071001403042e8040c0641d5101c2c04011a2003140c0c68030821101006240041650408599a0925546000c107414400025500b0b02c0c0d8281000c0e0b6446c02064042c62121001c0031002c1003c000031260002401881030441c01a800500c140b030b0400c1c00550701820030340c4030074080400b40340740040352000079860b0192020b0a000c01080035a5038641f6140d1455011340361411071003440d0720400f000b04a0b8401866200f0b0b25403030040349403000b120103010620856245010011b88a9100c80c3d00601403803801401c56000e00035105c0c2c59aa081c04082c2918421070f422f6501810901c07041400302822a031180700c075400071002009640e0301c00c1840e504d46045002070501454100c50504402e90f902d0940c40c000c4068101103400d08424040c10001180c120701500c2d100d0b80c41c0d01c070307a8000d00000e44104010400400010031035800402055030002c0c0e121415085051612040c0000320084a43c103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 185409298 1250 185408048 185408057
    0x1181b050d0e100509010b010c0c0306020315040504060902010e040b06031f080d0e0f0a03030e04050c0c0118110102030c0d08091e0616030b060d02091201020c0d1b12050a 75
    0x16059602d401c0186110b20b1112034000706107450010f90040c00c4071081242a810452400a500003044c400d0f07080304203803070304814050b070380342e85002c2c402840505441d08550050701e044200b00a1182550040c3e809030304c01d99a00520310009020002680d60319503489174400720400114a84800d00b415000749a100380c18040ba00d01c0d030b80c0302e149041c1700c00e207201e030004035000d0304098801c1d2920103049080300707000b11a884009420340e04c0c028081c00c10041c2e1280202d540b0f0700400d16041c0680251021500b542c0000e002416520101a00d02c0d0039540b0200c40c08000030b00e039800720798004000d80f102e003217a81004000a4a201208a0b144100507000c10300034000c0450740144520f031240141c0c6401d4481005018905081d5100329420b40f40745480420145000c0c01a03820381e5842c812210301c642c09400151301c801403c00014215142c1e00280e410725840041c00c030484410115015030001d06984031900500c180c2c1e008600005040e942c000e040c454140300700814a07000b00041d1100c0b0005192 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 185410548 1250 185409298 185409311
    0x215100504090c09150f0501050c01090204180c081203040318050306072007030c050f04060902070c0302010f03020a02030301031719080907060509060304260f0301181b050d 76
    0x31074125000c4140a40e8100f2540d030302404040418015907600c282d5a4280140192900d5201c81e1540214040c181c104080018800b03903182003500801d00491700180b040102c1c40c441a040c214a0080003400ca80440b04203900242c424000304041c24000c542443c124510398899804440078891100342100d100c00440022609880822010348034000301d03164010003a124503908443c113690820064100d9000c80802e2000841017480d0100301d83d003c1d0707060502022805c0c001303000b420603034011104042c800f040c0c03071051110146000b011617000b030301c0d4003c4e080c000700c0703046080e48a100d800340056441000100300181054048008450440c0e0403d0704004000c095800f4030703506907200e480000c030100d041c4034030902d0074000b1380d00420050506138070700200d85020604038040148007030101d484c5054401761220001401d4040300c6a080c84407652000d45900c1c1000301d80083c054600b215010007204400f11404d441104203071200d2041c95581c00d5040c10040341c40c0d074414150700300340c0791701c926 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 185411798 1250 185410548 185410559
    0x221090d0f0303141614030a1d15131a0a0e060403020d1b0302061602070f030b090111040e06090414030706051f0b03010b070c0e070f0305010b0a021510 67
    0x3500c2806038481d070342c04690b41c82004c1006503014400b40443d9003a00307000300c00c0f21209802c215508468406401030b075440e60780310092940102104001c403c6200c00c9100010409903001c1043e41440040005030621511168400200f85544c0d1074020869131555604210380618401c43c9079002044140c04240c00700780c04440e40c14498165400c50160740011000d4644681000703404c0c2500c0e1050005408803906510020750343c4a01600c03600d608000600601d003824424080040a09000042003200950b240760400406004807441d180c154a401c500640114117002114101d8031310b10400c41c0c1c00d85600d810003054140140084400d10391a6100050320380d070500141103041d000d0500000c0508d4807075003508000d480060f0800a2100300803051000100c0c1c0410340b81520220702c0bc1c3c980340c190510f4140990021a00880c80403000c00007084896903100143c0388240d030542d40c00b0301541c3d903580c2409841d03014001801c1c0140c2c201d20842c1816500c210105a403200040100f8140b403540c3c4c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 185413048 1250 185411798 185411813
    0x9060b0406030f02031b03030d050619030f0308132409060e0a0c0504050402010c0f0c08030403060606180b031b0904050702060f0f040b0402010507081b03030108010605010221090d 79
    0x1540112078600154407010254030f005d0180310406c0396000001003c500403040066200c4c811641508001c95030362020030026142e1040c00403001070708480400080307440c0d081100001841280860000780d440740000d034102c02b1030340c040e00500d501c90542020b034005c2c4400300e907002154015841c0e40c144d891030a0004501c50b4000c140400040074050071040f601402c04041e80007043e0801e40c02a030900b0107110042c0d902030380c007403690754102d040407096604600d08603e07104240d0344400403d100c08074010080c09420b50100e4100c0311980c8071124441400c7e602511080400d10402e412600103100007450740301010311502c0f4900094481d10b00d0b0030b041b1400982198420f64440005a100804110090001e2807140b60080082c0d07102c15128038140e5642c00721030300c00800033410440c000c28401c04125200c010b8403c2d041003441d5881d12000d4a00704507669030400d10850030690300b440300014142d4004a814558284988000001542007102032291a4004201544c01140c01101c2402181c0c20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 185414298 1250 185413048 185413061
    0x102060115020309090403090906090501030b0a0504020102030c0a1101080f04030c1202031c020a0f08040f12051c050405070605120a020307020705031c0905100f0309020102010b03070e0907090c05030a09060b04 92
    0x1a84681c1108c9050185035801c1320b84903080002d00d1850040140f010400e2080c00543c400707820f00001c5130607511440101d081d8054920020174030312920800e542042100b411540002c00281da03070b00764554030340840600c11001610080c000c00c2d122101c4501151080d200c40080c6102401101d146c00001c41c1c0c0446100c00902c03a0402c055804284040e080358011410654140146400382c083e007001e03160a51b041240784802070009420000c2c50f00903a000300181e45110f600f421050036820b541d44c1c3e0080160074126070450fa18001c407030010407500d0049050782ca2041800040790415a20800100001c3d48064000b1055215803c00040c4d00ea4040020717030050464280b02c1210b0080350b000c0581038158541020f44200e00312020303104c44650080c0c1101d201703095480d01240d00102c3e0300040c1d0050140c009003507010f014031000803c1c0d28601101c036601525aa80480d5800d030355030f03009102201c0040311143c1c005942000820250103107604107050030b138084c0c040003400501e914005011a071a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 185415548 1250 185414298 185414303
    0xf06040b0a5406090501050903040510081314030714160303030504080c0304030c090c03140c0a03110d0c120515063a0f090b01050418050106060809071401020601150203090904 77
    0x4541c1e5a002c10840d0a001d2141c06c0701c1c23584025418903060000103525100888071100030409080c0001d07186a01c00c107840c1461642150404003041088102c19440340c3c0451000d0706d000c03101e80c0d88602a00d0300001c81805450007107807040c0c81c0500b5580c0481c007801c001781050301c401209105501d091742c0c00b40700400080d0b2040115801d41d9140400c403100b6a810240560149403400240d00e001d00b0314130340d5003503004105c00c0650f07683e9407910206400404540c07504008a00f000308101000f40095070000c1e0900c101c645a103091401000e80358000e4800c100c0e48103400034030103001821700c1c0c10408041c01d03140c042032501813040c403d45000144121071004401c08050303100e060840902e0210300c14040e072500a24028401340ea6151101c040074101881030300d0060307036280490301c943c6480b8221442e40940c8500217014003556200020710410054032620600e00651100083c0510220003165407181d06070040d249681c6009a402c1e862032001c2501c105502042020f07208542d280303e4011300c110b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 185416798 1250 185415548 185415551
    0x100b160b090a050f030a0807080a1b0806011b0203070308070512030f0106080105240a02011401090b041514060d0603140d02060c0a09030206070201020f06040b0a5406 73
    0x206810014a0081c2c3c0100e014240d8204000c9200c2541e40b018805508c0102424901481d031070b41c40000000b4141181481e80700b106500a141c00f05601c000c105014074001d90303a0400007540d01203041d002032180e85c002075042c1d00101040000a40072009843c502d4050015201c204650100b1317601715a0045a1000c4490301c3c020052201d103030090541405081c0a5980701000c4040381139101e0040d00c28003006000740400315406203054400d401c100680210780a2600d201d5a5503802c6002521002400d90f1140b03003071502541c13250710f110810104546092240003080c40b40c1400303001c2c0746ea02c403c1005d80c03c140c89001c04408206c0010303600c091101c1000003040d050b86581d20085c10050047c0203072203405010410740c0980c03a40304407101c007940c0c0c04950749a610003040c0300503071074440c0c0031a4039803043c0500000c1006102e06008040d1041d0780a45d801d100c00c40350700380d203c0055040024040c07421004001030907040e40902c02d40301030180c05d0381480c1c0668403415500009811084a0403980e55 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 185418048 1250 185416798 185416813
    0xb120411060d02091c1101031a04021b01051303080a09030306050a030f02010f09060903110604080f0610090b060d0f14240319021002010b09101409100b160b09 70
    0x10b007002c4174140c034010b0215210200b10388a0b5a211090341101c000b8843c10142c440c2841c80c8015a01a0340154801d0002d00c115907502041c0c02e40e03404000030280d091903075460140028810b8031540b44000c051685a50345003000d50310715282c0310040c40e098000394205660b402004c103035601d466041102071802008180c004446902c00100042a604035100400c01003210030805150002e410740280d941c09003034107145c6090704021842e18001c81d4803641203441088244440704102065250007034040303101d02e13407406448904140c00e407800d029402e50030071405c1041c144150540d600c11811000c00300d5011542c090f035005c140c14555001e45a107001040c8201c01a0044251420b10503510f503401e07006040c0c0ba05900b02c141d101068010000f074040c00c500482004030038400e5220300b41c4444000c01e83c4001e41050000c0d41c081e21214000c20085281080c5610a185051b4544a01c2540c0d00d180c41d21403d820008400c10581004c80941004660001c4120001c0c04215801d48150021030040059 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 185419298 1250 185418048 185418067
    0x1b0513060e1003080306060717030a1508010618020a11011505190b030105011808010c02060402090a0203100b1e0418110315010810050907030f0c090b120411060d02 72
    0x840e0700c080c0c29400118020842040098000c60a9035803000089a005440350050b040c0509907968492014105207000001c018150810780d20071440b40d84c0c03c1803202ea0132a15503460341d003252041c0c041c000705e50700383c01802d004020081d0001c082d124014540340d0311503202e1001890948105100c294288904588144040d040c51013134240d0107c2e007590082540c0f482c01c0a02c1e0a0b912060080c3c2e4108240c0e182c00b08001169400701c01d00401d0030758000c000042e06800020f490b0581540d0403032044102c003021644a400741d0003584c0c000d200c0d074180555081d00d0503000c1405580000700001c00f55000701d80942e250290b02001e08000c00841d6444001c1c00762204d81c03031044031101c1c004000d0141041c024020340044005108070040030a003019a484c2d25600302c0700750800d02d140d20aa80c48030901040001a83d815000060304000d0700070b0a0090071114002503492050034098030355804070500c000c000c1d00158115194001d4002c0301c1a406100206001c500a0b0380b00424420b602500010380044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 185420548 1250 185419298 185419319
    0x2100e040f020a0c3827060f0402120d120c0813030309081605010c0e010206132003250509010b0d05060102010b04020d060e160801031b051306 63
    0x31544a400440c5006841440540103101d19000170b04641c0001c61401c1d00301e000105400e01c07152500c4071060402010340301c1c0c8401004101c6d003107591034003500c0b1101c48005814442d80c003110001d1020f044959150034240c00042ca004005a070300c00c82d111011404274009100501100d0859aa025040c150006506055441c01c840010800001204010030002c46401c4c130f2040030303454603011591140701d0508544034014401805100000d48041c801080815803140d0301103600e40d1190302c00c030700006005a03180c0d13804440103c2c012034031424040019414095010386010b034240c60031201c05894010a01d030048884201d4031318150050302e1110a109400b110004280880f1b55910b9581007a0020016018a107a400106a00d81020070031603030007134010022030900a4021510b850803110410068606446a0749903402d0700c00101d0b40728605c0d02c42c02e80ca03400d115107500410b1792855888a90f0032101142d07600b04813469580100b880d83d070303c11480c855184281000706105040040610 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 185421798 1250 185420548 185420561
    0x603070c0b090307030905060a1101050109051807051f0201021b0c03060c0901051c02160803101a1b070305030a05030412020c010e040f0b150703030e0a08121302100e04 74
    0x540a82c014407412001a034031aa61b00e0582d041650040d848892000e015282d01d015100d0440040d4240000807c009099510140c0f2402e04034603405210700300c584660392a5074140c002c5680200c080d0290301d80e2820042800c101d0325959100040c035205280114a4014181c045130120a070070a4038100024501003100a420003450340d2428502000413002808074483e510007001035501e050708154110344182d040e41c108000841141030001414174010302d0b140d0045881c5d540d0540861404035207500415111145101244120303407030702c840811440461240031407841002e1084106c084001841403016000c008543d0306d803944c4030305040c0f404200740032000000904640c00f038100705c4060383c0d00c510040c90482c025640003403482e0303080c2d030724201500e200541641c20079052641c00f512071a8a80040c81d55501a03074080009190300442103880f200c001c03c0103010900188480181c548420f800c1940010100340d40c0f041c01025603010a4100c0801e1040701c000c604080c0440120342403e0043d03c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 185423048 1250 185421798 185421811
    0xf01091403040602190309080118031206081b0a03120e100c08030406150f0803040e0a0c081902161a010501090f09051305030f03100b040f03021e0603070c0b 69
    0xc1d428103050807030081d96a602c0c422125803a080c442c040d1024103008100034805800300d900280010006620380d0329400c070544038100c000825103c003029244116200d0704040e01c181c00050900c0303000714905420031007039035401d0740c4c0d220811110000001d14120300705100b45131181c4580ca54082d03c2001c000740024010a650144450001000001840076048a41c00344d03203d480080d4030340b203214910841040581209000341c0b2007030000701d025100000a80221890200f940d0754583d0b4030300082094481080014003c06d00307150106001100100401100c801612070050400c48001400a0100301001c0300f504d801c149284802c00c060b14000700c0a0140000b800c004aa171890420300340100c07031851258843c1c0c107076a0030205104001d02e20102d80d003160404101da8448511140321409030380140d0f451821509540d01c0010303820705c0d20050f20104d0703d43c42c003003800c03082c5035409014240c0c41d1146403100540e42800d071300206603100809180590400d075070300c81034407207503142140969102400d003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 185424298 1250 185423048 185423053
    0x71b0e0415090609020a06020717072912011d06030f0303070509011b0b010f0f0501020307110f120705040b030303060d030e190303020607030b0f0a0501030b060c0f010914 75
    0x4200c041003084284410552449100080007001420903800900340c4010095200f81c410340009a11980028927406559400a40f0880a240200b215036208100d00c1202d28007c9580e10484c40c465041900c400028810803145d441d1101255505e99021426009155104c104120a008070040f4501c0d180c1c0c400c0b020f0300180740d0101844c9895959010003058201000b00c002003012180c0d2040da0218050154042c038210201900d103000d052010090184103402c074000c8000003814441035918508aa0060300918035150090700c0340e0000e20310708d480c8290400074483c882c29280d1101d00c1c03080000c0e00204003510800e42002d080105071030850015a102c1d901c18014010300c0e175102c03402c0320078160b81410482400750030b071004100000014442c03189240461280041071640101c1d507944108020780d420481141036034200401148000503103038120841034800c1c051b80d4000c5d805014581801414076080c200e0003a030040ca080410031009005945070250a801c010070b0084001440041c03c2c007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 185425548 1250 185424298 185424301
    0x7020109030b090f01020c0c030c010f050423120c011107030c0e0a1413050601060507050a03030f0f060f05040c0801050603131505090a11060307050a08150303071b0e 73
    0x80c5440114000a02003078003000100c0c2c0f0f0a1401c104030082c0e9007a0b00c00a5444108084603982c4820a007034425000f030048007250b070f59a44c07141030a183c4000c4c80d40c0300c0d2420b081c20540b0020142800d802c1400040c4082c01c0a06020703503401901d5130000035444001d19a00da1140001848580c0102d9040038581c03107448240005492080c1190a0b6203120180700010781d9000f161402404044040c050300d1185d840a01c031040e0a0f1550907a0110b0080b0111510b40c0d03a0745c00c040f140d89c85081703406080ea400942c00c03500081d20070f030000300308542811000301ea0428541000f404076640c562118140780c0008404115508140c06115845105030418a20962510000c07801d1488010a4041041c0041c81010200042da51141c48920300b17aa0080103140b41c0904155a241120744c001e8441c020b0030002d14009150000440784140d459a807064200045104243c0700d0311000342900c9290590040d000d2181e031810009000d00902400c0303ca4456541c004000300728400340e41122042c03d50301c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 185426798 1250 185425548 185425553
    0x20414190501210203070f030b010f060c0b060d0f141005060906010e06031308030c030411040920010c050307030801061206080309150c07080304090b040216020105090105040312050a110307 83
    0x990100b5103080003c00800c80340364400a42024801d410248107400070001c00f01c244001c945015050f1001c00c40c025001c15140d100540c0c02a1403044000d00c0300c48504001605424440f0040000500c20114412005c005644a003080407602341601000c0c0e200440d6400391361050300801c0d8100c8401c0e00d4850250400b40300007003d2030324011344140242d100101141c1f4000c0c1c6c414202e6446500300341c0c01a00c7e401c05c02944e15030341d8400d03141640c070003104810300c400754030b010302c80d07101401e5111107110301d040c084500c0c01888207016190a414002806109008035100380018040c451207503a03080c2181d81022005841219910f80b50241c00303140c610b083c0f054510003c101d0350f40000c11500785010646050841c9050301c205c8100c0201802503080000e402c40000000d80b080e1510380000f8000000364009200890280c42002c02480d201448503002550007070000b001045810301d0440e00d840d0b02c0e0380307640444108652400f000540d0001e60401602d900c598030028400d50103000d1803501d0100d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 185428048 1250 185426798 185426819
    0x120f010b120309011110050c0403020111011a13060806090a0501110f0f0306040209180105100e0a05060a1106010e09070e04080a030b03070f06050706060b0310090b0409020414190501 80
    0x85802c541444800945c4030aa2142040028070141c9000014029841d181811100b113421601c0124085007011540c2d0b45280300600950340c80949444090140d180d1460070403001b0041280c003c07451130b07a00c1a01049144050003a82d201d0001e500040c182c010179031402900312402c811604220312814810280304800410031140034142c0710100c03644980380c0302c00040c0240714044d4402da114480018100041c081080c1c4036040320740031540e00c80f1030600e41105a581d1002c0218440d8407481001c2d0500191a000e0081d220b01c140f1494111b400c0301c81450464901402a08a5121603201c0010000c1d1108200f0038100688140e0000c0102420291b84003d081c0c052004030300203142c0c03180c10400c203517203040040d0070080002c408800710041ea07038580034105900030310b401c1e0380c02410000081903604480742241d005544c120390800e03c95141c004058000c0a1050a06070f02680751200320740035a4550140280341c04005d01200494100713017100000502081600b420481d00300001080440c810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 185429298 1250 185428048 185428057
    0x40f06110312040c12260301050a0303121512140109030503040f02150a050a14070c05010804060f050c0a0e1002120714060a0504031107180b03010902120f010b1203 72
    0x1124a00c2219222491301d90208506608800c12081809400f2000e01c0401c0d0405490b11801070f14000d210442c1343e84689052100b401441e8010194000c01c00020b80b044600040c5c21190030030004441d5403028a0042d01c020960081c40d050300080d403582e041c000e100c02c0d40c44960300c0b1840200f080310794995019040f40030050014082d0303030300a04514155281d200c0d2030340c1081c4035004003640d1707007030b01200142c11504884882d40000c0c580e0540502a10189422a5815074002908001c07542c03501004503510040200116040c0b40c80d41006400c41080b80101402500d544524540380c000203a00213000b00c3d042c2c130f903d51044041c065940e005623004541c4907406c411130700c2c4103a56034115040500d45c00e051214104502d04c161010020580030581c0300350f015921a59600400d10481c5844a940e07130501d004009807801050300c034072003410791a40705548154026001140c14507060300011823810f00c6054188a0342c0040950f0002d00c0020320442400c403004482640b10302d100302e846650760340034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 185430548 1250 185429298 185429317
    0x1814060609040f140d090801060506030f010312050c010c05120703140a05090f070f06020c09010609050105210703050f01090c091a070b1617010605031501030e03070602040f061103 79
    0x101c940008107010341c140b1000800302d55001161151084284006e0810b00d00d40300b130711a41c1d440c2540c00301c0c0a16299049a000e90303000400b121441c3d0868071100b03007048042d102c00302402003c000082401c4c0c4203000e618140c1825132519510348003030a0307007010309840003004602094a0001c40c020504000c01ca81c0780c2005000c1000100c583da0180124580b042c0205003105074482d0803c0020000c0c01040000c0903a030030340e401c0d0741002c2011014001010001c1c0a540003007002140180155485000682030b0200003100140c801580300b00c1218110b1001e65019002988078020000303a013640c807021500402c03014804015403810184000d02c0000640900c45050b0102c00c3d51035105281001600c000070303002550b4210b107081c0107400c64100d80c00101c2c0300010640d42d880b03818500c0140510310303049682d43e4480600d16503400c400380d03031540c114180c824141039448034902d440601c01c20281468038403031100165602e08140c4030301d00080c0030703074002c804110b00003040b00340388000402070340e000c0320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 185431654 1106 185430548 185430563
    0xd02040914070c110a090c030b01020c0a1a070804030501060b07050111040e011e0f1205150c040e102301030c08152101181406060904 59
    0x507030448112021640003540d00010401451032140402c1d0024034a04901351201a481d08030b034043c401940000c1c1c0d64032031500a84d42c0412260100ba0f40445842d62024a0140c00c3c0e080c0070f946a0140c151344c40082011420055541c0a6502071680840240503040e1102d40300c0318550400e1000f503969600706082c1903121081502118191140c000b80a4020382c24682c200a15044110f010801d281481708d000906201402ca00030140c0348140c40e4225040e0070707090040c0303803c0b40b034244c0c017175a41c80c40c005008a060032a0216421202d40100d0701c40169143c95100c0f1036010320358041e0309000e05803101c40d0800c03402d42c440f0071094030b826207040140d005500000c99100c44e08544690000b2100d40120309249001e490740342851591140016841000111107801d48070003082c9800c115245040c040304101403883c8410701c0405543c02403d0916102c070001c1c54044020f071001e01141c = true := by decide +kernel

theorem cover : BRFrame.Cov 185251798 185431654 := by
  have h0 := BRFrame.cov_init 185251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 185251798 ≤ n) (h2 : n < 185431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
