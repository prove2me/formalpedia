-- Prove2me | solution 1 for CollatzFrontier.syracuse_uniform_descent_of_descent
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T17:26:43.199353+00:00
-- url     : https://prove2.me/submissions/fdd6643e-8bf1-42a6-ae03-84197778da2c

import Definitions.Def_syracuseStep
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-
Self-contained solution. All helper lemmas are inlined (and renamed under
`CollatzFrontierAux` to avoid any clash) from the private repo
`collatz-frontier` (commit 4d656b9c9c5815305bd391f206c9d3e9587dd395),
files `lean/CollatzFrontier/AffineStep.lean`, `TerminalBudget.lean`,
`UniformDescent.lean`, `AffineDrift.lean`. No repo module is imported.

The target drops the hypothesis `hm : Odd m` from the repo declaration
`CollatzFrontier.syracuse_uniform_descent_of_descent`: the proof below never
uses it (exactly as the repo's own `syracuse_uniform_descent_terminal`
documents with an explicit `clear hm`).
-/

namespace CollatzFrontierAux

/-- A power-of-two factor supplies an upper bound without fixing the valuation. -/
theorem syracuseStep_le_of_pow_two_factor {x y e : ℕ}
    (h : 3 * x + 1 = 2 ^ e * y) : syracuseStep x ≤ y := by
  unfold syracuseStep
  rw [h, Nat.ordCompl_self_pow_mul y e Nat.prime_two]
  exact Nat.ordCompl_le y 2

/-- Exact affine transfer; oddness is required only for an exact step. -/
theorem syracuseStep_affine (e : ℕ) {b A c D q : ℕ}
    (hc : 3 * b + 1 = 2 ^ e * c)
    (hD : 3 * A = 2 ^ e * D)
    (hodd : ¬ 2 ∣ c + D * q) :
    syracuseStep (b + A * q) = c + D * q := by
  unfold syracuseStep
  have h : 3 * (b + A * q) + 1 = 2 ^ e * (c + D * q) := by
    calc
      3 * (b + A * q) + 1 = (3 * b + 1) + (3 * A) * q := by ring
      _ = 2 ^ e * (c + D * q) := by rw [hc, hD]; ring
  rw [h]
  exact Nat.ordCompl_pow_mul_of_not_dvd e Nat.prime_two hodd

/-- Affine coefficient propagation under a finite power-of-two budget. -/
theorem coefficient_factor {K S e i : ℕ} (h : S + e ≤ K) :
    3 * (3 ^ i * 2 ^ (K - S)) =
      2 ^ e * (3 ^ (i + 1) * 2 ^ (K - (S + e))) := by
  have hs : K - S = e + (K - (S + e)) := by omega
  rw [hs, pow_add, pow_succ]
  ring

/-- Source-shaped terminal-budget transfer. Only the earlier quotients must be odd. -/
theorem syracuse_terminal_budget
    (a b : ℕ → ℕ) (r K k e B : ℕ)
    (hstart : b 0 = r)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hodd : ∀ i < k, Odd (b (i + 1)))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (he : 0 < e)
    (hbudget : (∑ i ∈ Finset.range k, a i) + e ≤ K)
    (hcontract : 3 ^ (k + 1) < 2 ^ ((∑ i ∈ Finset.range k, a i) + e))
    (hdesc : B < r) (q : ℕ) :
    syracuseStep^[k + 1] (r + 2 ^ K * q) < r + 2 ^ K * q := by
  let S : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, a j
  let A : ℕ → ℕ := fun i => 3 ^ i * 2 ^ (K - S i)
  have hsucc (i : ℕ) : S (i + 1) = S i + a i := by
    exact Finset.sum_range_succ a i
  have hmono {i j : ℕ} (hij : i ≤ j) : S i ≤ S j := by
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)
  have hremaining {i : ℕ} (hi : i < k) : S (i + 1) + e ≤ K := by
    have hh := hmono (show i + 1 ≤ k by omega)
    change S k + e ≤ K at hbudget
    omega
  have hcoeff {i : ℕ} (hi : i < k) : 3 * A i = 2 ^ (a i) * A (i + 1) := by
    dsimp [A]
    rw [hsucc]
    exact coefficient_factor (by have hh := hremaining hi; rw [hsucc] at hh; omega)
  have heven {i : ℕ} (hi : i < k) : A (i + 1) % 2 = 0 := by
    have hpos : 0 < K - S (i + 1) := by have hh := hremaining hi; omega
    have hexp : K - S (i + 1) = (K - S (i + 1) - 1) + 1 := by omega
    dsimp [A]
    rw [hexp]
    simp [pow_succ, Nat.mul_mod]
  have hpref : ∀ i, i ≤ k →
      syracuseStep^[i] (r + 2 ^ K * q) = b i + A i * q := by
    intro i
    induction i with
    | zero =>
        intro _
        simp [A, S, hstart]
    | succ i ih =>
        intro hi
        have hik : i < k := by omega
        rw [Function.iterate_succ_apply', ih (by omega)]
        apply syracuseStep_affine (a i) (hstep i hik) (hcoeff hik)
        have hc : b (i + 1) % 2 = 1 := by
          obtain ⟨u, hu⟩ := hodd i hik
          omega
        have hmod : (b (i + 1) + A (i + 1) * q) % 2 = 1 := by
          simp [Nat.add_mod, Nat.mul_mod, hc, heven hik]
        intro hdvd
        have hz := Nat.mod_eq_zero_of_dvd hdvd
        omega
  let D := 3 ^ (k + 1) * 2 ^ (K - (S k + e))
  have hDfactor : 3 * A k = 2 ^ e * D := coefficient_factor hbudget
  have hbound : syracuseStep (b k + A k * q) ≤ B + D * q := by
    apply syracuseStep_le_of_pow_two_factor (e := e)
    calc
      3 * (b k + A k * q) + 1 = (3 * b k + 1) + (3 * A k) * q := by ring
      _ = 2 ^ e * (B + D * q) := by rw [hfinal, hDfactor]; ring
  have hDle : D ≤ 2 ^ K := by
    have hlt := Nat.mul_lt_mul_of_pos_right hcontract
      (show 0 < 2 ^ (K - (S k + e)) from pow_pos (by decide) _)
    have hsum : S k + e + (K - (S k + e)) = K := by
      change S k + e ≤ K at hbudget
      omega
    change 3 ^ (k + 1) * 2 ^ (K - (S k + e)) <
      2 ^ (S k + e) * 2 ^ (K - (S k + e)) at hlt
    rw [← pow_add, hsum] at hlt
    exact Nat.le_of_lt hlt
  have hmul := Nat.mul_le_mul_right q hDle
  have hgap : B + D * q < r + 2 ^ K * q := by omega
  rw [Function.iterate_succ_apply', hpref k le_rfl]
  exact lt_of_le_of_lt hbound hgap

/-- Every Syracuse step has an odd result. -/
theorem syracuseStep_odd (n : ℕ) : Odd (syracuseStep n) := by
  apply Nat.odd_iff.mpr
  have hnot : ¬ 2 ∣ syracuseStep n :=
    Nat.not_dvd_ordCompl Nat.prime_two (show 3 * n + 1 ≠ 0 by omega)
  have hne : syracuseStep n % 2 ≠ 0 := by
    intro hzero
    exact hnot (Nat.dvd_of_mod_eq_zero hzero)
  have hlt := Nat.mod_lt (syracuseStep n) (show 0 < 2 by decide)
  omega

theorem syracuse_iterate_odd (n : ℕ) (hn : Odd n) (i : ℕ) :
    Odd (syracuseStep^[i] n) := by
  cases i with
  | zero => exact hn
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact syracuseStep_odd _

/-- Terminal-descent transfer across a residue class. The source API also
carries `hm : Odd m`; the proof below never uses it. -/
theorem syracuse_uniform_descent_terminal (a : ℕ → ℕ) (m m' K t : ℕ)
    (hm' : Odd m')
    (hcong : m ≡ m' [MOD 2 ^ K])
    (hstep : ∀ i < t, 2 ^ (a i) * (syracuseStep^[i + 1] m') =
      3 * (syracuseStep^[i] m') + 1)
    (hbudget : (∑ i ∈ Finset.range t, a i) ≤ K)
    (hgt : 3 ^ t < 2 ^ (∑ i ∈ Finset.range t, a i))
    (hdesc : syracuseStep^[t] m' < m')
    (hle : m' ≤ m) :
    syracuseStep^[t] m < m := by
  cases t with
  | zero => simp at hdesc
  | succ k =>
      have he : 0 < a k := by
        by_contra hnot
        have heq : a k = 0 := by omega
        have hlast := hstep k (by omega)
        rw [heq, pow_zero, one_mul] at hlast
        obtain ⟨u, hu⟩ := syracuse_iterate_odd m' hm' k
        obtain ⟨v, hv⟩ := syracuse_iterate_odd m' hm' (k + 1)
        omega
      obtain ⟨q, hq⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hcong.symm
      rw [hq]
      exact syracuse_terminal_budget a (fun i => syracuseStep^[i] m')
        m' K k (a k) (syracuseStep^[k + 1] m')
        rfl (fun i hi => (hstep i (by omega)).symm)
        (fun i hi => syracuse_iterate_odd m' hm' (i + 1))
        (hstep k (by omega)).symm he
        (by simpa only [Finset.sum_range_succ] using hbudget)
        (by simpa only [Finset.sum_range_succ] using hgt)
        hdesc q

/-- The scaled representative orbit grows by a nonnegative affine intercept. -/
theorem dyadic_chain_growth (a b : ℕ → ℕ) (k : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1)) :
    3 ^ k * b 0 ≤ 2 ^ (∑ i ∈ Finset.range k, a i) * b k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := ih (fun i hi => hstep i (by omega))
      rw [Finset.sum_range_succ, pow_add, pow_succ]
      calc
        _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) := by nlinarith [hp]
        _ ≤ 2 ^ (∑ i ∈ Finset.range k, a i) * (3 * b k + 1) := by
          calc
            _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) +
                2 ^ (∑ i ∈ Finset.range k, a i) := Nat.le_add_right _ _
            _ = _ := by ring
        _ = _ := by rw [hstep k (by omega)]; ring

/-- A final `+1` supplies strict drift; representative descent implies contraction. -/
theorem terminal_power_contraction (a b : ℕ → ℕ) (k e B : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (hdesc : B ≤ b 0) :
    3 ^ (k + 1) < 2 ^ ((∑ i ∈ Finset.range k, a i) + e) := by
  have hp := dyadic_chain_growth a b k hstep
  have hpow : 0 < 2 ^ (∑ i ∈ Finset.range k, a i) := pow_pos (by decide) _
  have hx : 3 ^ (k + 1) * b 0 <
      2 ^ ((∑ i ∈ Finset.range k, a i) + e) * b 0 := by
    calc
      _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) := by rw [pow_succ]; nlinarith
      _ < 2 ^ (∑ i ∈ Finset.range k, a i) * (3 * b k + 1) := by nlinarith
      _ = 2 ^ ((∑ i ∈ Finset.range k, a i) + e) * B := by rw [hfinal, pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hdesc
  exact Nat.lt_of_mul_lt_mul_right hx

end CollatzFrontierAux

open CollatzFrontierAux

theorem solution (a : ℕ → ℕ) (m m' K t : ℕ)
    (hm' : Odd m')
    (hcong : m ≡ m' [MOD 2 ^ K])
    (hstep : ∀ i < t, 2 ^ (a i) * (syracuseStep^[i + 1] m') = 3 * (syracuseStep^[i] m') + 1)
    (hbudget : (∑ i ∈ Finset.range t, a i) ≤ K)
    (hdesc : syracuseStep^[t] m' < m')
    (hle : m' ≤ m) :
    syracuseStep^[t] m < m := by
  cases t with
  | zero => simp at hdesc
  | succ k =>
      have hc := terminal_power_contraction a (fun i => syracuseStep^[i] m')
        k (a k) (syracuseStep^[k + 1] m')
        (fun i hi => (hstep i (by omega)).symm) (hstep k (by omega)).symm hdesc.le
      apply syracuse_uniform_descent_terminal a m m' K (k + 1) hm' hcong hstep hbudget
      · simpa only [Finset.sum_range_succ] using hc
      · exact hdesc
      · exact hle
