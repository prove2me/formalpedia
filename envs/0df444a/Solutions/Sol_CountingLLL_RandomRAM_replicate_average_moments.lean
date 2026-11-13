-- Prove2me | solution 1 for CountingLLL.RandomRAM.replicate_average_moments
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:27:04.707241+00:00
-- url     : https://prove2.me/submissions/c924780f-2a91-43f8-b9b8-4a81bd3432b9

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Moment bounds for the independent replicate averages in #442 §5.3. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (L : ℕ) (hL : 0 < L) (R : Fin L → Ω → ℝ) (r p : ℝ)
    (hind : iIndepFun R μ) (hL2 : ∀ j, MemLp (R j) 2 μ)
    (hmean : ∀ j, (∫ ω, R j ω ∂μ) = r)
    (hvar : ∀ j, variance (R j) μ ≤ 3 * p) :
    let X : Ω → ℝ := fun ω => 1 - (L : ℝ)⁻¹ * ∑ j, R j ω
    MemLp X 2 μ ∧ (∫ ω, X ω ∂μ) = 1 - r ∧ variance X μ ≤ 3 * p / L := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  let S : Ω → ℝ := fun ω => ∑ j, R j ω
  let A : Ω → ℝ := fun ω => (L : ℝ)⁻¹ * S ω
  have hS : MemLp S 2 μ := memLp_finsetSum Finset.univ (fun j _ => hL2 j)
  have hA : MemLp A 2 μ := hS.const_mul _
  have hX : MemLp (fun ω => 1 - A ω) 2 μ := (memLp_const (1 : ℝ)).sub hA
  have hSmean : (∫ ω, S ω ∂μ) = L * r := by
    simp only [S, integral_finset_sum Finset.univ (fun j _ => (hL2 j).integrable (by norm_num))]
    simp [hmean]
  have hAmean : (∫ ω, A ω ∂μ) = r := by
    rw [show A = fun ω => (L : ℝ)⁻¹ * S ω from rfl, integral_const_mul, hSmean]
    field_simp
  have hXmean : (∫ ω, 1 - A ω ∂μ) = 1 - r := by
    rw [integral_sub (integrable_const 1) (hA.integrable (by norm_num)), integral_const, probReal_univ]
    simpa [hAmean]
  have hSvariance : variance S μ = ∑ j, variance (R j) μ := by
    have h := IndepFun.variance_sum (μ := μ) (s := Finset.univ) (fun j _ => hL2 j)
      (fun i _ j _ hij => hind.indepFun hij)
    have hSe : S = ∑ j, R j := by
      funext ω
      simp [S]
    rw [hSe]
    simpa using h
  have hsum : (∑ j, variance (R j) μ) ≤ (L : ℝ) * (3 * p) := by
    calc
      _ ≤ ∑ _j : Fin L, 3 * p := Finset.sum_le_sum (fun j _ => hvar j)
      _ = _ := by simp
  have hXvar : variance (fun ω => 1 - A ω) μ ≤ 3 * p / L := by
    rw [variance_const_sub hA.aestronglyMeasurable, show A = fun ω => (L : ℝ)⁻¹ * S ω from rfl,
      variance_const_mul, hSvariance]
    have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (L : ℝ)⁻¹)
    have heq : (L : ℝ)⁻¹ ^ 2 * ((L : ℝ) * (3 * p)) = 3 * p / L := by field_simp
    exact hh.trans_eq heq
  exact ⟨hX, hXmean, hXvar⟩
