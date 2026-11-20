-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_uniform_physical_stopped_fullmark_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:36:35.053171+00:00
-- url     : https://prove2.me/submissions/c9b9a872-aadd-4cc4-83f7-d080e459bef2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_clipped_prejump_gradient_full_cutoff_L2_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
set_option autoImplicit false
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (j n : ℕ) :
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 ∧
    (∀ ω, τ ω = 0 → ∑ i ∈ Finset.range n, Z i ω = 0) := by
  intro grid N r H Z
  have hGrid : ∀ i, grid i ≤ grid (i + 1) := by
    intro i
    dsimp only [grid]
    gcongr <;> omega
  obtain ⟨hL2, hMean⟩ :=
    avram_p4_s3_interval_i_original_stopped_discounted_clipped_prejump_gradient_full_cutoff_L2_zero
      X x D hD w q K hK cut τ hτstop grid hGrid n
  refine ⟨hL2, hMean, ?_⟩
  intro ω hzero
  apply Finset.sum_eq_zero
  intro i hi
  change (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i) = 0
  have ht :
      (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0) := by
    simpa only [hzero, WithTop.coe_le_coe] using
      (show (0 : ℝ≥0) ≤ grid i from zero_le)
  simp only [if_pos ht, zero_mul]
