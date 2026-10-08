-- Prove2me | solution 2 for AvramDividend.Classical.continuousOn_cumulative_toReal_of_ac_positive
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T14:07:24.526031+00:00
-- url     : https://prove2.me/submissions/06d3a3db-d18f-449b-a975-f4975108fba0

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal

/-- If every lower cumulative interval has finite mass and the restriction of a measure to the positive half-line is absolutely continuous with respect to Lebesgue measure, then its real-valued cumulative function is continuous on the positive half-line. -/
theorem solution
    (β : Measure ℝ)
    (hfin : ∀ x : ℝ, β (Iic x) ≠ ∞)
    (hac : β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ)) :
    ContinuousOn (fun x : ℝ => (β (Iic x)).toReal) (Ioi (0 : ℝ)) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hx0 : β {x} = 0 := by
    have h1 : β.restrict (Ioi (0:ℝ)) {x} = 0 := hac (by simp)
    rwa [Measure.restrict_apply (measurableSet_singleton x),
      Set.inter_eq_left.mpr (by simpa using hx)] at h1
  set ν := β.restrict (Iic (x+1))
  have key : Tendsto (fun y => ∫⁻ z, (Iic y).indicator 1 z ∂ν) (𝓝 x)
      (𝓝 (∫⁻ z, (Iic x).indicator 1 z ∂ν)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun y => (measurable_one.indicator measurableSet_Iic)
    · exact Eventually.of_forall fun y => Eventually.of_forall fun z => by
        simp only [Set.indicator]; split_ifs <;> simp
    · simp only [lintegral_const, one_mul, ν, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact hfin _
    · have : ∀ᵐ z ∂ν, z ≠ x := by
        rw [ae_iff]; simp only [ne_eq, not_not]
        have : {z | z = x} = ({x} : Set ℝ) := rfl
        rw [this]
        exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hx0) (zero_le)
      filter_upwards [this] with z hz
      rcases lt_or_gt_of_ne hz with h | h
      · have : ∀ᶠ y in 𝓝 x, z < y := eventually_gt_nhds h
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [this] with y hy
        simp [Set.indicator, h.le, hy.le]
      · have : ∀ᶠ y in 𝓝 x, y < z := eventually_lt_nhds h
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [this] with y hy
        simp [Set.indicator, not_le.mpr h, not_le.mpr hy]
  have hν : ∀ y, y ≤ x + 1 → ∫⁻ z, (Iic y).indicator 1 z ∂ν = β (Iic y) := by
    intro y hy
    rw [lintegral_indicator_one measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
      Set.inter_eq_left.mpr (Iic_subset_Iic.mpr hy)]
  have key2 : Tendsto (fun y => β (Iic y)) (𝓝 x) (𝓝 (β (Iic x))) := by
    rw [← hν x (by linarith)]
    refine key.congr' ?_
    filter_upwards [eventually_lt_nhds (show x < x + 1 by linarith)] with y hy
    exact hν y hy.le
  exact (ENNReal.tendsto_toReal (hfin x)).comp key2
