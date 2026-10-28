-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:43:09.114411+00:00
-- url     : https://prove2.me/submissions/d8b8b499-c2ae-42c5-9c62-0ca71a26d208

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
section Measurability
variable {X : Type*} [MetricSpace X]
/-- Each secant supremum of a continuous function is lower semicontinuous. -/
theorem solution {f : X → ℝ} (hf : Continuous f) (r : ℝ) :
    LowerSemicontinuous (FunctionalInequalities.Energy.LocalSlope.secant f r) := by
  intro x t ht
  have ht' : t < ⨆ (y : X) (_ : dist y x < r), ENNReal.ofReal (dist (f y) (f x) / dist y x) := ht
  obtain ⟨y, hy⟩ := lt_iSup_iff.1 ht'
  obtain ⟨hyr, hyt⟩ := lt_iSup_iff.1 hy
  have hpos : 0 < dist y x := by
    rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h0 | h0
    · exfalso
      rw [← h0] at hyt
      simp at hyt
    · exact h0
  set q : X → ℝ := fun x' ↦ dist (f y) (f x') / dist y x' with hq
  have hcont : ContinuousAt (fun x' ↦ ENNReal.ofReal (q x')) x := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    refine ContinuousAt.div ?_ ?_ hpos.ne'
    · exact (continuous_const.dist hf).continuousAt
    · exact (continuous_const.dist continuous_id).continuousAt
  have hball : ∀ᶠ x' in 𝓝 x, dist y x' < r := by
    have hmem : Metric.ball y r ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_comm] using hyr)
    filter_upwards [hmem] with x' hx'
    simpa [Metric.mem_ball, dist_comm] using hx'
  have hgt : ∀ᶠ x' in 𝓝 x, t < ENNReal.ofReal (q x') := hcont (lt_mem_nhds hyt)
  filter_upwards [hball, hgt] with x' h1 h2
  refine lt_of_lt_of_le h2 ?_
  rw [FunctionalInequalities.Energy.LocalSlope.secant]
  exact le_iSup₂_of_le y h1 le_rfl
