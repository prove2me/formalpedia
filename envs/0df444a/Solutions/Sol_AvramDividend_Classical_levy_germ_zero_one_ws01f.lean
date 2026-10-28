-- Prove2me | solution 1 for AvramDividend.Classical.levy_germ_zero_one_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:52:55.985163+00:00
-- url     : https://prove2.me/submissions/fee3b6b1-5c2b-45d8-b5b8-0bc9265d62fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders
import Theorems.Thm_AvramDividend_Classical_germ_zero_one_of_shift_independence_ws01f

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory DurrettProbability
open AvramDividend.Classical
open scoped NNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {A : Set Ω} (hA : MeasurableSet[germSigma X.X] A) :
    P A = 0 ∨ P A = 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hBm : ∀ t : ℝ≥0, Measurable (X.X t) := by
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hC : ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 => X.X t ω) (𝓝 0) (𝓝 0) := by
    filter_upwards [] with ω
    have hR := X.rightCont ω 0
    change Tendsto (fun t : ℝ≥0 => X.X t ω)
      (𝓝[Set.Ici (0 : ℝ≥0)] (0 : ℝ≥0)) (𝓝 (X.X 0 ω)) at hR
    have hIci : Set.Ici (0 : ℝ≥0) = Set.univ := by
      ext t
      simp
    simpa [hIci, X.X_zero ω] using hR
  have hPast (s : ℝ≥0) : pastSigma X.X s ≤ 𝓕 s := by
    unfold pastSigma
    refine iSup₂_le fun t ht => ?_
    exact (X.adapted t).comap_le.trans (𝓕.mono ht)
  have hShift : ∀ s : ℝ≥0, 0 < s →
      Indep
        (MeasurableSpace.comap
          (fun ω (u : ℝ≥0) => X.X (s + u) ω - X.X s ω)
          MeasurableSpace.pi)
        (pastSigma X.X s) P := by
    intro s hs
    have hFinite := finite_future_increment_sigma_indep_past X s
    have hWhole :=
      chat04_whole_future_process_indep_past_of_finite_cylinders X s hFinite
    exact indep_of_indep_of_le_right hWhole (hPast s)
  exact germ_zero_one_of_shift_independence_ws01f X.X hBm hC hShift hA
