-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_zero_noise_original_filtered_levy_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T16:00:53.2621+00:00
-- url     : https://prove2.me/submissions/9550961b-e908-4a0a-88c1-eecd291c81fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A deterministic zero-noise Lévy process exists on the original filtered probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = 0 ∧
      (∀ (t : ℝ≥0) (ω : Ω), Y.X t ω = 0) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  refine ⟨{
    X := fun _ _ => 0
    c := 0
    σ := 0
    ν := 0
    isProbability := X.isProbability
    σ_nonneg := by norm_num
    ν_Ici := by simp
    ν_integrable := by simp
    X_zero := by intros; rfl
    rightCont := by
      intro ω t
      exact continuousWithinAt_const
    leftLim := by
      intro ω t ht
      exact ⟨0, tendsto_const_nhds⟩
    noPosJumps := by
      intro ω t l ht hlim
      haveI : NeBot (𝓝[<] t) :=
        nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
      have hEq : (0 : ℝ) = l :=
        tendsto_nhds_unique tendsto_const_nhds hlim
      simpa [hEq]
    adapted := by
      intro t
      exact measurable_const
    indepIncrements := by
      intro s t hst
      have hIndep : Indep ⊥ (𝓕 s) P := indep_bot_left _
      simpa using hIndep
    stationaryIncrements := by
      intro s t hst
      simp only [sub_self]
      exact IdentDistrib.refl measurable_const.aemeasurable
    laplace := by
      intro t θ hθ
      have hExp : (fun _ : Ω => Real.exp (θ * (0 : ℝ))) =
          (fun _ : Ω => (1 : ℝ)) := by
        funext ω
        simp
      constructor
      · simpa using (integrable_const (μ := P) (c := (1 : ℝ)))
      · simp [laplaceExponent_zero_jump_measure]
  }, rfl, rfl, ?_⟩
  intro t ω
  rfl
