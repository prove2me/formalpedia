-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_laplace_quotient_integrable_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:42:18.514099+00:00
-- url     : https://prove2.me/submissions/219f79ac-40b7-4ae2-a370-cac15e6566b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18_standing_X_integrable_fixedtime
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_X_abs_plus_exp2_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_scalar_exp_quotient_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_laplace_quotient_integral_normalisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Uniform integrable original-space control of the positive Laplace
    difference quotients and their exact integral normalisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      let F : ℝ → Ω → ℝ := fun θ ω =>
        (Real.exp (θ * X.X t ω) - 1) / θ
      ∃ bound : Ω → ℝ,
        Integrable bound P ∧
        (∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0),
          AEStronglyMeasurable (F θ) P) ∧
        (∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0),
          ∀ᵐ ω ∂P, ‖F θ ω‖ ≤ bound ω) ∧
        (∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0),
          ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ =
            ∫ ω, F θ ω ∂P) := by
  intro t
  letI : IsProbabilityMeasure P := X.isProbability
  let bound : Ω → ℝ := fun ω =>
    |X.X t ω| + 1 + Real.exp (2 * X.X t ω)
  have hEnv := avram_ja18g_original_X_abs_plus_exp2_integrable X hX t
  have hBoundInt : Integrable bound P := by
    have hh : Integrable (fun ω =>
        (|X.X t ω| + Real.exp (2 * X.X t ω)) + 1) P :=
      hEnv.add (integrable_const (1 : ℝ))
    convert hh using 1
    funext ω
    dsimp [bound]
    ring
  have hXInt := avram_ja18_standing_X_integrable_fixedtime X hX t
  have hMeas (θ : ℝ) : AEStronglyMeasurable
      (fun ω => (Real.exp (θ * X.X t ω) - 1) / θ) P := by
    have hc : Continuous (fun y : ℝ => (Real.exp (θ * y) - 1) / θ) := by
      fun_prop
    exact (hc.measurable.comp_aemeasurable hXInt.aemeasurable).aestronglyMeasurable
  have hpos : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < θ := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact hθ
  have hsmall : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0), θ ≤ 1 := by
    have hh : Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hh] with θ hθ
    exact hθ.le
  refine ⟨bound, hBoundInt, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall hMeas
  · filter_upwards [hpos, hsmall] with θ hθ hθ1
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, bound] using
      (avram_ja18g_scalar_exp_quotient_uniform_bound (X.X t ω) θ hθ hθ1)
  · filter_upwards [hpos] with θ hθ
    exact avram_ja18g_original_laplace_quotient_integral_normalisation X t θ hθ
