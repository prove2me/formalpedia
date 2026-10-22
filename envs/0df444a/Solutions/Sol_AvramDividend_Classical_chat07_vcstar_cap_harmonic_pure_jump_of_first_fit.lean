-- Prove2me | solution 1 for AvramDividend.Classical.chat07_vcstar_cap_harmonic_pure_jump_of_first_fit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:55:42.779078+00:00
-- url     : https://prove2.me/submissions/74edcae8-925f-4a03-b9ba-253dcfbb420f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_scaledW_endpoint_harmonic_of_continuous_residual
import Theorems.Thm_AvramDividend_Classical_generator_boundary_left_germ_congr_of_sigma_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Pure-jump cap generator matching requires only first-order smooth fit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ)
    (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (a : ℝ) (ha : 0 < a) (hbarrier : a = (cstar W).toReal)
    (hdom : X.GeneratorIntegrable W a)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a))
    (hinside : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0)
    (hder : deriv (vcstar W) a =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W a)) a) :
    X.GeneratorIntegrable (vcstar W) a ∧
      X.generator (vcstar W) a - q * vcstar W a = 0 := by
  subst a
  let u : ℝ → ℝ :=
    fun z => divE (W z) (scaleDeriv W (cstar W).toReal)
  obtain ⟨hdomU, hzeroU⟩ :=
    chat07_scaledW_endpoint_harmonic_of_continuous_residual
      X q W (cstar W).toReal ha hdom hcont hinside
  have hleft : ∀ z : ℝ, z ≤ (cstar W).toReal →
      vcstar W z = u z := by
    intro z hz
    exact vcstar_eq_scaledW_le_cstar_of_support W hsupport z hz
  obtain ⟨hiff, heq⟩ :=
    generator_boundary_left_germ_congr_of_sigma_zero
      X hσ (vcstar W) u (cstar W).toReal hleft hder
  refine ⟨hiff.mpr hdomU, ?_⟩
  have hval : vcstar W (cstar W).toReal = u (cstar W).toReal :=
    hleft (cstar W).toReal le_rfl
  rw [heq, hval]
  exact hzeroU
