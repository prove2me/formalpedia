-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_atomless_original_real_signed_derivative_strictpre_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:56:35.503379+00:00
-- url     : https://prove2.me/submissions/60bc1e27-5b46-40ff-a0bf-6ce31f32c014

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every atomless original dividend time measure sees identical real signed
gradients before and after replacing the true process by its strict source
prejump and dividend right-limit reserve on positive times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ν : Measure ℝ) [NullSingletonClass ν]
    (q : ℝ) (w : ℝ → ℝ) :
    (∫ s in Ioi (0 : ℝ),
      Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) =
    (∫ s in Ioi (0 : ℝ),
      Real.exp (-(q * s)) *
        (1 - deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω)) ∂ν) := by
  have hPre :=
    avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
      X x D hD ω ν
  apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
  filter_upwards [hPre] with s hs hs0
  rw [hs hs0]
