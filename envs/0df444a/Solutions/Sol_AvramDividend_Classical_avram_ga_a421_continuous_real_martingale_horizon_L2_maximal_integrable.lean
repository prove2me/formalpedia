-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:53:53.236253+00:00
-- url     : https://prove2.me/submissions/2915821e-294a-41df-ac34-b3688702987a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
import Theorems.Thm_AvramDividend_Classical_avram_ga_a425_continuous_dyadic_uniform_L2_maximal_to_path_integrability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale M 𝓕 P)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω))
    (T : ℝ≥0)
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      (∀ᵐ ω ∂P, 0 ≤ S ω ∧
        ∀ t : ℝ≥0, t ≤ T → (M t ω)^2 ≤ S ω) := by
  have hDyad :=
    avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
      P 𝓕 M hMart hCont T hL2
  exact avram_ga_a425_continuous_dyadic_uniform_L2_maximal_to_path_integrability
    P 𝓕 M hCont T hL2 hDyad
