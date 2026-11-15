-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:44:21.642369+00:00
-- url     : https://prove2.me/submissions/510a959b-b38e-4060-a7d5-99d6114ef21a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (T : ℝ≥0) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      (∀ᵐ ω ∂P, 0 ≤ S ω ∧
        ∀ t : ℝ≥0, t ≤ T →
          (X.X t ω - (t : ℝ) * X.c)^2 ≤ S ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X t ω - (t : ℝ) * X.c
  have hm : Martingale M 𝓕.rightCont P :=
    avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
      X hNuZero
  have hc : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω) := by
    filter_upwards
      [avram_ubv_top11_original_zero_nu_global_continuous_ae X hNuZero]
      with ω hw
    exact hw.sub (NNReal.continuous_coe.mul continuous_const)
  have hL2 : Integrable (fun ω => (M T ω)^2) P :=
    (avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      X hNuZero T).1
  exact avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
    P 𝓕.rightCont M hm hc T hL2
