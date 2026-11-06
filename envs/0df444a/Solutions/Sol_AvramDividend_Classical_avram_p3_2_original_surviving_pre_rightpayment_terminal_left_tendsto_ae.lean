-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_surviving_pre_rightpayment_terminal_left_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:44:16.982331+00:00
-- url     : https://prove2.me/submissions/ac613160-b235-4ea2-bb6a-c3b73ad555a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At a fixed positive time, the original post-rightpayment reserve before
that time converges almost surely to the actual pre-rightpayment reserve at
the horizon. The atom at the horizon is not subtracted. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      Tendsto (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 (riskProcess X x D t ω)) := by
  filter_upwards [avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
    X t ht] with ω hNo
  have hXeq :
      X.X t ω = Function.leftLim (fun s : ℝ≥0 => X.X s ω) t :=
    sub_eq_zero.mp hNo
  have hXlim :
      Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t) (𝓝 (X.X t ω)) := by
    simpa only [hXeq] using
      (tendsto_leftLim_of_tendsto (X.leftLim ω t ht))
  have hDlim :
      Tendsto (fun s : ℝ≥0 => rightLimit D s ω)
        (𝓝[<] t) (𝓝 (D t ω)) :=
    avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω t ht
  have hRlim :
      Tendsto (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 (x + X.X t ω - D t ω)) := by
    exact (tendsto_const_nhds.add hXlim).sub hDlim
  simpa only [riskProcess] using hRlim
