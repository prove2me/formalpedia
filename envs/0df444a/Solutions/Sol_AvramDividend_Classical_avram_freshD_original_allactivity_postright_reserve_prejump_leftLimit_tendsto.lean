-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_allactivity_postright_reserve_prejump_leftLimit_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:56:34.409329+00:00
-- url     : https://prove2.me/submissions/4945e357-bb8e-47be-93df-2d1024817528

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (𝓝[<] t)
      (𝓝 (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)) := by
  have hX : Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)) :=
    (avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω).1 t
  have hD : Tendsto (fun s : ℝ≥0 => rightLimit D s ω)
      (𝓝[<] t) (𝓝 (D t ω)) :=
    avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω t ht
  have hConst : Tendsto (fun _ : ℝ≥0 => x)
      (𝓝[<] t) (𝓝 x) := tendsto_const_nhds
  exact (hConst.add hX).sub hD
