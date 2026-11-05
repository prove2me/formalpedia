-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:02:17.177114+00:00
-- url     : https://prove2.me/submissions/04f67fd1-8634-430b-9cec-0c56a4e51271

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The unchanged original Lévy reserve after right dividend payment has pathwise right continuity even at zero and the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (Ici t) t := by
  have hX : ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω) (Ici t) t := by
    simpa [X.X_zero ω] using
      (avram_wave7_01_original_shifted_future_increment_path_cadlag X ω 0).1 t
  have hDright : ContinuousWithinAt
      (fun s : ℝ≥0 => rightLimit D s ω) (Ici t) t :=
    dividendStrategy_rightLimit_rightContinuous D hD ω t
  exact (continuousWithinAt_const.add hX).sub hDright
