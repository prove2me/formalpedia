-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_original_drift_prepayment_left_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:10:23.118616+00:00
-- url     : https://prove2.me/submissions/ba28fa82-17ea-4803-a690-f7202eaaa411

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => x + (s : ℝ) * X.drift -
        Function.leftLim (fun r : ℝ≥0 => D r ω) s)
      (Iic t) t := by
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.1.1.2.1 ω
  have hDleft : ContinuousWithinAt
      (Function.leftLim (fun r : ℝ≥0 => D r ω)) (Iic t) t :=
    continuousWithinAt_leftLim_Iic (hmono.tendsto_leftLim t)
  have hlin : ContinuousAt (fun s : ℝ≥0 => x + (s : ℝ) * X.drift) t := by
    fun_prop
  exact hlin.continuousWithinAt.sub hDleft
