-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_controlled_jump_drop_covers_dividend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:18:45.683077+00:00
-- url     : https://prove2.me/submissions/5251649c-990e-41db-ad4d-6a881721d3d3

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    0 ≤ rightLimit D t ω - D t ω ∧
      rightLimit D t ω - D t ω ≤
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t -
          (x + X.X t ω - rightLimit D t ω) := by
  constructor
  · exact sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω t)
  · rw [avram_wave3_04_postPaymentReserve_exact_leftLim_identity
      X x D hD ω t ht]
    have hX := avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω t ht
    linarith