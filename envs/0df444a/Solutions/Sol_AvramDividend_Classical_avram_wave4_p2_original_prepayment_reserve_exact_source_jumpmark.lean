-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:29:20.43337+00:00
-- url     : https://prove2.me/submissions/c5f99c2c-0d94-4d55-8c55-c76370ed2655

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

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
    riskProcess X x D t ω -
      Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t =
      X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by
  rw [avram_wave4_p2_original_prepost_reserve_same_leftlim
    X x D hD ω t ht,
    avram_wave3_04_postPaymentReserve_exact_leftLim_identity
      X x D hD ω t ht]
  change (x + X.X t ω - D t ω) -
    (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) =
      X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
  ring