-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_prepayment_jump_support_source_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:28:31.631654+00:00
-- url     : https://prove2.me/submissions/80009661-5a64-47a8-8ccb-98f5ee01f41d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
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
    (riskProcess X x D t ω ≠
      Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t) ↔
      (X.X t ω ≠ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) := by
  rw [avram_wave4_p2_original_prepost_reserve_same_leftlim
    X x D hD ω t ht,
    avram_wave3_04_postPaymentReserve_exact_leftLim_identity
      X x D hD ω t ht]
  change (x + X.X t ω - D t ω ≠
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ↔
    (X.X t ω ≠ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
  constructor
  · intro hneq heq
    apply hneq
    rw [heq]
  · intro hneq heq
    apply hneq
    linarith