-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_exact_jumpmark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:08:02.760007+00:00
-- url     : https://prove2.me/submissions/5b373b13-624a-4ab9-b8c0-fd9723962402

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (x + X.X t ω - rightLimit D t ω) -
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) -
        (rightLimit D t ω - D t ω) := by
  rw [avram_wave3_04_postPaymentReserve_exact_leftLim_identity
    X x D hD ω t ht]
  ring