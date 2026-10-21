-- Prove2me | solution 1 for AvramDividend.Classical.capped_postPaymentReserve_within_cap_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:26:53.502384+00:00
-- url     : https://prove2.me/submissions/caa46970-56f2-4531-914c-00fc0fbb3353

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X t ω - rightLimit D t ω ∧
      ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C := by
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hn := postPaymentReserve_nonnegative_strictly_before_ruin
    X x D hs ω t ht
  have hup := (postPaymentReserve_rightJump_decomposition
    X x D hs ω t).2.2
  exact ⟨hn, (ENNReal.ofReal_mono hup).trans (hD.2 ω t ht0)⟩
