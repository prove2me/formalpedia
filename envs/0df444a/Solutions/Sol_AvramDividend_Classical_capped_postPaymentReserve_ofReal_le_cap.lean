-- Prove2me | solution 1 for AvramDividend.Classical.capped_postPaymentReserve_ofReal_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:26:42.157435+00:00
-- url     : https://prove2.me/submissions/54012078-0bc1-4f3d-abc8-4eb9754e0fa2

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
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
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (ω : Ω) (t : ℝ≥0) :
    ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C := by
  by_cases ht : t = 0
  · subst t
    exact (capped_postPaymentReserve_initial_state X x C D hD hxc ω).2
  · have htpos : 0 < t :=
      lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht)
    have hs : IsDividendStrategy 𝓕 D := hD.1.1
    have hle :
        x + X.X t ω - rightLimit D t ω ≤
          riskProcess X x D t ω :=
      (postPaymentReserve_rightJump_decomposition X x D hs ω t).2.2
    exact (ENNReal.ofReal_mono hle).trans (hD.2 ω t htpos)
