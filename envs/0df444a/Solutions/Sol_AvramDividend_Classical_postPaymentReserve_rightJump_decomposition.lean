-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_rightJump_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:23:35.656587+00:00
-- url     : https://prove2.me/submissions/957c96fa-bc88-40bc-94be-d987ea26d78d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ rightLimit D t ω - D t ω ∧
    riskProcess X x D t ω =
      (x + X.X t ω - rightLimit D t ω) +
        (rightLimit D t ω - D t ω) ∧
    x + X.X t ω - rightLimit D t ω ≤
      riskProcess X x D t ω := by
  have hle := dividendStrategy_le_rightLimit D hD ω t
  constructor
  · linarith
  constructor
  · dsimp [riskProcess]
    ring
  · dsimp [riskProcess]
    linarith
