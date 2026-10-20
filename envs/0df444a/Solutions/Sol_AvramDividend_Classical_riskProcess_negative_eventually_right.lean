-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_negative_eventually_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:13:58.567983+00:00
-- url     : https://prove2.me/submissions/643c3993-3158-4f3d-a4c8-5897e2eecd50

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : ℝ≥0)
    (hneg : riskProcess X x D s ω < 0) :
    ∀ᶠ t in 𝓝[Ici s] s, riskProcess X x D t ω < 0 := by
  have hlt : X.X s ω < D s ω - x := by
    dsimp [riskProcess] at hneg
    linarith
  have hcont : ∀ᶠ t in 𝓝[Ici s] s, X.X t ω < D s ω - x :=
    (X.rightCont ω s).eventually (isOpen_Iio.mem_nhds hlt)
  filter_upwards [hcont, self_mem_nhdsWithin] with t hXt hst
  have hm : D s ω ≤ D t ω := (hD.2.1 ω) hst
  dsimp [riskProcess]
  linarith
