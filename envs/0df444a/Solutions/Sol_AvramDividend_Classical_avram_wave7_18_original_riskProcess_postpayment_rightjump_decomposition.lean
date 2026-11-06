-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:27:04.495251+00:00
-- url     : https://prove2.me/submissions/9b8ed430-c8ff-49cf-b996-79382cd5d3ac

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    riskProcess X x D t ω -
      (rightLimit D t ω - D t ω) =
      x + X.X t ω - rightLimit D t ω ∧
    riskProcess X x D t ω =
      (x + X.X t ω - rightLimit D t ω) +
      (rightLimit D t ω - D t ω) := by
  constructor <;> simp only [riskProcess] <;> ring
