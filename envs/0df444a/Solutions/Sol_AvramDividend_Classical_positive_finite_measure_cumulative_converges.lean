-- Prove2me | solution 1 for AvramDividend.Classical.positive_finite_measure_cumulative_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:27:36.216163+00:00
-- url     : https://prove2.me/submissions/61a158c9-f381-4a4e-a5d6-6b4f90f10d88

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (β : Measure ℝ)
    (hfinite : β Set.univ ≠ ⊤)
    (hpos : 0 < β Set.univ) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun x : ℝ => (β (Iic x)).toReal) atTop (𝓝 L) := by
  refine ⟨(β Set.univ).toReal, ENNReal.toReal_pos hpos.ne' hfinite, ?_⟩
  exact (ENNReal.tendsto_toReal hfinite).comp
    (tendsto_measure_Iic_atTop β)
