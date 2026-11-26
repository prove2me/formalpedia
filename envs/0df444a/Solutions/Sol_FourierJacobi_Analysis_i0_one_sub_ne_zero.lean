-- Prove2me | solution 1 for FourierJacobi.Analysis.i0_one_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:47.445625+00:00
-- url     : https://prove2.me/submissions/0c799d94-0d49-4adb-8e2e-0824eda76d20

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro he
  have hz1 : z = 1 := (sub_eq_zero.mp he).symm
  simp [hz1] at hz
end FourierJacobi.Analysis
