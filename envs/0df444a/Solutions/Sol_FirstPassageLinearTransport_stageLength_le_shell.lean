-- Prove2me | solution 1 for FirstPassageLinearTransport.stageLength_le_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:27:25.582119+00:00
-- url     : https://prove2.me/submissions/ca50f44e-bc3f-4df2-93a4-014556bdc3cb

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_boundedFirstPassage_le
import Theorems.Thm_FirstPassageLinearTransport_bounded_passage_exists
import Theorems.Thm_FirstPassageLinearTransport_stageLength_eq_bounded

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    stageLength p n ≤ M := by
  rw [stageLength_eq_bounded p hM hnShell]
  exact boundedFirstPassage_le (bounded_passage_exists p hM hnShell hnGood)
end FirstPassageLinearTransport
