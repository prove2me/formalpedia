-- Prove2me | solution 1 for Formalism.IncomingBounds.unitFactorialProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:55:26.955633+00:00
-- url     : https://prove2.me/submissions/ccd70d12-f020-436b-897e-ed14c9b7e805

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Theorems.Thm_Formalism_IncomingBounds_num_uFac_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : UProduct := by
  intro l hl x
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction x with
  | zero => simp [uFac]
  | succ x ih =>
    rw [num_uFac_succ, ih, Finset.prod_range_succ, pow_succ]
    ring
end Formalism.IncomingBounds
