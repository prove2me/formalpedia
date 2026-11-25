-- Prove2me | solution 1 for Formalism.IncomingBounds.thmPExp_wt_le_add_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:16.679362+00:00
-- url     : https://prove2.me/submissions/645d562f-f76f-476e-8500-00bf5301db89

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp

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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (y : WithTop ℝ) (c w : ℝ) :
    ((c : ℝ) : WithTop ℝ) ≤ y + ((w : ℝ) : WithTop ℝ) ↔ ((c - w : ℝ) : WithTop ℝ) ≤ y := by
  induction y with
  | top => simp
  | coe t =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith
end Formalism.IncomingBounds
