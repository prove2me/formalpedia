-- Prove2me | solution 1 for GenFrameSpan.nablaX_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:20.825944+00:00
-- url     : https://prove2.me/submissions/0aad3c89-88e8-4492-a0e7-2964c1e1da80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply

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
open Classical
open GenFrameSpan
open CutKW MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]
namespace GenFrameSpan
theorem _root_.solution (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, ∏ c, Dm s _ (J s c) := by
  unfold nablaX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  unfold Dm Xm
  rfl
end GenFrameSpan
