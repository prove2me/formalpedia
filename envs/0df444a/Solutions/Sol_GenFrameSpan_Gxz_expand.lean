-- Prove2me | solution 1 for GenFrameSpan.Gxz_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:55.006366+00:00
-- url     : https://prove2.me/submissions/b19dc30d-c404-43f1-8fe1-97b190f41056

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
import Theorems.Thm_GenFrameSpan_minorXZ_expand

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
theorem _root_.solution (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) :
    Gxz N0 N1 nu I = ∑ F : (∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0),
      rename (Sum.inl : _ → XZ Lt N0 N1) (∏ s, ∏ c, Dm s _ (F s c)) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (∏ s, ∏ c, Zm s _ (I s c) (F s c)) := by
  unfold Gxz
  simp_rw [minorXZ_expand, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  simp only [map_prod, Finset.prod_mul_distrib]
end GenFrameSpan
