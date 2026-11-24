-- Prove2me | solution 1 for GenFrameSpan.stepSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:52.965544+00:00
-- url     : https://prove2.me/submissions/575667e3-5682-4b2f-97e1-440a4b3ff67f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
import Theorems.Thm_GenFrameSpan_applyAt0_eq
import Theorems.Thm_GenFrameSpan_Lj_inl_inr
import Theorems.Thm_GenFrameSpan_Gxz_expand
import Theorems.Thm_GenFrameSpan_prodD_mem

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
namespace GenFrameSpan
theorem _root_.solution : StepSpan := by
  intro Lt _ _ l _ N0 N1 nu Th I
  rw [applyAt0_eq, Gxz_expand, map_sum]
  refine Submodule.sum_mem _ fun F _ => ?_
  rw [Lj_inl_inr]
  exact Submodule.smul_mem _ _ (prodD_mem nu F)
end GenFrameSpan
