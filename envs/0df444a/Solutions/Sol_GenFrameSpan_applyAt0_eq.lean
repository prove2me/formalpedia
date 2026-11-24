-- Prove2me | solution 1 for GenFrameSpan.applyAt0_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:15.084593+00:00
-- url     : https://prove2.me/submissions/d165abf7-833b-46c4-b960-a06278d85f54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
import Theorems.Thm_GenFrameSpan_Lj_monomial

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
theorem _root_.solution (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : applyAt0 N0 N1 l Th P = Lj Th P := by
  conv_rhs => rw [P.as_sum]
  rw [map_sum]
  unfold applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Lj_monomial, atMon, smul_monomial, zsmul_eq_mul, mul_assoc]
end GenFrameSpan
