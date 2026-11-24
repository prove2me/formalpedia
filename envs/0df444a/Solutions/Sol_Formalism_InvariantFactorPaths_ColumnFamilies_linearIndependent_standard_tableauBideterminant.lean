-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.linearIndependent_standard_tableauBideterminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:28:31.068129+00:00
-- url     : https://prove2.me/submissions/4bd06762-8771-46e2-95d4-45efe8855d58

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_linearIndependent
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_exp_inj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :
    LinearIndependent R (fun I : {I : TIdx mu // StdT I} => qa_P R I.1) := by
  refine ldbasis_linearIndependent (colLex n n) _ ?_ fun I => (tableauBideterminant_degree_leadingCoeff R I.1).2
  intro I J h
  simp only [(tableauBideterminant_degree_leadingCoeff R _).1] at h
  exact Subtype.ext (qa_exp_inj I.1 J.1 I.2 J.2 h)
end Formalism.InvariantFactorPaths.ColumnFamilies
