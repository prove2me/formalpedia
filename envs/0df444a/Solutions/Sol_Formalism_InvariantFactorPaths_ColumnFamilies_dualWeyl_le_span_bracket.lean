-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.dualWeyl_le_span_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:51.868925+00:00
-- url     : https://prove2.me/submissions/a567038c-7f60-4759-ac82-7c20a4afa190

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_divideN
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_nu_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_brkPol
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_dualWeyl_eq_span_tableauBideterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl ℤ n n (qn_nu mu) ≤ Submodule.span ℤ (Set.range fun I : TIdx mu => transposeVariables ℤ n (brkPol mu I)) := by
  rw [qn_nu_eq hmu]
  simp only [qn_T_brkPol]
  exact qn_divideN n (qa_nu mu) (fun I : TIdx mu => qa_P ℤ I) (le_of_eq (dualWeyl_eq_span_tableauBideterminant ℤ hmu)) _
end Formalism.InvariantFactorPaths.ColumnFamilies
