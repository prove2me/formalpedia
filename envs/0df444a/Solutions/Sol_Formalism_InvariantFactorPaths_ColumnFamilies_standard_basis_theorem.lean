-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.standard_basis_theorem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:08:24.045568+00:00
-- url     : https://prove2.me/submissions/926ee39f-0dc9-4fa0-9b86-4db09fe43a15

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SBasis
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_brk_Phi
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_SMu_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_dualWeyl_eq_span_standard_tableauBideterminant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_linearIndependent_standard_tableauBideterminant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_PhiZ_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : SBasis := by
  intro n _ mu hmu
  have he : (fun I : {I : TIdx mu // StdT I} => brk mu I.1) =
      (qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) ∘
        fun I : {I : TIdx mu // StdT I} => qa_P ℤ I.1 := by
    funext I
    exact qa_brk_Phi mu I.1
  constructor
  · rw [he]
    exact (linearIndependent_standard_tableauBideterminant ℤ mu).map' (qa_PhiZ n _)
      (LinearMap.ker_eq_bot.mpr (qa_PhiZ_inj n _ (Units.isUnit _)))
  · rw [qa_SMu_eq hmu, dualWeyl_eq_span_standard_tableauBideterminant ℤ hmu, Submodule.map_span, ← Set.range_comp, he]
end Formalism.InvariantFactorPaths.ColumnFamilies
