-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_brk_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:14.578927+00:00
-- url     : https://prove2.me/submissions/8683b480-8cd5-41d4-a72d-86ed72c95be7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SBasis
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_PhiZ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_brk_eq


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
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brk mu I = qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) (qa_P ℤ I) := by
  rw [qa_brk_eq, qa_PhiZ_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
