-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_Phi_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:15.946616+00:00
-- url     : https://prove2.me/submissions/7c1837e1-c2d4-4382-9a83-3c52be74ebfe

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_algebraMap_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_Phi_apply

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
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) (u : GLCoord R n) (hu : IsUnit u) :
    Function.Injective (qa_Phi R n u) := by
  intro f g h
  rw [qa_Phi_apply, qa_Phi_apply] at h
  exact rename_injective _ Prod.swap_injective (qa_algebraMap_inj R n (hu.mul_left_cancel h))
end Formalism.InvariantFactorPaths.ColumnFamilies
