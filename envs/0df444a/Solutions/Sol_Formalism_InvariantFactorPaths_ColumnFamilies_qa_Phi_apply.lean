-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_Phi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:52.253525+00:00
-- url     : https://prove2.me/submissions/c7223b0a-2f12-4940-a29b-060ec5a6e846

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) (f : MvPolynomial (Fin n × Fin n) R) :
    qa_Phi R n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (rename Prod.swap f) := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
