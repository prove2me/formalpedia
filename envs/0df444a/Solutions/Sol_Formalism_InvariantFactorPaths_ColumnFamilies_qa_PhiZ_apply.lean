-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_PhiZ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:42:47.503715+00:00
-- url     : https://prove2.me/submissions/6f3705d8-14e2-4fa3-b6d5-64ba7700844b

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
theorem _root_.solution (n : ℕ) (u : GLCoord ℤ n) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    qa_PhiZ n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap f) := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
