-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_algebraMap_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:00:10.50223+00:00
-- url     : https://prove2.me/submissions/7ce4467c-34e5-4b23-b6b0-4d390e74db61

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_det_ne
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
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) :=
  IsLocalization.injective (GLCoord R n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (qa_det_ne R n))
end Formalism.InvariantFactorPaths.ColumnFamilies
