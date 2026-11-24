-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_detU_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:20.357875+00:00
-- url     : https://prove2.me/submissions/14943c7c-a53f-45e8-a446-774b992bf8cc

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) : ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = algebraMap _ _ (genMat ℤ n).det := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
