-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_dU_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:39.99484+00:00
-- url     : https://prove2.me/submissions/7c9e7e95-9b18-470f-910e-e997e419fc80

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_detU

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
theorem _root_.solution {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : ((qc_dU g : Rˣ) : R) = g.val.det :=
  qc_evGL_detU g
end Formalism.InvariantFactorPaths.ColumnFamilies
