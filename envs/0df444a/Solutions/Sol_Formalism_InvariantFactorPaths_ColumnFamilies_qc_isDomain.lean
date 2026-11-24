-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.347904+00:00
-- url     : https://prove2.me/submissions/e25bc9c0-760d-4f28-9744-d67127fa624f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_genMat_det_ne

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
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (n : ℕ) : IsDomain (GLCoord R n) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial (Fin n × Fin n) R) (S := GLCoord R n)
    (M := Submonoid.powers (genMat R n).det)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (qc_genMat_det_ne R n))
end Formalism.InvariantFactorPaths.ColumnFamilies
