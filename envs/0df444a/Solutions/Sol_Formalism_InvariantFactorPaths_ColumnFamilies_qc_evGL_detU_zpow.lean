-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_detU_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:58.198527+00:00
-- url     : https://prove2.me/submissions/a60d5ed6-cd15-4ac4-81e2-2f7c0db06889

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
theorem _root_.solution {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) (m : ℤ) :
    evGL g ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((qc_dU g ^ m : Rˣ) : R) := by
  rw [qc_dU, ← map_zpow]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
