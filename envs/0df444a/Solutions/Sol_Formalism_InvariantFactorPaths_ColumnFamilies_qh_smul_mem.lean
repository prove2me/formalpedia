-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:19.058554+00:00
-- url     : https://prove2.me/submissions/4a9bdd55-6b9e-4622-9535-38296eea90b4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_algR

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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (r : R) {f : GLCoord R n} (hf : f ∈ inducedSections R mu) :
    r • f ∈ inducedSections R mu := by
  intro R' _ _ b g hb
  rw [Algebra.smul_def, map_mul, map_mul, qh_evGLR_algR, qh_evGLR_algR, mul_assoc, hf R' b g hb]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
