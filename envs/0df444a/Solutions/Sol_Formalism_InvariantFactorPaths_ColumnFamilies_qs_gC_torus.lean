-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_gC_torus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:08.284937+00:00
-- url     : https://prove2.me/submissions/3eb3cc19-ff6f-4b6d-89c9-1421bb88d80b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : (qs_gC n).map (evGL (torusPt n)) =
    Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (1 : ℤ)) (1 : ℤ) := by
  ext a b
  simp only [Matrix.map_apply, qs_gC, Matrix.of_apply, qb_evGL_algebraMap, genMat, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
