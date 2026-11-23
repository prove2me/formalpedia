-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_mn_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:08.94181+00:00
-- url     : https://prove2.me/submissions/b9ee2ce0-2c30-4282-98e3-e9d4856f14fd

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_ne

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
variable {n : ℕ}
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (J I : Finset (Fin n)) : qs_mn g.transpose J I = qs_mn g I J := by
  by_cases h : J.card = I.card
  · rw [qs_mn_eq _ J I h rfl, qs_mn_eq _ I J rfl h, ← Matrix.det_transpose]; rfl
  · rw [qs_mn_ne _ h, qs_mn_ne _ (Ne.symm h)]
end Formalism.InvariantFactorPaths.ColumnFamilies
