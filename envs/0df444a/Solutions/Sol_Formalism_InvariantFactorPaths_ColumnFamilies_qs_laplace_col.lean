-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:11.649926+00:00
-- url     : https://prove2.me/submissions/441c82ed-7478-46d3-bfbf-4d1820bf9f3a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_transpose
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_laplace

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
theorem _root_.solution (A I : Finset (Fin n)) (m : Fin n) :
    ∑ k ∈ A, ((qs_sg (A.erase k) k : ℤ) : R) * qs_mn g (A.erase k) I * g k m =
      if m ∈ I then 0 else ((qs_sg I m : ℤ) : R) * qs_mn g A (insert m I) := by
  have := qs_laplace g.transpose I A m
  simpa only [qs_mn_transpose, Matrix.transpose_apply] using this
end Formalism.InvariantFactorPaths.ColumnFamilies
