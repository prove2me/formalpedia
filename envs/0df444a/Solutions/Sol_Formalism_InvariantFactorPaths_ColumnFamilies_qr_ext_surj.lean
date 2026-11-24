-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_ext_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:28.010172+00:00
-- url     : https://prove2.me/submissions/dc4aa6ea-5e31-4eaf-9485-6f313ba684f1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_mem_castSucc
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_mem_last

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
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (K : Finset (Fin (m + 1))) (h : Fin.last m ∈ K ↔ e) :
    K = qr_ext e (univ.filter fun a : Fin m => a.castSucc ∈ K) := by
  ext x
  induction x using Fin.lastCases with
  | last => rw [qr_mem_last, h]
  | cast a => rw [qr_mem_castSucc]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
