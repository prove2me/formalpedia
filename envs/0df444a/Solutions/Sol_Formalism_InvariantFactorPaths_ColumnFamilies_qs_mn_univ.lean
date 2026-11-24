-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_mn_univ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.299379+00:00
-- url     : https://prove2.me/submissions/b8a3ff4f-db25-4211-bb24-99b737763bf5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_eq


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
theorem _root_.solution : qs_mn (qs_gC n) univ univ = ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) := by
  have hc : (univ : Finset (Fin n)).card = n := by simp
  rw [qs_mn_eq _ _ _ hc hc]
  have h1 : ∀ a, (univ : Finset (Fin n)).orderEmbOfFin hc a = a := fun a =>
    (congrFun (Finset.orderEmbOfFin_unique hc (f := id) (fun _ => mem_univ _) strictMono_id) a).symm
  simp only [h1]
  show _ = algebraMap _ _ (genMat ℤ n).det
  rw [RingHom.map_det]; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
