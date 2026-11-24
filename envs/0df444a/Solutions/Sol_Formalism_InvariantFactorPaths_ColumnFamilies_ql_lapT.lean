-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_lapT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:58:50.314805+00:00
-- url     : https://prove2.me/submissions/171bb1ba-efdf-4522-a7cf-452fe9243f75

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sum_w
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_lap
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_transpose


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
variable {R : Type*} [CommRing R]
variable (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A A' * qs_mn g K K' * ql_w R A' K' I = ∑ I', ql_w R A K I' * qs_mn g I' I := by
  have h := ql_lap g.transpose A K I
  simp only [qs_mn_transpose] at h
  rw [h, ← ql_sum_w A K (fun I' => qs_mn g I' I)]
  exact sum_congr rfl fun _ _ => mul_comm _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
