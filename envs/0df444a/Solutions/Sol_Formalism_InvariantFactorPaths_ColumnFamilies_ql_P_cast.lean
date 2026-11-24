-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_P_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:49.574875+00:00
-- url     : https://prove2.me/submissions/e0aa13cb-8f43-4c95-b171-f8f45202b1d6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_W_cast__311b4d
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_w_cast


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
theorem _root_.solution {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ((ql_P ℤ k L i : ℤ) : R) = ql_P R k L i := by
  simp only [ql_P, Int.cast_sum, Int.cast_mul, Int.cast_prod, ql_w_cast, ql_W_cast]
end Formalism.InvariantFactorPaths.ColumnFamilies
