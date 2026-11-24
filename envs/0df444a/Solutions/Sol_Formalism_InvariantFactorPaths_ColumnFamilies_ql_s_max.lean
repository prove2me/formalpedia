-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_s_max
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:51.559548+00:00
-- url     : https://prove2.me/submissions/a228a45a-da59-427c-a090-21da3e2b2aee

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn

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
theorem _root_.solution {K : Finset (Fin n)} {m : Fin n} (h : ∀ x ∈ K, x < m) : wedgeSign R K {m} = 1 := by
  rw [wedgeSign, if_pos (by simpa using fun hm => lt_irrefl _ (h m hm)), ql_sr]
  refine prod_eq_one fun a ha => ?_
  rw [prod_singleton, if_neg (not_lt.2 (h a ha).le)]
end Formalism.InvariantFactorPaths.ColumnFamilies
