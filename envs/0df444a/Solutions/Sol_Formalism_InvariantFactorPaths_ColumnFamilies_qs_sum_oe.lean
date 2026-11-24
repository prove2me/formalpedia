-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_oe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.417864+00:00
-- url     : https://prove2.me/submissions/3a81699a-2d48-4a84-a38b-fc244012298c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] {h : ℕ} (I : Finset (Fin n)) (hI : I.card = h) (f : Fin n → M) :
    ∑ m ∈ I, f m = ∑ j : Fin h, f (I.orderEmbOfFin hI j) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ I hI]
  rw [Finset.sum_map]; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
