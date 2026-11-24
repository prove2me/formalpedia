-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.sum_four_comm_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:17.086577+00:00
-- url     : https://prove2.me/submissions/c625dcab-2644-47d2-8215-b1d341bffeea

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (F : α → β → γ → δ → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := sum_congr rfl fun c _ => sum_congr rfl fun d _ => sum_comm
end Formalism.InvariantFactorPaths.ColumnFamilies
