-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_mem_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:26.315305+00:00
-- url     : https://prove2.me/submissions/59ae0e7b-45d9-47df-9b77-f8f404d29974

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite

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
theorem _root_.solution (a : Fin m) : a.castSucc ∈ qr_ext e S ↔ a ∈ S := by
  unfold qr_ext
  split_ifs <;> simp [(Fin.castSucc_lt_last a).ne]
end Formalism.InvariantFactorPaths.ColumnFamilies
