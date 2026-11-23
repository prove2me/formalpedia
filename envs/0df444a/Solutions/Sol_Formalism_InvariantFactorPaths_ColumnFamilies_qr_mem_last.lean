-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_mem_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:02.353834+00:00
-- url     : https://prove2.me/submissions/7a9254f0-10d1-4eed-ade4-7ae884615b05

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_last_notMem

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
theorem _root_.solution : Fin.last m ∈ qr_ext e S ↔ e := by
  unfold qr_ext
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; exact qr_last_notMem S
end Formalism.InvariantFactorPaths.ColumnFamilies
