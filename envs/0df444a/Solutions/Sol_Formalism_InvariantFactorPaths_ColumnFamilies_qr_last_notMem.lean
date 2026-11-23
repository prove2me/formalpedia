-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_last_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:07.15135+00:00
-- url     : https://prove2.me/submissions/78281c6e-14a1-44ce-8f32-1228133cff5b

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
theorem _root_.solution : Fin.last m ∉ S.map Fin.castSuccEmb := by
  simp only [Finset.mem_map, not_exists, not_and]
  intro a _ h
  exact (Fin.castSucc_lt_last a).ne h
end Formalism.InvariantFactorPaths.ColumnFamilies
