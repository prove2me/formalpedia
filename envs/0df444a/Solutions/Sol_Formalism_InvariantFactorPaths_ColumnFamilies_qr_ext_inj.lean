-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_ext_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:27.996439+00:00
-- url     : https://prove2.me/submissions/c235de0b-26e8-416c-a8b3-d19f9af1a6df

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_mem_castSucc

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
theorem _root_.solution {S S' : Finset (Fin m)} (h : qr_ext e S = qr_ext e S') : S = S' := by
  ext a
  rw [← qr_mem_castSucc e S a, h, qr_mem_castSucc]
end Formalism.InvariantFactorPaths.ColumnFamilies
