-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_j_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:54.535792+00:00
-- url     : https://prove2.me/submissions/3e27c55d-7c42-49c5-ac06-d8a9872d13a9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_TCols_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_base_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_ext_inj


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
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hi : Interl lam nu) : Function.Injective (qr_j (lam := lam) hi) := by
  intro I' K' h
  funext c
  have h1 := congrArg Subtype.val (congrFun h ⟨c.1, qr_TCols_sub hi c.2⟩)
  have h2 := qr_ext_inj _ h1
  rw [qr_base_mem, qr_base_mem] at h2
  exact Subtype.ext h2
end Formalism.InvariantFactorPaths.ColumnFamilies
