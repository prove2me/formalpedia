-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.natAct_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:56.806849+00:00
-- url     : https://prove2.me/submissions/8f0ac749-02b0-4011-8f50-b867dd4918fa

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat
import Theorems.Thm_Formalism_MainNotions_Inhab_gPos_one
import Theorems.Thm_Formalism_MainNotions_Inhab_subst_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.MainNotions.G MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
variable (P : Places p O Kf)
namespace Formalism.MainNotions.Inhab
theorem _root_.solution : P.natAct (fun _ => 1) = LinearMap.id := by
  unfold Places.natAct
  simp only [Units.val_one, inv_one, gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    subst_one]
  rfl
end Formalism.MainNotions.Inhab
