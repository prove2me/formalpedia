-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.levAll_funMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:23.140712+00:00
-- url     : https://prove2.me/submissions/ec76d932-4783-4c78-9740-e9993664db6e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat
import Theorems.Thm_Formalism_MainNotions_Inhab_smul_sgnEl
import Theorems.Thm_Formalism_MainNotions_Inhab_actX_sgnEl
import Theorems.Thm_Formalism_MainNotions_Inhab_chi_sgnEl
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
theorem _root_.solution (h2 : (2 : Kf) ≠ 0) (Hv : P.Tup → Submodule O P.Xsp) : (levAll P).funMod Hv = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  have h := hF.2
  rw [SetLike.mem_coe, Submodule.mem_iInf] at h
  have h' := h (sgnEl P)
  rw [Submodule.mem_iInf] at h'
  rw [Submodule.mem_bot]
  funext L
  have h3 := h' L
  rw [LinearMap.mem_ker] at h3
  simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, smul_sgnEl, actX_sgnEl, chi_sgnEl,
    neg_smul, one_smul] at h3
  have h5 : F L - -(F L) = 0 := h3
  have h4 : (2 : Kf) • F L = 0 := by rw [two_smul, ← sub_neg_eq_add]; exact h5
  exact (smul_eq_zero.mp h4).resolve_left h2
end Formalism.MainNotions.Inhab
