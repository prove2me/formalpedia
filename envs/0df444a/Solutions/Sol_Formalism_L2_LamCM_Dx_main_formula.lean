-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.main_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:09.259005+00:00
-- url     : https://prove2.me/submissions/05bf46de-59dd-40b0-baa1-967e5a4cda05

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_castSucc
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_last
import Theorems.Thm_Formalism_L2_LamCM_Dx_lastL_apply
import Theorems.Thm_Formalism_L2_LamCM_Dx_absNorm_eq_relIndex_mul
import Theorems.Thm_Formalism_L2_LamCM_Dx_sand_comap
import Theorems.Thm_Formalism_L2_LamCM_Dx_imI_ne_zero
import Theorems.Thm_Formalism_L2_LamCM_Dx_fiD_succ
import Theorems.Thm_Formalism_L2_LamCM_Dx_relIndex_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_castSucc
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_last
attribute [local simp] Formalism.L2.LamCM.Dx.lastL_apply

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.Dx
theorem _root_.solution : ∀ (n : ℕ) (M' M : Submodule (𝓞 K) (Fin n → K)), M' ≤ M → Sand M' → Sand M →
    FractionalIdeal.absNorm (fiD M') = (M'.toAddSubgroup.relIndex M.toAddSubgroup : ℚ) * FractionalIdeal.absNorm (fiD M) := by
  intro n
  induction n with
  | zero =>
    intro M' M h _ _
    have e : M' = M := le_antisymm h fun x _ => by rw [Subsingleton.elim x 0]; exact zero_mem _
    subst e
    simp [AddSubgroup.relIndex_self]
  | succ n ih =>
    intro M' M h hM' hM
    rw [fiD_succ M' hM', fiD_succ M hM, map_mul, map_mul, relIndex_succ M' M h,
      ih _ _ (Submodule.comap_mono h) (sand_comap M' hM') (sand_comap M hM),
      absNorm_eq_relIndex_mul (imI M hM) (imI M' hM') (imI_ne_zero M' hM') (Submodule.map_mono h)]
    push_cast
    show _ = _ * _ * (FractionalIdeal.absNorm (fiD (M.comap (snocL K n))) * FractionalIdeal.absNorm (imI M hM))
    simp only [imI, FractionalIdeal.coe_mk]
    ring
end Formalism.L2.LamCM.Dx
