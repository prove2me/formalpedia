-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.relIndex_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:09.00714+00:00
-- url     : https://prove2.me/submissions/3221a0d4-e1d1-4a2d-80db-1a479b150c1c

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_castSucc
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_last
import Theorems.Thm_Formalism_L2_LamCM_Dx_lastL_apply
import Theorems.Thm_Formalism_L2_LamCM_Dx_idx
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
theorem _root_.solution {n : ℕ} (M' M : Submodule (𝓞 K) (Fin (n+1) → K)) (h : M' ≤ M) :
    M'.toAddSubgroup.relIndex M.toAddSubgroup =
      (M'.comap (snocL K n)).toAddSubgroup.relIndex (M.comap (snocL K n)).toAddSubgroup *
        (M'.map (lastL K n)).toAddSubgroup.relIndex (M.map (lastL K n)).toAddSubgroup := by
  rw [idx M'.toAddSubgroup M.toAddSubgroup h (lastL K n).toAddMonoidHom, Submodule.map_toAddSubgroup,
    Submodule.map_toAddSubgroup]
  congr 1
  have hinj : Function.Injective (snocL K n).toAddMonoidHom := by
    intro u v huv
    ext j
    have := congrFun huv (Fin.castSucc j)
    simpa using this
  have hm : ∀ N : Submodule (𝓞 K) (Fin (n+1) → K),
      (N.comap (snocL K n)).toAddSubgroup.map (snocL K n).toAddMonoidHom = N.toAddSubgroup ⊓ (lastL K n).toAddMonoidHom.ker := by
    intro N
    ext x
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup,
      Submodule.mem_comap, LinearMap.toAddMonoidHom_coe, lastL_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨hw, by simp⟩
    · rintro ⟨hx, h0⟩
      refine ⟨Fin.init x, ?_, ?_⟩ <;>
      · have e : snocL K n (Fin.init x) = x := by
          ext k; refine Fin.lastCases ?_ (fun j => ?_) k
          · simp [h0]
          · simp [Fin.init]
        rw [e]; try exact hx
  rw [← hm, ← hm, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
end Formalism.L2.LamCM.Dx
