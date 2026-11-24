-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.isT_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:16:53.611285+00:00
-- url     : https://prove2.me/submissions/d2f207dd-b38e-47f3-ac8f-c3b992765d7f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_noConst_iff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_det_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_coeff_Ps
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_eqn_eq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}
open Formalism.L2.FormalSeriesBounds.Sys
variable (S : Sys X)
namespace Formalism.L2.FormalSeriesBounds.Sys
theorem _root_.solution (t : I → MvPowerSeries I C) : S.IsT t ↔ NoConst t ∧ S.Ps t = t := by
  have hdet : IsUnit S.Mt.det := isUnit_iff_ne_zero.mpr S.det_ne
  have key : ∀ μ : I →₀ ℕ, ((∀ x, Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ = dl x μ) ↔
      (fun c => coeff μ (t c)) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹) := by
    intro μ
    constructor
    · intro h
      have h' : Matrix.vecMul (fun c => coeff μ (t c)) S.Mt = fun x => dl x μ - S.Rr t x μ := by
        funext x
        exact eq_sub_of_add_eq (h x)
      rw [← h', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    · intro h x
      rw [h, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
      simp
  rw [Sys.IsT, noConst_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · funext c
    ext μ
    rw [S.coeff_Ps]
    have hk := (key μ).mp (fun x => by rw [← S.eqn_eq t x μ]; exact h x μ)
    exact (congrFun hk c).symm
  · intro x μ
    rw [S.eqn_eq t x μ]
    refine (key μ).mpr ?_ x
    funext c
    rw [← S.coeff_Ps, h]
end Formalism.L2.FormalSeriesBounds.Sys
