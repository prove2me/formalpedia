-- Prove2me | solution 1 for Formalism.REAL.casArr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:16:01.706286+00:00
-- url     : https://prove2.me/submissions/1d5ef08b-27bc-4965-a499-0aff353b9c07

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_indexArray_ext
import Theorems.Thm_Formalism_REAL_inner_totalPositionAction
import Theorems.Thm_Formalism_REAL_compactCasimir_apply
import Theorems.Thm_Formalism_REAL_compactCasimir_add
import Theorems.Thm_Formalism_REAL_totalPositionAction_mul_pointwiseAction
import Theorems.Thm_Formalism_REAL_sum_positionMixedCasimir
import Theorems.Thm_Formalism_REAL_admissibleArrays_apply_mem
import Theorems.Thm_Formalism_REAL_compactCasimir_pointwiseAction_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (hk : KCasSpan) : CasArr := by
  intro V _ _ n ε E Λ u j
  refine ⟨fun hgl hkh F hF => ?_, fun F => ?_⟩
  · have hcomm : ∀ a b c d, positionsE V n j a b * ptE E c d = ptE E c d * positionsE V n j a b :=
      fun a b c d => totalPositionAction_mul_pointwiseAction E a b c d
    have hsplit : arrE E j = fun a b => positionsE V n j a b + ptE E a b := rfl
    rw [hsplit, compactCasimir_add ε _ _ hcomm, ← sum_positionMixedCasimir]
    rw [LinearMap.add_apply, LinearMap.add_apply, two_mul, LinearMap.add_apply, LinearMap.sum_apply,
      two_smul]
    congr 1
    congr 1
    refine indexArray_ext fun α => ?_
    rw [compactCasimir_pointwiseAction_apply, PiLp.smul_apply]
    exact hk V n ε E Λ u (fun a b c d _ _ => hgl a b c d) hkh (F α) (admissibleArrays_apply_mem hF α)
  · rw [compactCasimir_apply, inner_sum, Complex.re_sum]
    refine Finset.sum_nonneg fun a _ => ?_
    rw [inner_sum, Complex.re_sum]
    refine Finset.sum_nonneg fun b _ => ?_
    split_ifs
    · rw [← inner_totalPositionAction]
      have hre : (⟪positionsE V n j b a F, positionsE V n j b a F⟫_ℂ).re = ‖positionsE V n j b a F‖ ^ 2 := by
        first
          | exact inner_self_eq_norm_sq _
          | exact inner_self_eq_norm_sq (𝕜 := ℂ) _
          | simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (positionsE V n j b a F)
      rw [hre]
      positivity
    · simp
end Formalism.REAL
