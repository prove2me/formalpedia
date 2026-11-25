-- Prove2me | solution 1 for Formalism.L2.Col.lamJ_on_HKJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:07:17.220082+00:00
-- url     : https://prove2.me/submissions/84b2f768-2355-4060-aa4a-b9f3810cca8b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_HK_le_uniUT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n r t j : ℕ) (M : ↥(HKJ κ n r t j)) :
    lamJ ψ χ n r t j (Subgroup.inclusion (HK_le_uniUT n κ r _) M) = lamKJ χ n r t j M := by
  unfold lamJ lamKJ lamK lamGen
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply]
  have hs : supChar ψ n r (List.replicate j t) (Finset.range (r - 1)) (Subgroup.inclusion (HK_le_uniUT n κ r (List.replicate j t)) M) = 1 := by
    apply Units.ext
    change ψ (supSum r (Finset.range (r - 1)) ((M.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) = 1
    have h0 : supSum r (Finset.range (r - 1)) ((M.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = 0 := by
      obtain ⟨M', hM', hMe⟩ := M.2
      have hker : blkHom n κ (coarse r (List.replicate j t)) 0 M' = 1 := hM'
      unfold supSum
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j' _
      split_ifs with hc
      · obtain ⟨hc1, hc2, -⟩ := hc
        have hi0 : coarse r (List.replicate j t) i.val = 0 := by
          simp only [coarse, blkIdx, if_pos (show i.val < r by omega)]
        have hj0 : coarse r (List.replicate j t) j'.val = 0 := by
          simp only [coarse, blkIdx, if_pos hc2]
        have hk := congrFun (congrFun hker ⟨i, hi0⟩) ⟨j', hj0⟩
        rw [blkHom_apply, Matrix.one_apply_ne (fun e => by
          have := congrArg (fun x => x.1.val) e
          simp only at this
          omega)] at hk
        rw [← hMe]
        exact hk
      · rfl
    rw [h0, AddChar.map_zero_eq_one]
  rw [hs, one_mul]
  rfl
end Formalism.L2.Col
