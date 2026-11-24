-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.ell_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:07.177881+00:00
-- url     : https://prove2.me/submissions/8d8ce24f-82ba-4491-8c5b-ef32fbfd6fc5

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_lv_eI
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
variable {r' : ℕ}
open Formalism.FourierDecayAlt.B2 (a0)
open B2x6 (lv blk)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (z : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    ell k (1 + r') (liftVec k 1 r' z) (ιLev k 1 r' g) = ell k r' z g := by
  unfold ell
  symm
  apply Fintype.sum_of_injective (fun a : Fin r' => (⟨a.val + 1, by omega⟩ : Fin (1 + r')))
  · intro a b h
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  · intro a ha
    have ha0 : a.val = 0 := by
      by_contra h0
      apply ha
      have := a.isLt
      exact ⟨⟨a.val - 1, by omega⟩, Fin.ext (by simp only; omega)⟩
    have e : eI k (1 + r') a = B2x6.iF k r' := Fin.ext (by rw [B2x6.iF_val]; exact ha0)
    split_ifs with h
    · rw [e, B2x6.lev_F, if_neg]
      intro h2
      have := congrArg Fin.val h2
      rw [B2x6.iF_val] at this
      simp only [eI] at this
      omega
    · rw [e, B2x6.lev_mulVec_F, B2x6.lift_F]
  · intro a
    by_cases h : a.val + 1 < r'
    · rw [dif_pos h, dif_pos (by simp only; omega)]
      have e2 : eI k (1 + r') ⟨a.val + 1 + 1, by omega⟩ = lv k r' (eI k r' ⟨a.val + 1, h⟩) := (lv_eI (k := k) (⟨a.val + 1, h⟩ : Fin r')).symm
      rw [← lv_eI a]
      exact (B2x6.lev_mm g _ _).symm.trans (by rw [e2])
    · rw [dif_neg h, dif_neg (by simp only; omega), ← lv_eI a, B2x5.lev_lift]
      exact (congrFun (B2x6.lift_res (g *ᵥ z)) (eI k r' a)).symm
end Formalism.FourierDecayAlt.P.Qx4
