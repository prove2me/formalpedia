-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.hx_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:11.3779+00:00
-- url     : https://prove2.me/submissions/a7655ca1-bf7a-4cf3-9f2b-23c25144ef90

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_sub_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_sub_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_act
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Hh
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_es_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_es_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_ne_of_val_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
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
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {x : Fin (2 * r + k + 1) → ℂ} (hx' : IsX k r l x) : hx k r l x ∈ UP k r l := by
  obtain ⟨h1, h2, h3⟩ := hx'
  have h1' : ⟪𝐞, x⟫ = 1 := by rw [← h_conj _ Hh, h1, map_one]
  have h4 : ⟪𝐬, x⟫ = conj ⟪x, 𝐬⟫ := (h_conj _ Hh _ _).symm
  have hvp : ⟪x - 𝐬 - ⟪x, 𝐬⟫ • 𝐞, 𝐞⟫ = 0 := by
    simp only [h_sub_left, h_smul_left, h1, h_es_e, h_e_e, if_true]; ring
  refine ⟨hs_glev (h_e_e l l) hvp ?_ ?_ ?_, ?_, fun y hy => ?_⟩
  · simp only [h_sub_left, h_sub_right, h_smul_left, h_smul_right, h1, h1', h2, h4, h_es_e, h_e_e, h_e_es, h_es_es, if_true]
    ring
  · intro a ha
    exact ⟨h_e_e a l, by rw [h_es_e, if_neg (ne_of_val_lt ha)]⟩
  · intro a ha
    simp only [h_sub_right, h_smul_right, (h3 a ha).1, (h3 a ha).2, h_e_e, h_es_es, h_e_es, h_es_e,
      if_neg (ne_of_val_lt ha)]
    constructor <;> ring
  · unfold hx; rw [hs_act, h_e_e]
    have : ⟪𝐞, x - 𝐬 - ⟪x, 𝐬⟫ • 𝐞⟫ = 0 := by rw [← h_conj _ Hh, hvp, map_zero]
    rw [this]; simp
  · unfold hx; rw [hs_act, hy]
    exact ⟨-⟪y, x - 𝐬 - ⟪x, 𝐬⟫ • 𝐞⟫, by simp [sub_eq_add_neg]⟩
end Formalism.FourierDecayAlt.P.Qx4
