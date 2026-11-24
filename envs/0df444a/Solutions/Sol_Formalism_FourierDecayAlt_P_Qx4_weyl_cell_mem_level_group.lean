-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.weyl_cell_mem_level_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:25.432478+00:00
-- url     : https://prove2.me/submissions/d6c4e91f-2ddd-4445-9f00-322c75f7cef5

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Hh
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_es_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_es_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_ne_of_val_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_mem_UH_of
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
theorem _root_.solution {c : ℂ} (hc : c ≠ 0) : w1 k r l c ∈ Glev k r l.castSucc := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  refine ⟨?_, fun a ha => ?_⟩
  · apply B2x8.mem_UH_of
    intro u w
    have h1 : ⟪𝐞, w⟫ = conj ⟪w, 𝐞⟫ := (h_conj _ Hh _ _).symm
    have h2 : ⟪𝐬, w⟫ = conj ⟪w, 𝐬⟫ := (h_conj _ Hh _ _).symm
    rw [weyl_cell_mulVec, weyl_cell_mulVec]
    simp only [h_add_left, h_add_right, h_smul_left, h_smul_right, h_e_e, h_es_es, h_e_es, h_es_e, if_true, h1, h2,
      map_sub, map_mul, map_inv₀, Complex.conj_conj]
    field_simp
    ring
  · have hne : a ≠ l := ne_of_val_lt (by simpa using ha)
    constructor
    · rw [weyl_cell_mulVec, h_e_e, h_e_es, if_neg hne]; simp
    · rw [weyl_cell_mulVec, h_es_e, h_es_es, if_neg hne]; simp
end Formalism.FourierDecayAlt.P.Qx4
