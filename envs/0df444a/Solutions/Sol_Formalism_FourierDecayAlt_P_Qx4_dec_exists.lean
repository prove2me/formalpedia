-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.dec_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:32:57.945492+00:00
-- url     : https://prove2.me/submissions/20c90da7-d32a-423d-be8d-d5242e91d66d

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_es_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_ne_of_val_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hx_es
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_stab_dec__b3b71b5cc842
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_w1_mulVec_bvec_eI
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_mem_level_group
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
theorem _root_.solution {g : Mx k r} (hg : g ∈ Glev k r l.castSucc) (hc : ⟪g *ᵥ 𝐞, 𝐞⟫ ≠ 0) :
    ∃ u g₁ u', Dec k r l g ⟪g *ᵥ 𝐞, 𝐞⟫ u g₁ u' := by
  set c := ⟪g *ᵥ 𝐞, 𝐞⟫ with hcdef
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  have hX : IsX k r l (c⁻¹ • (g *ᵥ 𝐞)) := by
    refine ⟨?_, ?_, fun a ha => ⟨?_, ?_⟩⟩
    · rw [h_smul_left, ← hcdef, inv_mul_cancel₀ hc]
    · rw [h_smul_left, h_smul_right, uh_herm hg.1, h_e_e]; simp
    · rw [h_smul_right]
      conv_lhs => rw [← (hg.2 a (by simpa using ha)).1]
      rw [uh_herm hg.1, h_e_e, mul_zero]
    · rw [h_smul_right]
      conv_lhs => rw [← (hg.2 a (by simpa using ha)).2]
      rw [uh_herm hg.1, h_es_e, if_neg (ne_of_val_lt ha), mul_zero]
  have hu := hx_up hX
  set u := hx k r l (c⁻¹ • (g *ᵥ 𝐞)) with hudef
  have hues : u *ᵥ 𝐬 = c⁻¹ • (g *ᵥ 𝐞) := hx_es hX
  have hw := weyl_cell_mem_level_group (k := k) (r := r) (l := l) hc
  have hg' : (w1 k r l c)⁻¹ * (u⁻¹ * g) ∈ Glev k r l.castSucc := glev_mul (glev_inv hw) (glev_mul (glev_inv hu.1) hg)
  have he' : ((w1 k r l c)⁻¹ * (u⁻¹ * g)) *ᵥ 𝐞 = 𝐞 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    apply uh_inv_fix hw.1
    symm
    apply uh_inv_fix hu.1.1
    rw [w1_mulVec_bvec_eI, Matrix.mulVec_smul, hues, smul_smul, mul_inv_cancel₀ hc, one_smul]
  obtain ⟨u', hu', g₁, hg₁, h⟩ := stab_dec' hg' he'
  refine ⟨u, g₁, u', hc, hu, hg₁, hu', ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← h, ← Matrix.mul_assoc (w1 k r l c), uh_mul_inv hw.1, Matrix.one_mul,
    ← Matrix.mul_assoc, uh_mul_inv hu.1.1, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Qx4
