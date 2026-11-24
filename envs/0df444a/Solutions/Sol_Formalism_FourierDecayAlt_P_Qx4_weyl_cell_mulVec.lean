-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.weyl_cell_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:19:13.961018+00:00
-- url     : https://prove2.me/submissions/cbc4c75c-2ad9-488f-bb8d-f4fa1a1ea7d2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_herm_e_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_herm_es_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_eI_ne_esI
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_apply_dual_basis
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_apply_basis
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_apply_other
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
theorem _root_.solution (c : ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    w1 k r l c *ᵥ y = y + (c * ⟪y, 𝐬⟫ - ⟪y, 𝐞⟫) • 𝐬 + ((conj c)⁻¹ * ⟪y, 𝐞⟫ - ⟪y, 𝐬⟫) • 𝐞 := by
  ext p
  rw [herm_e_right, herm_es_right]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, mulVec, dotProduct]
  by_cases h2 : p = esI k r l
  · subst h2
    simp only [weyl_cell_apply_dual_basis, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, (eI_ne_esI l l).symm, if_false]
    ring
  · by_cases h1 : p = eI k r l
    · subst h1
      simp only [weyl_cell_apply_basis, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, eI_ne_esI l l, if_false]
      rw [Complex.star_def]; ring
    · simp only [weyl_cell_apply_other c h1 h2, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h1, h2,
        if_false]
      ring
end Formalism.FourierDecayAlt.P.Qx4
