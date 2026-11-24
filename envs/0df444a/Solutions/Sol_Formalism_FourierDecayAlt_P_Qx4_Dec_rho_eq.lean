-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.Dec.rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:01:48.703825+00:00
-- url     : https://prove2.me/submissions/e37ca75c-a337-4840-b8eb-026b3dcaa17f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_mem_level_group
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_iH_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_cF_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_uL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_uL_iH
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
namespace Dec
theorem _root_.solution {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : rho k r l g = g₁ := by
  unfold rho
  rw [h.uL_iH, h.uL_eq, h.cF_eq, iH_eq h.hu.1.1, ← weyl_cell_inv h.hc]
  conv_lhs => rw [h.eq]
  have hw := weyl_cell_mem_level_group (k := k) (r := r) (l := l) h.hc
  calc (w1 k r l c)⁻¹ * u⁻¹ * (u * (w1 k r l c * g₁) * u') * u'⁻¹
      = (w1 k r l c)⁻¹ * ((u⁻¹ * u) * ((w1 k r l c) * (g₁ * (u' * u'⁻¹)))) := by simp only [Matrix.mul_assoc]
    _ = g₁ := by
      rw [uh_inv_mul h.hu.1.1, uh_mul_inv h.hu'.1.1, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        uh_inv_mul hw.1, Matrix.one_mul]
end Dec
end Formalism.FourierDecayAlt.P.Qx4
