-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.log_subst_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:37.687745+00:00
-- url     : https://prove2.me/submissions/2962b516-22a9-4453-9566-213605578951

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_geomAlt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable {K : Type*} [Field K] [CharZero K]
namespace Formalism.ELL.PadicLogarithmSubstitution
theorem _root_.solution (c : K) (B : PowerSeries K) (hB0 : constantCoeff B = 1)
    (hBd : (1 + X) * derivative K B = c • B) :
    (log K).subst (B - 1) = c • log K := by
  have h0 : constantCoeff (B - 1) = 0 := by simp [hB0]
  have hS : HasSubst (B - 1) := HasSubst.of_constantCoeff_zero' h0
  have hone : (1 + X : PowerSeries K).subst (B - 1) = B := by
    rw [subst_add hS, subst_X hS, ← coe_substAlgHom hS, map_one]; ring
  have hGB : (geometricSignedSeries K).subst (B - 1) * B = 1 := by
    have hm := subst_mul hS (geometricSignedSeries K) (1 + X)
    rw [geomAlt_mul, hone, ← coe_substAlgHom hS, map_one] at hm
    rw [← coe_substAlgHom hS, ← hm]
  have hD : derivative K ((log K).subst (B - 1)) = derivative K (c • log K) := by
    have hX : (1 + X : PowerSeries K) ≠ 0 := by
      intro h
      have := congrArg constantCoeff h
      simp at this
    refine mul_right_cancel₀ hX ?_
    rw [derivative_subst hS, deriv_log, Derivation.map_smul, deriv_log]
    change (geometricSignedSeries K).subst (B - 1) * derivative K (B - 1) * (1 + X) =
      c • geometricSignedSeries K * (1 + X)
    rw [map_sub, derivative_one, sub_zero, mul_assoc, mul_comm (derivative K B), hBd,
      mul_smul_comm, hGB, smul_mul_assoc, geomAlt_mul]
  refine derivative.ext hD ?_
  rw [show constantCoeff (c • log K) = 0 by simp]
  exact constantCoeff_subst_eq_zero h0 _ constantCoeff_log
end Formalism.ELL.PadicLogarithmSubstitution
