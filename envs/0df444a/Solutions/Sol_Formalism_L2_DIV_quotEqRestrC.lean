-- Prove2me | solution 1 for Formalism.L2.DIV.quotEqRestrC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:56:15.070176+00:00
-- url     : https://prove2.me/submissions/ccc3091f-8513-4990-893d-09692197bc38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : QuotEqRestrC := by
  intro n d A hA C P h1 h2
  have hGP : Cᴴ * A * C * P = Cᴴ * A := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    rw [Matrix.mul_assoc (Cᴴ * A), ← h2]
  have hPG : Pᴴ * (Cᴴ * A * C) = A * C := by
    have := congrArg Matrix.conjTranspose hGP
    simpa [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc] using this
  rw [quotMetC, restrMetC]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_assoc, hPG, Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), Matrix.one_mul, h1]
end Formalism.L2.DIV
