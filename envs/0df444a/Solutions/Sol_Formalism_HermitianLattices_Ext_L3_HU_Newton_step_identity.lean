-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Newton.step_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:45.643862+00:00
-- url     : https://prove2.me/submissions/6e7db53d-5093-4d87-929f-35cfc040a811

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StepIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
open Formalism.HermitianLattices.Ext.L3.HU.Newton
namespace Formalism.HermitianLattices.Ext.L3.HU.Newton
theorem _root_.solution (P H X Y Y' Z V V' : Matrix n n K) (a b : K)
    (hG : P * H * X = H + (a * b) • Z) (hHY : H * Y = b • V') (hYH : Y' * H = b • V)
    (hV : V + V' = Z) :
    (P - a • (Y' * P)) * H * (X - a • (X * Y)) =
      H + (a * a * b) • (-(Z * Y) - Y' * Z + Y' * V' + a • (Y' * Z * Y)) := by
  have e1 : P - a • (Y' * P) = (1 - a • Y') * P := by rw [sub_mul, one_mul, smul_mul_assoc]
  have e2 : X - a • (X * Y) = X * (1 - a • Y) := by rw [mul_sub, mul_one, mul_smul_comm]
  have e3 : (1 - a • Y') * P * H * (X * (1 - a • Y)) = (1 - a • Y') * (P * H * X) * (1 - a • Y) := by
    simp only [Matrix.mul_assoc]
  have hYHY : Y' * H * Y = b • (Y' * V') := by
    rw [Matrix.mul_assoc, hHY, mul_smul_comm]
  have hV2 : V = Z - V' := eq_sub_of_add_eq hV
  rw [e1, e2, e3, hG]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  simp only [← Matrix.mul_assoc, hYHY]
  simp only [← Matrix.mul_assoc, hHY, hYH, hV2]
  simp only [Matrix.mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  module
end Formalism.HermitianLattices.Ext.L3.HU.Newton
