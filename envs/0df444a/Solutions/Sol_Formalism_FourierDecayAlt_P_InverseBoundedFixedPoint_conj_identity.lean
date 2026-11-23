-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.conj_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:40.861891+00:00
-- url     : https://prove2.me/submissions/7f0696bb-426b-4a56-aa02-81370e88072e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_HH_HA
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_HA_HH
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_HA_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution (p : K) (Y N : Matrix (Fin m) (Fin m) K) (hs : Yᵀ = Y)
    (e : Y = N - p • (Y * HA K m * Y)) :
    (1 + (2 * p) • (HA K m * Y))ᵀ * HH K m * (1 + (2 * p) • (HA K m * Y)) =
      HH K m + (4 * ((m + 1 : ℕ) : K) * p) • N := by
  have eN : N = Y + p • (Y * HA K m * Y) := by rw [eq_sub_iff_add_eq] at e; exact e.symm
  have e1 : HH K m * (HA K m * Y) = ((m + 1 : ℕ) : K) • Y := by
    rw [← Matrix.mul_assoc, HH_HA, Matrix.smul_mul, one_mul]
  have e2 : Y * HA K m * HH K m = ((m + 1 : ℕ) : K) • Y := by
    rw [Matrix.mul_assoc, HA_HH, Matrix.mul_smul, mul_one]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_mul, hs,
    HA_symm]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, e1, e2]
  conv_rhs => rw [eN]
  simp only [Matrix.mul_assoc]
  module
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
