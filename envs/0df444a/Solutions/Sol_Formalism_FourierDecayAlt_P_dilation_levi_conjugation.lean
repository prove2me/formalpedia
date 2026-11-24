-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_levi_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:53:01.87767+00:00
-- url     : https://prove2.me/submissions/bfd9917d-1c73-48d7-837a-2b0b4c3395be

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_aDil_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dgR_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dgR_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2_aDil_inv
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
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open B2x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.DilLev := by
  intro k r' t ht g
  rw [B2.aDil_inv _ _ _ ht, B2.aDil_inv _ _ _ ht]
  simp only [aDil_eq]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold ιLev
  by_cases hi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hi, dif_pos hi]
    by_cases hj : 1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1
    · rw [dif_pos hj, dif_pos hj, Matrix.mul_diagonal, Matrix.diagonal_mul, dgR_shift t i hi, dgR_shift t⁻¹ j hj]
    · rw [dif_neg hj, dif_neg hj]; simp
  · rw [dif_neg hi, dif_neg hi]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, mul_one, ← Complex.ofReal_mul, dgR_mul_inv _ _ _ ht, Complex.ofReal_one]
    · rw [if_neg h]; simp
end Formalism.FourierDecayAlt.P
