-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.dgR_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:36:33.860207+00:00
-- url     : https://prove2.me/submissions/0c29d125-8b77-43d6-a3f2-ded04c89cdd9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
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
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) : dgR k r t i * dgR k r t (Fin.rev i) = 1 := by
  unfold dgR
  have hr : (Fin.rev i).val = 2 * r + k - i.val := by rw [Fin.val_rev]; omega
  have hi := i.isLt
  rw [hr]
  by_cases h1 : i.val < r
  · rw [if_pos h1, if_neg (show ¬ (2 * r + k - i.val < r) by omega), if_neg (show ¬ (2 * r + k - i.val ≤ r + k) by omega)]
    have : 2 * r + k - i.val - (r + k) = r - i.val := by omega
    rw [this]
    exact mul_inv_cancel₀ (pow_ne_zero _ ht)
  · rw [if_neg h1]
    by_cases h2 : i.val ≤ r + k
    · rw [if_pos h2, if_neg (show ¬ (2 * r + k - i.val < r) by omega), if_pos (show 2 * r + k - i.val ≤ r + k by omega)]
      simp
    · rw [if_neg h2, if_pos (show 2 * r + k - i.val < r by omega)]
      have : r - (2 * r + k - i.val) = i.val - (r + k) := by omega
      rw [this]
      exact inv_mul_cancel₀ (pow_ne_zero _ ht)
end Formalism.FourierDecayAlt.P.B2x7
