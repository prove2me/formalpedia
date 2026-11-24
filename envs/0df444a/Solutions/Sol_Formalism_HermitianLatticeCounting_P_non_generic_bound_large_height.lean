-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.non_generic_bound_large_height
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:43.831995+00:00
-- url     : https://prove2.me/submissions/dd7b3400-9423-4f84-96c1-112b0c26d7af

import Definitions.Def_Formalism_FlagUnipotentLattices_ConductorCharacterLeakBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_GaussSumCharacterAverageBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_maximal_sum_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_type_cauchy_schwarz
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_maximal_sum_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_type_cauchy_schwarz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S4 Formalism.HermitianLatticeCounting.P.S4aux Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.NonGenericBoundLargeHeight := by
  intro k r H nn D Ty _ _ w amp μ be hH hnn hw hTy hbe hμ hμM hsum hamp
  have hH1 : (1 : ℝ) ≤ H := by linarith
  set n : ℕ := k - 1 with hn
  set A0 : ℝ := H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := H ^ (4 * (r + 1)) with hA1
  have hA0p : 0 < A0 := by positivity
  have hA1p : 0 < A1 := by positivity
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ 8 * A0 * A1 * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    have hms := S4aux.maximal_sum_bound D w (μ t) (amp t) 1 (2 * A0 * be t ^ n) hw (hμ t) zero_le_one
      (fun d => by rw [one_mul]; exact hamp t d) (hμM t)
    have h1 : be t ^ n * (be t ^ n)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    calc _ ≤ _ := hms
      _ ≤ 1 ^ 2 * (2 * A0 * be t ^ n) * (4 * A1 * (be t ^ n)⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (be t ^ n * (be t ^ n)⁻¹) * (8 * A0 * A1 * nn) := by ring
      _ = _ := by rw [h1, one_mul]
  have h8 : (8 : ℝ) ≤ H ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ H ^ 3 := by gcongr
  have hexp : 1 + 1 + 3 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1) ≤ 39 * (r + 1) ^ 2 := by
    nlinarith
  calc _ ≤ _ := S4aux.type_cauchy_schwarz D Ty w amp hw
    _ ≤ H * ∑ t : Ty, 8 * A0 * A1 * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H * (8 * A0 * A1 * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H * (H * (H ^ 3 * A0 * A1 * nn)) := by
        gcongr
    _ = H ^ (1 + 1 + 3 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1)) * nn := by
        rw [pow_add, pow_add, pow_add, pow_add, pow_one]; ring
    _ ≤ _ := by
        gcongr
end Formalism.HermitianLatticeCounting.P
