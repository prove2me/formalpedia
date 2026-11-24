-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:40.974866+00:00
-- url     : https://prove2.me/submissions/e635b1b7-9d72-4b61-92de-cd15e1c057f7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution (I PPs : Finset ℕ) (a : ℕ → ℂ) (c : ℕ → ℝ) (ha : ∀ n, ‖a n‖ ≤ c n) :
    ∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)| := by
  have key : ((∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, a n * (starRingEnd ℂ) (a n') *
        ((∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ) : ℝ) : ℂ) := by
    push_cast
    have : ∀ q ∈ PPs, ((‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ : ℂ)) ^ 2 =
        ∑ n ∈ I, ∑ n' ∈ I, a n * (starRingEnd ℂ) (a n') *
          ((jacobiSym (n : ℤ) q : ℂ) * (jacobiSym (n' : ℤ) q : ℂ)) := by
      intro q _
      rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro n' _
      simp only [map_mul, map_intCast]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro n' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _
    rw [jacobiSym.mul_left]
    push_cast
    ring
  have hnn : 0 ≤ ∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hc : ∀ n, 0 ≤ c n := fun n => (norm_nonneg _).trans (ha n)
  calc ∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2
      = ‖((∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    _ ≤ _ := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
        rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (ha n) (ha n') (norm_nonneg _) (hc n)) (abs_nonneg _)
end Formalism.HermitianLattices.GL2PrimeSums
