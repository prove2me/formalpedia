-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.meansq_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:27.166+00:00
-- url     : https://prove2.me/submissions/9898c527-6c86-4b7b-85e4-f9225e675eba

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (PP I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ)
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (J : ℕ → ℕ → ℤ) :
    (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by
  have key : ((∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, ((c n : ℝ) : ℂ) * ((c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
        ((∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ) : ℝ) : ℂ) := by
    have h1 : ∀ q, ((‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ I, ∑ n' ∈ I, ((c n : ℝ) : ℂ) * ((c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
          (((J n q * J n' q : ℤ) : ℝ) : ℂ) := by
      intro q
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
      simp only [map_mul, Complex.conj_ofReal, map_intCast]
      push_cast
      ring
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
  calc (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2)
      ≤ ‖((∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real]; exact le_abs_self _
    _ ≤ ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
          RCLike.norm_conj, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hc n),
          abs_of_nonneg (hc n')]
        have h2 : ‖κ n‖ * ‖κ n'‖ ≤ 1 := by
          have := mul_le_mul (hκ n) (hκ n') (norm_nonneg _) zero_le_one
          simpa using this
        have h3 : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
        have h4 : c n * c n' * (‖κ n‖ * ‖κ n'‖) ≤ c n * c n' := by
          simpa using mul_le_mul_of_nonneg_left h2 h3
        exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
