-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:32.386303+00:00
-- url     : https://prove2.me/submissions/bb6e06d3-e4f5-457b-916b-98839de07f98

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_sum_ind

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
theorem _root_.solution (P : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (o mf : ℕ → ℕ) (μ : ℕ → ℕ → ℝ)
    (δ : ℝ) (r r' : ℕ)
    (hpt : ∀ n ∈ P, ∀ n' ∈ P, |μ n n'| ≤ δ + (if mf n = mf n' then (1 : ℝ) else 0)
      + (if o n = 1 ∧ o n' = 1 then (1 : ℝ) else 0)
      + (if o n = r ∧ o n' = r' then (1 : ℝ) else 0)
      + (if o n = r' ∧ o n' = r then (1 : ℝ) else 0)) :
    ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * |μ n n'| ≤
      δ * (∑ n ∈ P, c n) ^ 2
      + ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if mf n = mf n' then (1 : ℝ) else 0)
      + (∑ n ∈ P.filter (fun n => o n = 1), c n) ^ 2
      + 2 * ((∑ n ∈ P.filter (fun n => o n = r), c n) * (∑ n ∈ P.filter (fun n => o n = r'), c n)) := by
  have e1 : δ * (∑ n ∈ P, c n) ^ 2 = ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * δ := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n' _
    ring
  have e2 := gl2a5_sum_ind P c (fun n => o n = 1) (fun n => o n = 1)
  have e3 := gl2a5_sum_ind P c (fun n => o n = r) (fun n => o n = r')
  have e4 := gl2a5_sum_ind P c (fun n => o n = r') (fun n => o n = r)
  have e5 : 2 * ((∑ n ∈ P.filter (fun n => o n = r), c n) * (∑ n ∈ P.filter (fun n => o n = r'), c n)) =
      (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = r ∧ o n' = r' then (1 : ℝ) else 0)) +
      (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = r' ∧ o n' = r then (1 : ℝ) else 0)) := by
    rw [e3, e4]; ring
  have e6 : (∑ n ∈ P.filter (fun n => o n = 1), c n) ^ 2 =
      (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = 1 ∧ o n' = 1 then (1 : ℝ) else 0)) := by
    rw [e2]; ring
  rw [e1, e6, e5, ← add_assoc]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro n hn
  apply Finset.sum_le_sum; intro n' hn'
  have := mul_le_mul_of_nonneg_left (hpt n hn n' hn') (mul_nonneg (hc n) (hc n'))
  calc _ ≤ _ := this
    _ = _ := by ring
end Formalism.HermitianLattices.GL2PrimeSums
