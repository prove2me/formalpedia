-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.block_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:42.532802+00:00
-- url     : https://prove2.me/submissions/5a83461b-c6fd-4b47-a3cb-203953a9ba3c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LatticeEstimates
open Finset MeasureTheory Matrix Real
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder
namespace Formalism.HermitianLattices.LatticeEstimates
theorem _root_.solution : WeightedCauchySchwarz := by
  intro ι _ w q c O hw hO
  have h1 : ‖∑ e, q e * (w e : ℂ) * c e‖ ≤ ∑ e, (‖q e‖ * Real.sqrt (w e)) * (‖c e‖ * Real.sqrt (w e)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun e _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw e).le]
    nth_rewrite 1 [← Real.mul_self_sqrt (hw e).le]
    ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun e => ‖q e‖ * Real.sqrt (w e))
    (fun e => ‖c e‖ * Real.sqrt (w e))
  have h3 : ∀ (x : ι → ℂ) e, (‖x e‖ * Real.sqrt (w e)) ^ 2 = ‖x e‖ ^ 2 * w e := by
    intro x e; rw [mul_pow, Real.sq_sqrt (hw e).le]
  simp only [h3] at h2
  have h4 : (∑ e, ‖q e‖ ^ 2 * w e) * O⁻¹ * ∑ e, ‖c e‖ ^ 2 * w e * O
      = (∑ e, ‖q e‖ ^ 2 * w e) * ∑ e, ‖c e‖ ^ 2 * w e := by
    rw [← Finset.sum_mul]; field_simp
  rw [h4]
  calc _ ≤ (∑ e, (‖q e‖ * Real.sqrt (w e)) * (‖c e‖ * Real.sqrt (w e))) ^ 2 := by gcongr
    _ ≤ _ := h2
end Formalism.HermitianLattices.LatticeEstimates
