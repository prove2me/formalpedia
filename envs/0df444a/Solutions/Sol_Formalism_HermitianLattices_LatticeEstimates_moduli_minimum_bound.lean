-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.moduli_minimum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:53.087619+00:00
-- url     : https://prove2.me/submissions/c1fee891-f189-41c8-80e7-1c3031d4e325

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
theorem _root_.solution : Ms_min := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by simpa using hx
  have hN : (1:ℝ) ≤ ∏ φ : K →+* ℂ, ‖φ (x:K)‖ := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.norm ℚ (x:K)) = ∏ σ : K →ₐ[ℚ] ℂ, σ (x:K) :=
      Algebra.norm_eq_prod_embeddings ℚ ℂ (x:K)
    have h2 : ∏ φ : K →+* ℂ, ‖φ (x:K)‖ = ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ (x:K))‖ := by
      rw [h1, norm_prod]
      exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
    rw [h2, ← Algebra.coe_norm_int x]
    have h3 : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    simp
    exact_mod_cast Int.one_le_abs h3
  have hpos : ∀ φ : K →+* ℂ, 0 < ‖φ (x:K)‖ := fun φ => norm_pos_iff.mpr ((map_ne_zero φ).mpr hx')
  have hlog : 0 ≤ ∑ φ : K →+* ℂ, Real.log (‖φ (x:K)‖ ^ 2) := by
    rw [← Real.log_prod (fun φ _ => (pow_pos (hpos φ) 2).ne'), Finset.prod_pow]
    exact Real.log_nonneg (one_le_pow₀ hN)
  have : ∑ φ : K →+* ℂ, (1 + Real.log (‖φ (x:K)‖ ^ 2)) ≤ ∑ φ : K →+* ℂ, ‖φ (x:K)‖ ^ 2 :=
    Finset.sum_le_sum fun φ _ => by
      linarith [Real.add_one_le_exp (Real.log (‖φ (x:K)‖ ^ 2)), Real.exp_log (pow_pos (hpos φ) 2)]
  rw [Finset.sum_add_distrib] at this
  simp only [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, mul_one] at this
  linarith
end Formalism.HermitianLattices.LatticeEstimates
