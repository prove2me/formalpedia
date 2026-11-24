-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.yBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:46.07855+00:00
-- url     : https://prove2.me/submissions/c70bbc24-2358-4424-849c-94e7936384d7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset Matrix Unitary
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : Formalism.HermitianLattices.CumulantEstimateDefs.EigenvalueSumBound := by
  intro N X hX
  have hsq : ∑ i, (hX.eigenvalues i) ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
    have h1 : (X * X).trace = ((∑ i, (hX.eigenvalues i) ^ 2 : ℝ) : ℂ) := by
      set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) with hD
      have hs : X = conjStarAlgAut ℂ _ hX.eigenvectorUnitary D := hX.spectral_theorem
      have hXX : X * X = conjStarAlgAut ℂ _ hX.eigenvectorUnitary (D * D) := by
        rw [map_mul, ← hs]
      rw [hXX, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul, hD,
        Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      push_cast
      apply Finset.sum_congr rfl; intro i _
      simp [sq]
    have h2 : (X * X).trace = ((∑ a, ∑ b, ‖X a b‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      push_cast
      apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
      have : X b a = star (X a b) := (hX.apply b a).symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    exact_mod_cast h1.symm.trans h2
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) (fun i => |hX.eigenvalues i|)
  have e1 : ∑ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) * |hX.eigenvalues i| =
      ∑ i, |hX.eigenvalues i| := by
    apply Finset.sum_congr rfl; intro i _
    by_cases h : hX.eigenvalues i = 0 <;> simp [h]
  have e2 : ∑ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) ^ 2 = (X.rank : ℝ) := by
    rw [hX.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    have : ∀ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) ^ 2 =
        if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0 := by
      intro i; split_ifs <;> simp
    simp only [this, Finset.sum_boole]
  have e3 : ∑ i, |hX.eigenvalues i| ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
    rw [← hsq]; apply Finset.sum_congr rfl; intro i _; exact sq_abs _
  rw [e1, e2, e3] at hcs
  exact hcs
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
