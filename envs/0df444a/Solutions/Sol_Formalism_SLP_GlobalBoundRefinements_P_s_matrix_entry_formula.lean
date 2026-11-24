-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.s_matrix_entry_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:24.737705+00:00
-- url     : https://prove2.me/submissions/33792347-4faa-4259-8ce9-a6033da63455

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : SEntry := by
  intro ga T T' hT hT'
  have hsT : (Real.sqrt T : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  have hsT' : (Real.sqrt T' : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT').ne'
  have hv : ∀ i, (![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hsT
    · simpa using hsT'
  have hinv : (Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)])⁻¹ =
      Matrix.diagonal (fun i => (![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)] i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    exact inv_mul_cancel₀ (hv _)
  rw [hinv]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hT.le, Real.sq_sqrt hT'.le]
  field_simp
end Formalism.SLP.GlobalBoundRefinements.P
