-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.halfSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:53.56484+00:00
-- url     : https://prove2.me/submissions/f4f95631-663a-466f-af86-281b4d0e5ea3

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
open Finset MeasureTheory
open scoped ComplexOrder
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution (N : ℕ) (sg : Fin N → Bool) (f : Fin N → Fin N → ℝ)
    (hs : ∀ a b, f a b = f b a) (h0 : ∀ a b, sg a = sg b → f a b = 0) :
    ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
  have split : ∀ a b, f a b = (if b < a then f a b else 0) + (if a < b then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, lt_asymm h]
    · subst h
      simp [h0 a a rfl]
    · simp [h, lt_asymm h]
  have swap : ∑ a, ∑ b, (if a < b then f a b else 0) = ∑ a, ∑ b, (if b < a then f a b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs]
  have filt : ∀ a, ∑ b, (if b < a then f a b else 0) =
      ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
    intro a
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b < a <;> by_cases hsg : sg a = sg b <;> simp [hb, hsg, h0 a b]
  calc ∑ a, ∑ b, f a b = ∑ a, ∑ b, (if b < a then f a b else 0) +
        ∑ a, ∑ b, (if a < b then f a b else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => split a b
    _ = 2 * ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
        rw [swap, ← two_mul]
        simp only [filt]
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
