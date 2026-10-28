-- Prove2me | solution 1 for CountingMatroid.Analysis.SlotBlockSignature.slot_block_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:42:58.242984+00:00
-- url     : https://prove2.me/submissions/ae875b86-43d4-42d3-8856-8fd8d873b328

import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
set_option autoImplicit false

/-!
The block-matrix calculation for the transport Hessian. This module proves
the implication from a one-positive-direction bound to the balanced slot
inequality; it does not assert that operational weights satisfy that bound.
-/

namespace CountingMatroid.Analysis.SlotBlockSignature
end CountingMatroid.Analysis.SlotBlockSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SlotBlockSignature

open scoped BigOperators

/-- INTERNAL: Expansion of the transport block matrix's quadratic form.
TEXLINE: main.tex:595-625 -/
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (V : α → α → ℝ) (sₐ sᵦ h : α → ℝ) (u x y : ℝ) :
    (slotBlockMatrix V sₐ sᵦ u).toQuadraticForm' (slotBlockVector h x y) =
      (∑ i, ∑ j, V i j * h i * h j) +
        2 * x * (∑ i, sᵦ i * h i) +
        2 * y * (∑ i, sₐ i * h i) + 2 * u * x * y := by
  change Matrix.toLinearMap₂' ℝ (slotBlockMatrix V sₐ sᵦ u)
    (slotBlockVector h x y) (slotBlockVector h x y) = _
  rw [Matrix.toLinearMap₂'_apply]
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, slotBlockMatrix,
    slotBlockVector, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
    Bool.true_eq_false, ite_true, ite_false, smul_eq_mul,
    mul_zero, zero_mul, Finset.sum_add_distrib]
  ring_nf
  have hsum (c : ℝ) (s : α → ℝ) :
      (∑ i, c * h i * s i) = c * ∑ i, s i * h i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdouble : (∑ i, ∑ j, h i * h j * V i j) =
      ∑ i, ∑ j, V i j * h i * h j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, hsum, hdouble]
  ring
