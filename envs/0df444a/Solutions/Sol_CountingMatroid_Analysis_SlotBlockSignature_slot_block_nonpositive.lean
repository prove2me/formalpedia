-- Prove2me | solution 1 for CountingMatroid.Analysis.SlotBlockSignature.slot_block_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:26:25.929082+00:00
-- url     : https://prove2.me/submissions/a3691502-f8b5-4afd-b3ea-2de1ad5f0f2d

import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_SignatureOrthogonalNonpositive_signature_orthogonal_nonpositive
import Theorems.Thm_CountingMatroid_Analysis_SlotBlockSignature_slot_block_eval

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

/-- PAPER: main.tex:605-625
The one-positive-direction signature implies the balanced slot inequality,
using e=(0,1,1), on which the quadratic form equals 2u>0. -/
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (V : α → α → ℝ) (sₐ sᵦ : α → ℝ) (u : ℝ) (hu : 0 < u)
    (hsig : sigPos (slotBlockMatrix V sₐ sᵦ u).toQuadraticForm' ≤ 1)
    (h : α → ℝ) (x y : ℝ)
    (hbalance : (∑ i, (sₐ i + sᵦ i) * h i) + u * (x + y) = 0) :
    (∑ i, ∑ j, V i j * h i * h j) +
      2 * x * (∑ i, sᵦ i * h i) +
      2 * y * (∑ i, sₐ i * h i) + 2 * u * x * y ≤ 0 := by
  let Q := (slotBlockMatrix V sₐ sᵦ u).toQuadraticForm'
  let e : α ⊕ Bool → ℝ := slotBlockVector (fun _ => 0) 1 1
  let v : α ⊕ Bool → ℝ := slotBlockVector h x y
  have he : 0 < Q e := by
    dsimp only [Q, e]
    rw [slot_block_eval]
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) hu)
  have hev : e + v = slotBlockVector h (x + 1) (y + 1) := by
    ext j
    cases j with
    | inl i => simp [e, v, slotBlockVector]
    | inr b => cases b <;> simp [e, v, slotBlockVector, add_comm]
  have horth : Q.IsOrtho e v := by
    rw [QuadraticMap.isOrtho_def, hev]
    dsimp only [Q, e, v]
    simp only [slot_block_eval]
    simp only [mul_zero, Finset.sum_const_zero] 
    simp_rw [add_mul, Finset.sum_add_distrib] at hbalance
    nlinarith [hbalance]
  have hn := SignatureOrthogonalNonpositive.signature_orthogonal_nonpositive
    Q hsig e v he (QuadraticMap.associated_isOrtho.mpr horth)
  simpa only [Q, v, slot_block_eval] using hn
