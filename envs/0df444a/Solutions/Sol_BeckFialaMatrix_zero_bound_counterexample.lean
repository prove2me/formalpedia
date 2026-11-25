-- Prove2me | solution 1 for BeckFialaMatrix.zero_bound_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:00:57.296806+00:00
-- url     : https://prove2.me/submissions/6a12bdfc-ac8a-4643-ac54-1368aa286f0c

module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_BeckFialaMatrix_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution :
    ¬ (∀ (m N t : ℕ) (A : Fin m → Fin N → ℤ), (∀ j i, A j i = 0 ∨ A j i = 1) →
        (∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t) →
        ∀ x : Fin N → ℚ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
        ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
          ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ)) := by
  intro h
  obtain ⟨y, -, hbd⟩ := h 1 1 0 (fun _ _ => 0) (fun _ _ => Or.inl rfl)
    (by intro i; simp) (fun _ => 0) (by intro i; norm_num)
  have := hbd 0
  simp at this
end BeckFialaMatrix
