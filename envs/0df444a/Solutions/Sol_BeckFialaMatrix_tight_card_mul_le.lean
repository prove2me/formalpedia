-- Prove2me | solution 1 for BeckFialaMatrix.tight_card_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:55:59.680803+00:00
-- url     : https://prove2.me/submissions/6880f439-cd5a-4cfb-aa26-f320ec9a59bf

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
theorem _root_.solution {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t) (x : Fin N → ℚ) :
    (univ.filter (fun j => t < floatingDegree A x j)).card * (t + 1) ≤
      (floatingCoordinates x).card * t := by
  classical
  set F := floatingCoordinates x with hF
  set T := univ.filter (fun j => t < floatingDegree A x j) with hT
  have key : ∀ j ∈ T, t + 1 ≤ floatingDegree A x j := by
    intro j hj
    simp only [hT, mem_filter, mem_univ, true_and] at hj
    omega
  have h2 : ∑ j ∈ T, floatingDegree A x j = ∑ i ∈ F, (T.filter (fun j => A j i = 1)).card := by
    simp only [floatingDegree, Finset.card_filter, ← hF]
    exact Finset.sum_comm
  have h3 : ∀ i ∈ F, (T.filter (fun j => A j i = 1)).card ≤ t := by
    intro i _
    refine le_trans (card_le_card ?_) (hdeg i)
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact hj.2
  calc T.card * (t + 1) = ∑ _j ∈ T, (t + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ j ∈ T, floatingDegree A x j := Finset.sum_le_sum key
    _ = ∑ i ∈ F, (T.filter (fun j => A j i = 1)).card := h2
    _ ≤ ∑ _i ∈ F, t := Finset.sum_le_sum h3
    _ = F.card * t := by rw [Finset.sum_const, smul_eq_mul]
end BeckFialaMatrix
