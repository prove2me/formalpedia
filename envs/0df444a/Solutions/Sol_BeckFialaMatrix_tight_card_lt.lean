-- Prove2me | solution 1 for BeckFialaMatrix.tight_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:01:03.246832+00:00
-- url     : https://prove2.me/submissions/3612b41c-647a-4fc0-9463-db6080c887fb

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
public import Theorems.Thm_BeckFialaMatrix_tight_card_mul_le

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t) (x : Fin N → ℚ)
    (hne : (floatingCoordinates x).Nonempty) :
    (univ.filter (fun j => t < floatingDegree A x j)).card < (floatingCoordinates x).card := by
  have h := tight_card_mul_le A hdeg x
  have hpos : 0 < (floatingCoordinates x).card := card_pos.mpr hne
  by_contra hcon
  push Not at hcon
  nlinarith [Nat.mul_le_mul_right (t + 1) hcon]
end BeckFialaMatrix
