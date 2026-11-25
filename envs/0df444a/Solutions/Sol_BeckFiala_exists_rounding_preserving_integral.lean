-- Prove2me | solution 1 for BeckFiala.exists_rounding_preserving_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:34:39.831986+00:00
-- url     : https://prove2.me/submissions/871ace77-c8e2-440f-b0ce-fe8ce4a7bc1b

module
public import Mathlib
public import Definitions.Def_LeanPool_BeckFialaMatrix
public import Definitions.Def_BeckFiala_Solution
public import Theorems.Thm_BeckFialaMatrix_exists_rounding_preserving_integral
public import Theorems.Thm_BeckFialaMatrix_mem_floatingCoordinates


set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFiala
namespace BeckFiala
theorem _root_.solution {m N t : ℕ} (ht : 1 ≤ t)
    (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      (∀ i, ¬ (0 < x i ∧ x i < 1) → (y i : ℚ) = x i) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  obtain ⟨y, hy, hfix, hbd⟩ :=
    BeckFialaMatrix.exists_rounding_preserving_integral ht A hA hdeg x hx
  exact ⟨y, hy, fun i hi => hfix i (by rwa [BeckFialaMatrix.mem_floatingCoordinates]), hbd⟩
end BeckFiala
