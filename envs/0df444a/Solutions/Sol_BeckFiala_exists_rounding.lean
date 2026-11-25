-- Prove2me | solution 1 for BeckFiala.exists_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:40:03.192951+00:00
-- url     : https://prove2.me/submissions/d9eef455-c0e4-49a3-ba73-6607abbfa28e

module
public import Mathlib
public import Definitions.Def_LeanPool_BeckFialaMatrix
public import Definitions.Def_BeckFiala_Solution
public import Theorems.Thm_BeckFialaMatrix_exists_rounding


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
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) :=
  BeckFialaMatrix.exists_rounding ht A hA hdeg x hx
end BeckFiala
