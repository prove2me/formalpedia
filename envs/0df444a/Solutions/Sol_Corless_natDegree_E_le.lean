-- Prove2me | solution 1 for Corless.natDegree_E_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:10.960261+00:00
-- url     : https://prove2.me/submissions/6e97c3ef-c940-45e5-99a9-cc06bb8222e8

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Theorems.Thm_Corless_natDegree_Dv_le

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless
namespace Corless
theorem _root_.solution (s : ℕ → ℤ) (j : ℕ) : (E s j).natDegree ≤ j := by
  unfold E
  rw [natDegree_expand]
  have h1 := natDegree_map_le (f := Int.castRingHom ℂ) (p := Dv s j)
  have h2 := natDegree_Dv_le s j
  have : (Polynomial.map (Int.castRingHom ℂ) (Dv s j)).natDegree * 2 ≤ j / 2 * 2 := by
    exact Nat.mul_le_mul_right 2 (h1.trans h2)
  omega
end Corless
