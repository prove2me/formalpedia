-- Prove2me | solution 1 for Corless.charmatrix_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:34.467403+00:00
-- url     : https://prove2.me/submissions/721a09d7-5dec-4099-8e26-6055305d6243

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless
namespace Corless
theorem _root_.solution (m : ℕ) (u : ℕ → ℂ) : charmatrix (T m u) = CM m u := rfl
end Corless
