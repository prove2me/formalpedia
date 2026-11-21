-- Prove2me | solution 1 for Corless.entrySign_I
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:39.100169+00:00
-- url     : https://prove2.me/submissions/0d1d2af5-3ba2-4c64-b0cf-d9f1c62641f6

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Theorems.Thm_Corless_I_ne_one
public import Theorems.Thm_Corless_entrySign_one
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero


attribute [local simp] Corless.entrySign_one

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless
namespace Corless
theorem _root_.solution : entrySign Complex.I = -1 := by simp [entrySign, I_ne_one]
end Corless
