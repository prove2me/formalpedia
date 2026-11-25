-- Prove2me | solution 1 for FiniteLP.inner_toE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:41.87862+00:00
-- url     : https://prove2.me/submissions/e2a2a1fc-8d1b-4bdb-9a09-ec11378772c5

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Theorems.Thm_FiniteLP_toE_apply
attribute [local simp] FiniteLP.toE_apply

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP
namespace FiniteLP
theorem _root_.solution {ι : Type*} [Fintype ι] (f : ι → ℝ) (y : EuclideanSpace ℝ ι) :
    (inner ℝ (toE f) y) = ∑ i, f i * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, toE, mul_comm]
end FiniteLP
