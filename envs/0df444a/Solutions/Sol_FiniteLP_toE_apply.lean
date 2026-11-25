-- Prove2me | solution 1 for FiniteLP.toE_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:27:15.725842+00:00
-- url     : https://prove2.me/submissions/5dc24aec-2cee-4eaa-9c41-25e276d3b533

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP
namespace FiniteLP
theorem _root_.solution {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) : toE f i = f i := rfl
end FiniteLP
