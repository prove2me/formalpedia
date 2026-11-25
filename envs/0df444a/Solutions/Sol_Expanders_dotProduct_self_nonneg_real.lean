-- Prove2me | solution 1 for Expanders.dotProduct_self_nonneg_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:19:52.373642+00:00
-- url     : https://prove2.me/submissions/c360d3ba-5435-457e-a647-b186738765f8

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (x : V → ℝ) : 0 ≤ dotProduct x x :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
end Expanders
