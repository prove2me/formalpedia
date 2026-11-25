-- Prove2me | solution 1 for Expanders.dotProduct_adjMatrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:08:57.133684+00:00
-- url     : https://prove2.me/submissions/1bd9cb77-a3e5-4bab-a142-14e7944f5a07

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V → ℝ) :
    dotProduct x (G.adjMatrix ℝ *ᵥ y) = ∑ v, x v * ∑ w ∈ G.neighborFinset v, y w := by
  simp [dotProduct, adjMatrix_mulVec_apply]
end Expanders
