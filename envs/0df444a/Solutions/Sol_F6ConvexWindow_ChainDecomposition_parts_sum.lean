-- Prove2me | solution 1 for F6ConvexWindow.ChainDecomposition.parts_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:40:16.92408+00:00
-- url     : https://prove2.me/submissions/e3d3431f-788d-4371-92f7-d7a2f8ef5e84

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
open F6ConvexWindow.ChainDecomposition
variable {k : ℕ} (d : ChainDecomposition (V := V) k)
namespace F6ConvexWindow.ChainDecomposition
theorem _root_.solution (f : V → ℕ) : (∑ i, ∑ x ∈ d.part i, f x) = ∑ x, f x := by
  exact sum_fiberwise univ d.color f
end F6ConvexWindow.ChainDecomposition
