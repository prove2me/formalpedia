-- Prove2me | solution 1 for DistanceGeometry.centeredGram_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:45:29.028555+00:00
-- url     : https://prove2.me/submissions/120efaa5-150e-4e06-8f3f-3debe19f0843

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}
namespace DistanceGeometry
theorem _root_.solution [NeZero n] (D : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    centeredGram D i j = (D 0 i + D 0 j - D i j) / 2 := rfl
end DistanceGeometry
