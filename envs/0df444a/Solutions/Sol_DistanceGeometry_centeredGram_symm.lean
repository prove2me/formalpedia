-- Prove2me | solution 1 for DistanceGeometry.centeredGram_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:08.493019+00:00
-- url     : https://prove2.me/submissions/c30c1b0c-2a81-49a3-9afc-5562a11c214d

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Theorems.Thm_DistanceGeometry_sqDistMatrix_apply
public import Theorems.Thm_DistanceGeometry_centeredGram_apply
attribute [local simp] DistanceGeometry.sqDistMatrix_apply
attribute [local simp] DistanceGeometry.centeredGram_apply

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}
namespace DistanceGeometry
theorem _root_.solution [NeZero n] {D : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ i j, D i j = D j i) (i j : Fin n) :
    centeredGram D i j = centeredGram D j i := by
  simp only [centeredGram_apply]
  rw [hsymm i j, add_comm (D 0 i)]
end DistanceGeometry
