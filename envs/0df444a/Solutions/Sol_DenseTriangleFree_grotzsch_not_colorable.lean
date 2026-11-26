-- Prove2me | solution 1 for DenseTriangleFree.grotzsch_not_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:00.544798+00:00
-- url     : https://prove2.me/submissions/0125b07b-dc18-4945-8686-4a249227040c

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Theorems.Thm_DenseTriangleFree_grotzsch_not_colorable_aux

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution : ¬ grotzsch.Colorable 3 := by
  rintro ⟨c⟩
  have h : ∀ i j : Fin 11, grotzschAdjB i j = true → c i ≠ c j := fun i j h => c.valid h
  exact grotzsch_not_colorable_aux (c 0) (c 1) (h 0 1 rfl) (c 2) (h 1 2 rfl) (c 3) (h 2 3 rfl)
    (c 4) (h 3 4 rfl) (h 4 0 rfl) (c 5) (h 5 1 rfl) (h 5 4 rfl) (c 6) (h 6 2 rfl) (h 6 0 rfl)
    (c 7) (h 7 3 rfl) (h 7 1 rfl) (c 8) (h 8 4 rfl) (h 8 2 rfl) (c 9) (h 9 0 rfl) (h 9 3 rfl)
    (c 10) (h 10 5 rfl) (h 10 6 rfl) (h 10 7 rfl) (h 10 8 rfl) (h 10 9 rfl)
end DenseTriangleFree
