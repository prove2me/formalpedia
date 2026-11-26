-- Prove2me | solution 1 for DenseTriangleFree.heavyTest_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:16.320022+00:00
-- url     : https://prove2.me/submissions/2f4eb7be-1105-4427-adf4-d42e17e24e38

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution (ws : List ℕ) (Fb Js : List (List ℕ)) (l l' : List ℕ) (h : l.Perm l') :
    heavyTest ws Fb Js l = heavyTest ws Fb Js l' := by
  have hs : wsumL ws l = wsumL ws l' := (h.map _).sum_eq
  have hm : ∀ i, l.elem i = l'.elem i := by
    intro i
    rw [Bool.eq_iff_iff]
    simp only [List.elem_iff]
    exact h.mem_iff
  simp only [heavyTest, hs, hm]
end DenseTriangleFree
