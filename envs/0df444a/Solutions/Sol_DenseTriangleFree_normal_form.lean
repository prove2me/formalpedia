-- Prove2me | solution 1 for DenseTriangleFree.normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:12.831033+00:00
-- url     : https://prove2.me/submissions/ffc342d0-e5be-4bea-bdff-3c6b38bed53a

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
public import Definitions.Def_JinLib_KeyLemma

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution : ∀ S : Finset (Fin 5), ∃ r : Fin 5, ∃ s : Bool,
    (Finset.univ.filter fun i => sig r s i ∈ S).card = S.card ∧
    ((Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2, 3, 4} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2, 3} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 3} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 2} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = ∅) := by
  decide +kernel
end DenseTriangleFree
