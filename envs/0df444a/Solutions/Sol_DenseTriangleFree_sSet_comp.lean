-- Prove2me | solution 1 for DenseTriangleFree.sSet_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:54.26191+00:00
-- url     : https://prove2.me/submissions/bd0350a0-c6a6-48e2-93a9-0da09311e1ce

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
public import Definitions.Def_JinLib_KeyLemma
public import Theorems.Thm_DenseTriangleFree_sig_nbrs
public import Theorems.Thm_DenseTriangleFree_mem_sSet


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace DenseTriangleFree
theorem _root_.solution (a : V) (U : Fin 5 → V) (r : Fin 5) (s : Bool) :
    sSet G a (U ∘ sig r s) = Finset.univ.filter fun i => sig r s i ∈ sSet G a U := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_sSet, Function.comp]
  rcases sig_nbrs r s i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact ⟨fun ⟨t, h, h', h''⟩ => ⟨t, h, h'', h'⟩, fun ⟨t, h, h', h''⟩ => ⟨t, h, h'', h'⟩⟩
end DenseTriangleFree
