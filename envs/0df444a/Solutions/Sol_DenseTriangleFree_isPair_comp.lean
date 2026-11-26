-- Prove2me | solution 1 for DenseTriangleFree.isPair_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:25.243674+00:00
-- url     : https://prove2.me/submissions/979ff415-35e9-4196-8a84-bb1fabd6c276

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
public import Definitions.Def_JinLib_KeyLemma
public import Theorems.Thm_DenseTriangleFree_sig_step

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace DenseTriangleFree
theorem _root_.solution {a : V} {U : Fin 5 → V} (hp : IsPair G a U) (r : Fin 5) (s : Bool) :
    IsPair G a (U ∘ sig r s) := by
  refine ⟨fun i => ?_, fun i => hp.2 _⟩
  simp only [Function.comp]
  rcases sig_step r s i with h | h
  · rw [h]; exact hp.1 _
  · rw [h]; exact (hp.1 _).symm
end DenseTriangleFree
