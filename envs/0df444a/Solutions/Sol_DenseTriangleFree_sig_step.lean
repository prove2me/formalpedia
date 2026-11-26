-- Prove2me | solution 1 for DenseTriangleFree.sig_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:18.914308+00:00
-- url     : https://prove2.me/submissions/e03e1722-12aa-4b1d-a624-75710a9d887d

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
theorem _root_.solution : ∀ (r : Fin 5) (s : Bool) (i : Fin 5),
    sig r s (i + 1) = sig r s i + 1 ∨ sig r s i = sig r s (i + 1) + 1 := by decide
end DenseTriangleFree
