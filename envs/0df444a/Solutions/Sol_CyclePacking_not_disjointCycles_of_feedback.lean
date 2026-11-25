-- Prove2me | solution 1 for CyclePacking.not_disjointCycles_of_feedback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:36.257952+00:00
-- url     : https://prove2.me/submissions/b1824c20-6b2e-4456-9082-e5518e03b0ae

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Definitions.Def_ErdosPosaCycles_Solution
public import Theorems.Thm_ErdosPosa_not_disjointCycles_of_feedback


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CyclePacking
universe u
namespace CyclePacking
theorem _root_.solution {V : Type u} [Finite V] (G : SimpleGraph V) {X : Set V}
    (hX : IsFeedbackSet G X) : ¬ HasDisjointCycles G (X.ncard + 1) :=
  ErdosPosa.not_disjointCycles_of_feedback G hX
end CyclePacking
