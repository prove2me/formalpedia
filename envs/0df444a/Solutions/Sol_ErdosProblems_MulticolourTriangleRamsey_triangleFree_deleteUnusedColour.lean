-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.triangleFree_deleteUnusedColour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/b5bc0e78-853d-45d5-99d3-2b4829772be5

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (k + 1)))
    (omitted : Fin (k + 1))
    (hunused : ∀ edge : (⊤ : SimpleGraph (Fin n)).edgeSet,
      C edge ≠ omitted)
    (hC : TriangleFree C) :
    TriangleFree (deleteUnusedColour C omitted hunused) := by
  classical
  intro colour t ht
  let lifted : Fin (k + 1) :=
    ((omittedColourEquiv k omitted).symm colour).val
  have hmono :
      (deleteUnusedColour C omitted hunused).labelGraph colour ≤
        C.labelGraph lifted := by
    intro x y hadj
    obtain ⟨hxy, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mpr
    refine ⟨hxy, ?_⟩
    change
      omittedColourEquiv k omitted
        ⟨C.get x y hxy, hunused ⟨s(x, y), hxy⟩⟩ = colour at hcolour
    have hvalue := congrArg
      (fun c : Fin k => ((omittedColourEquiv k omitted).symm c).val)
      hcolour
    simpa [lifted] using hvalue
  exact hC lifted t (ht.mono hmono)
end ErdosProblems.MulticolourTriangleRamsey
