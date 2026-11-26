-- Prove2me | solution 1 for DenseTriangleFree.triangle_of_cliqueFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:59.089793+00:00
-- url     : https://prove2.me/submissions/3058601e-1bc7-467c-ae81-c7a8cb6f16f7

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution {V : Type*} {G : SimpleGraph V} (h3 : G.CliqueFree 3) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) : False := by
  classical
  exact h3 {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
end DenseTriangleFree
