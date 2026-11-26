-- Prove2me | solution 1 for DenseTriangleFree.grotzsch_cliqueFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:05.692478+00:00
-- url     : https://prove2.me/submissions/0c9c9572-77ff-4d5d-b910-8eea8e042195

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Theorems.Thm_DenseTriangleFree_grotzsch_triangle

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution : grotzsch.CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
  exact grotzsch_triangle a b c hab hbc hac
end DenseTriangleFree
