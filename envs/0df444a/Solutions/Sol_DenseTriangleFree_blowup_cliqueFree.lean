-- Prove2me | solution 1 for DenseTriangleFree.blowup_cliqueFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:37.381739+00:00
-- url     : https://prove2.me/submissions/7023e99c-6ce9-4772-be2b-8e6150f26b25

module
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Blowup
public import Theorems.Thm_DenseTriangleFree_grotzsch_triangle


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution (m : ℕ) : (blowup m).CliqueFree 3 := by
  intro s hs
  classical
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
  exact grotzsch_triangle _ _ _ hab hbc hac
end DenseTriangleFree
