-- Prove2me | solution 1 for DenseTriangleFree.jin_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:18.954068+00:00
-- url     : https://prove2.me/submissions/0d4b02a0-c1f5-43e7-bd24-d25e8d407130

module
public import Mathlib
public import Definitions.Def_JinLib_Blowup
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Bipartite
public import Definitions.Def_JinLib_Jin
public import Theorems.Thm_DenseTriangleFree_blowup_cliqueFree
public import Theorems.Thm_DenseTriangleFree_blowup_degree
public import Theorems.Thm_DenseTriangleFree_blowup_not_colorable


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution (m : ℕ) (hm : 0 < m) :
    ∃ G : SimpleGraph (Fin (29 * m)), ∃ _ : DecidableRel G.Adj,
      G.CliqueFree 3 ∧ (∀ v, G.degree v = 10 * m) ∧ ¬ G.Colorable 3 :=
  ⟨blowup m, inferInstance, blowup_cliqueFree m, blowup_degree m, blowup_not_colorable m hm⟩
end DenseTriangleFree
