-- Prove2me | solution 1 for DenseTriangleFree.key_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:55.781805+00:00
-- url     : https://prove2.me/submissions/c3c023b8-7576-4322-9ca2-8a30d2840d77

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
public import Definitions.Def_JinLib_KeyLemma
public import Theorems.Thm_DenseTriangleFree_normal_form
public import Theorems.Thm_DenseTriangleFree_isPair_comp
public import Theorems.Thm_DenseTriangleFree_sSet_comp
public import Theorems.Thm_DenseTriangleFree_patZ_01234_of
public import Theorems.Thm_DenseTriangleFree_patZ_0123_of
public import Theorems.Thm_DenseTriangleFree_patZ_012_of
public import Theorems.Thm_DenseTriangleFree_patZ_013_of
public import Theorems.Thm_DenseTriangleFree_patZ_01_of
public import Theorems.Thm_DenseTriangleFree_patZ_02_of
public import Theorems.Thm_DenseTriangleFree_patZ_0_of
public import Theorems.Thm_DenseTriangleFree_patZ_none_of


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [DecidableRel G.Adj]
namespace DenseTriangleFree
theorem _root_.solution (h3 : G.CliqueFree 3)
    (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
    (hδ : 10 * Fintype.card V < 29 * G.minDegree) (a : V) (U : Fin 5 → V)
    (hp : IsPair G a U) : False := by
  classical
  obtain ⟨p, hpmem, hpbest⟩ := Finset.exists_max_image
    (Finset.univ.filter fun p : V × (Fin 5 → V) => IsPair G p.1 p.2)
    (fun p => (sSet G p.1 p.2).card) ⟨(a, U), by simpa using hp⟩
  have hp0 : IsPair G p.1 p.2 := by simpa using hpmem
  have hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W →
      (sSet G b W).card ≤ (sSet G p.1 p.2).card :=
    fun b W h => hpbest (b, W) (by simpa using h)
  obtain ⟨r, s, hcard, hT⟩ := normal_form (sSet G p.1 p.2)
  have hp' := isPair_comp G hp0 r s
  rw [← sSet_comp] at hcard hT
  rw [← hcard] at hbest
  rcases hT with h | h | h | h | h | h | h | h <;> rw [h] at hbest <;>
    simp only [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
      Finset.card_singleton, Finset.card_empty, or_self, not_false_eq_true,
      Fin.reduceEq] at hbest
  · exact patZ_01234_of G h3 hδ _ _ hp' h
  · exact patZ_0123_of G h3 hδ _ _ hp' h
  · exact patZ_012_of G h3 hδ hbest _ _ hp' h
  · exact patZ_013_of G h3 hmax hδ hbest _ _ hp' h
  · exact patZ_01_of G h3 hδ hbest _ _ hp' h
  · exact patZ_02_of G h3 hmax hδ hbest _ _ hp' h
  · exact patZ_0_of G h3 hmax hδ hbest _ _ hp' h
  · exact patZ_none_of G h3 hmax hδ hbest _ _ hp' h
end DenseTriangleFree
