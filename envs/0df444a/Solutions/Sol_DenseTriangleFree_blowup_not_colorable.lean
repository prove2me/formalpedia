-- Prove2me | solution 1 for DenseTriangleFree.blowup_not_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:23.723978+00:00
-- url     : https://prove2.me/submissions/4e35bb68-e9c7-4e6d-9b34-b12c7dbd17d8

module
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Blowup
public import Theorems.Thm_DenseTriangleFree_grotzsch_not_colorable


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution (m : ℕ) (hm : 0 < m) : ¬ (blowup m).Colorable 3 := by
  rintro ⟨c⟩
  apply grotzsch_not_colorable
  have sec : ∀ x : Fin 11, ∃ a : Fin (29 * m), blowProj m a = x := by
    intro x
    obtain ⟨k, hk⟩ : ∃ k : Fin 29, slotProj k = x := by revert x; decide
    exact ⟨finProdFinEquiv (k, ⟨0, hm⟩), by simp [blowProj, hk]⟩
  choose s hs using sec
  refine ⟨Coloring.mk (fun x => c (s x)) fun {x y} h => c.valid ?_⟩
  change grotzsch.Adj (blowProj m (s x)) (blowProj m (s y))
  rw [hs, hs]; exact h
end DenseTriangleFree
