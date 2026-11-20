-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.validCatalogue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:18.788379+00:00
-- url     : https://prove2.me/submissions/881cafe8-08b0-457d-b9b7-c7bfbfbcf773

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_pathWord_length_ge
import Theorems.Thm_DeletionCode_BubbleCatalogue_family_extra
import Theorems.Thm_DeletionCode_BubbleCatalogue_family_vertex
import Theorems.Thm_DeletionCode_BubbleCatalogue_geometry_unique
import Theorems.Thm_DeletionCode_BubbleCatalogue_geometry_endpoints

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {k ν : ℕ} (words : Fin ν → BubbleWord k)
    (hboundary : ∀ b, (words b).left.getLast? = some (!(words b).bit) ∧
      (words b).right.head? = some (!(words b).bit))
    (hgeometry : ∀ b, Geometry (words b))
    (hdisjoint : ∀ a b : Fin ν, a ≠ b → ∀ sa sb i j,
      i + (windowLength k - 1) ≤ (pathWord (words a) sa).length →
      j + (windowLength k - 1) ≤ (pathWord (words b) sb).length →
      SpectrumPath.vertexAt (listLetters (pathWord (words a) sa)) (windowLength k) i ≠
        SpectrumPath.vertexAt (listLetters (pathWord (words b) sb)) (windowLength k) j) :
    ValidCatalogue words (fun _ => (0 : Fin 1)) := by
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  refine ⟨hboundary, ?_, ?_, ?_⟩
  · intro b side i j heq
    apply Fin.ext
    apply geometry_unique (words b) (hgeometry b) side i.val j.val
    · have hi := i.isLt
      have hlen := pathWord_length_ge (words b) side
      change i.val < (editedFamily words (fun _ => 0)).family.extra b side + 2 at hi
      rw [family_extra] at hi
      omega
    · have hj := j.isLt
      have hlen := pathWord_length_ge (words b) side
      change j.val < (editedFamily words (fun _ => 0)).family.extra b side + 2 at hj
      rw [family_extra] at hj
      omega
    · simpa only [indexedFamily, family_vertex] using heq
  · intro b i j hi hj heq
    change i ≤ (editedFamily words (fun _ => 0)).family.extra b false + 1 at hi
    change j ≤ (editedFamily words (fun _ => 0)).family.extra b true + 1 at hj
    have hn := pathWord_length_ge (words b) false
    have hp := pathWord_length_ge (words b) true
    rw [family_extra] at hi hj
    simp only [pathWord, Bool.false_eq_true, ite_false, ite_true] at hi hj hn hp
    have h := geometry_endpoints (words b) (hgeometry b) i j (by omega)
      (by omega) (by simpa only [indexedFamily, family_vertex, pathWord,
        Bool.false_eq_true, ite_false, ite_true] using heq)
    simpa only [indexedFamily, family_extra, pathWord, Bool.false_eq_true, ite_false, ite_true] using h
  · intro r a _ b _ hab sa sb i j hi hj
    change SupportComponents.vertex (editedFamily words (fun _ => 0)).family _ a sa i ≠
      SupportComponents.vertex (editedFamily words (fun _ => 0)).family _ b sb j
    rw [family_vertex, family_vertex]
    apply hdisjoint a b hab sa sb i j
    · have hn := pathWord_length_ge (words a) sa
      change i ≤ (editedFamily words (fun _ => 0)).family.extra a sa + 1 at hi
      rw [family_extra] at hi
      omega
    · have hn := pathWord_length_ge (words b) sb
      change j ≤ (editedFamily words (fun _ => 0)).family.extra b sb + 1 at hj
      rw [family_extra] at hj
      omega
end DeletionCode.BubbleCatalogue
