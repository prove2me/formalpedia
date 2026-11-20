-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.geometry_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:53.277148+00:00
-- url     : https://prove2.me/submissions/8d9261a9-50f9-45ae-8847-d69faf58be98

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_long_short_lengths
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (hg : Geometry bubble) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ bubble.negativeWord.length)
    (hj : j + (windowLength k - 1) ≤ bubble.positiveWord.length)
    (heq : SpectrumPath.vertexAt (listLetters bubble.negativeWord) (windowLength k) i =
      SpectrumPath.vertexAt (listLetters bubble.positiveWord) (windowLength k) j) :
    (i = 0 ∧ j = 0) ∨
      (i = bubble.negativeWord.length - windowLength k + 1 ∧
        j = bubble.positiveWord.length - windowLength k + 1) := by
  have hlens := long_short_lengths bubble
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  cases ho : bubble.orientation <;>
    simp only [BubbleWord.negativeWord, BubbleWord.positiveWord, ho] at hi hj heq ⊢
  · have h := hg.endpoints i j (by omega) (by omega) (fun r hr => congrFun heq ⟨r, hr⟩)
    rcases h with h | h
    · exact Or.inl h
    · right; omega
  · have h := hg.endpoints j i (by omega) (by omega) (fun r hr => (congrFun heq ⟨r, hr⟩).symm)
    rcases h with h | h
    · left; exact ⟨h.2, h.1⟩
    · right; omega
end DeletionCode.BubbleCatalogue
