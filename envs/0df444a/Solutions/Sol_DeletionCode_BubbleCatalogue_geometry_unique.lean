-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.geometry_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:52.794321+00:00
-- url     : https://prove2.me/submissions/95e74244-7c3c-411e-8a08-f9fbfe0c7234

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_long_short_lengths

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (hg : Geometry bubble)
    (side : Bool) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ (pathWord bubble side).length)
    (hj : j + (windowLength k - 1) ≤ (pathWord bubble side).length)
    (heq : SpectrumPath.vertexAt (listLetters (pathWord bubble side)) (windowLength k) i =
      SpectrumPath.vertexAt (listLetters (pathWord bubble side)) (windowLength k) j) : i = j := by
  have hlens := long_short_lengths bubble
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  have hlong (hi : i ≤ windowLength k - bubble.rho + 1)
      (hj : j ≤ windowLength k - bubble.rho + 1)
      (heq : SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i =
        SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) j) : i = j :=
    congrArg Fin.val (hg.long_simple (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) heq)
  have hshort (hi : i ≤ windowLength k - bubble.rho)
      (hj : j ≤ windowLength k - bubble.rho)
      (heq : SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i =
        SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) j) : i = j :=
    congrArg Fin.val (hg.short_simple (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) heq)
  cases side <;> cases ho : bubble.orientation <;>
    simp only [pathWord, BubbleWord.negativeWord, BubbleWord.positiveWord, ho,
      Bool.false_eq_true, ite_false, ite_true] at hi hj heq
  · exact hlong (by omega) (by omega) heq
  · exact hshort (by omega) (by omega) heq
  · exact hshort (by omega) (by omega) heq
  · exact hlong (by omega) (by omega) heq
end DeletionCode.BubbleCatalogue
