-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.catalogueRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:37.480868+00:00
-- url     : https://prove2.me/submissions/3a8e73f2-088b-418a-a969-948826169b48

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_validCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_rule_spectrum

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {t k : ℕ} (words : Fin (2 * t) → BubbleWord k)
    (hboundary : ∀ b, (words b).left.getLast? = some (!(words b).bit) ∧
      (words b).right.head? = some (!(words b).bit))
    (hgeometry : ∀ b, Geometry (words b))
    (hdisjoint : ∀ a b : Fin (2 * t), a ≠ b → ∀ sa sb i j,
      i + (windowLength k - 1) ≤ (pathWord (words a) sa).length →
      j + (windowLength k - 1) ≤ (pathWord (words b) sb).length →
      SpectrumPath.vertexAt (listLetters (pathWord (words a) sa)) (windowLength k) i ≠
        SpectrumPath.vertexAt (listLetters (pathWord (words b) sb)) (windowLength k) j)
    (hdel : (Finset.univ.filter (fun b => (words b).orientation = .deletion)).card = t)
    (hins : (Finset.univ.filter (fun b => (words b).orientation = .insertion)).card = t) :
    ConnectedBlocks.CatalogueRule t k
      (∑ b, (wordSpectrum (listLetters (words b).positiveWord)
        (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord)
          (words b).negativeWord.length (windowLength k))) := by
  classical
  refine ⟨words, validCatalogue words hboundary hgeometry hdisjoint, ?_, ?_⟩
  · intro r
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    simpa only [and_self_left, true_and] using And.intro hdel hins
  · exact rule_spectrum words (fun _ => 0)
end DeletionCode.BubbleCatalogue
