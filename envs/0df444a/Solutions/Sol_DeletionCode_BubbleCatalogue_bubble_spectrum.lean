-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.bubble_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:00.036472+00:00
-- url     : https://prove2.me/submissions/b4bea7a0-ac73-4e1d-89e7-283625191447

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_pathWord_length_ge
import Theorems.Thm_DeletionCode_BubbleCatalogue_family_path
import Theorems.Thm_DeletionCode_BubbleCatalogue_family_extra
import Theorems.Thm_DeletionCode_BubbleCatalogue_wordSpectrum_eq_pathSpectrum

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) :
    bubbleSpectrum (editedFamily words rank).family (windowLength k) b =
      wordSpectrum (listLetters (words b).positiveWord) (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord) (words b).negativeWord.length (windowLength k) := by
  have hp : windowLength k ≤ (words b).positiveWord.length := by
    simpa only [pathWord, ite_true] using pathWord_length_ge (words b) true
  have hn : windowLength k ≤ (words b).negativeWord.length := by
    simpa only [pathWord, Bool.false_eq_true, ite_false] using pathWord_length_ge (words b) false
  rw [wordSpectrum_eq_pathSpectrum _ _ _ hp, wordSpectrum_eq_pathSpectrum _ _ _ hn]
  funext g
  simp only [bubbleSpectrum, family_path, family_extra, pathWord, Bool.false_eq_true,
    ite_false, ite_true, Pi.sub_apply]
end DeletionCode.BubbleCatalogue
