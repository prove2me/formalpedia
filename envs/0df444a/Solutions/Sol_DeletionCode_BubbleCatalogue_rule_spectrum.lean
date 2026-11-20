-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.rule_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:22.834229+00:00
-- url     : https://prove2.me/submissions/31b76b78-8508-4df8-8331-4adcb54cb058

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_BubbleCatalogue_bubble_spectrum

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {k ν : ℕ} (words : Fin ν → BubbleWord k) (rank : Fin ν → ℕ) :
    ruleSpectrum (editedFamily words rank).family (windowLength k) Finset.univ =
      ∑ b, (wordSpectrum (listLetters (words b).positiveWord)
        (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord)
          (words b).negativeWord.length (windowLength k)) := by
  classical
  funext g
  simp only [ruleSpectrum, Finset.sum_apply, Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro b _
  exact congrFun (bubble_spectrum words rank b) g
end DeletionCode.BubbleCatalogue
