-- Prove2me | solution 1 for DeletionCode.BubbleLocalSpectrum.oriented_context_replacement_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:45.078417+00:00
-- url     : https://prove2.me/submissions/c20ebb06-02e2-4fac-abb2-be6ba8092be1

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Theorems.Thm_DeletionCode_BubbleLocalSpectrum_oriented_context_replacement

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.BubbleLocalSpectrum
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    wordSpectrum (listLetters (x ++ (bubble.positiveWord ++ y)))
        (x ++ (bubble.positiveWord ++ y)).length (windowLength k) -
      wordSpectrum (listLetters (x ++ (bubble.negativeWord ++ y)))
        (x ++ (bubble.negativeWord ++ y)).length (windowLength k) =
      wordSpectrum (listLetters bubble.positiveWord) bubble.positiveWord.length (windowLength k) -
        wordSpectrum (listLetters bubble.negativeWord) bubble.negativeWord.length (windowLength k) := by
  funext g
  exact oriented_context_replacement bubble x y g
end DeletionCode.BubbleLocalSpectrum
