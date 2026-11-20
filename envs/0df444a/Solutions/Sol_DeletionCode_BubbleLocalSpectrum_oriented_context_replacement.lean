-- Prove2me | solution 1 for DeletionCode.BubbleLocalSpectrum.oriented_context_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:52.287178+00:00
-- url     : https://prove2.me/submissions/695fc369-2a7f-495d-9c58-1e00d9cc7986

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Theorems.Thm_DeletionCode_BubbleLocalSpectrum_context_replacement
import Theorems.Thm_DeletionCode_SpectrumLocalization_context_replacement


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.BubbleLocalSpectrum
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (x y : List Bool)
    (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.positiveWord ++ y)))
        (x ++ (bubble.positiveWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.negativeWord ++ y)))
        (x ++ (bubble.negativeWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.positiveWord) bubble.positiveWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.negativeWord) bubble.negativeWord.length (windowLength k) g := by
  have h := context_replacement bubble x y g
  cases ho : bubble.orientation with
  | deletion =>
    simpa only [BubbleWord.positiveWord, BubbleWord.negativeWord, ho] using h
  | insertion =>
    simp only [BubbleWord.positiveWord, BubbleWord.negativeWord, ho]
    omega
end DeletionCode.BubbleLocalSpectrum
