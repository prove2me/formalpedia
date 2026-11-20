-- Prove2me | solution 1 for DeletionCode.BubbleLocalSpectrum.context_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:01.135322+00:00
-- url     : https://prove2.me/submissions/272f594e-9c4f-4092-9b68-b2f59282c2cf

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Theorems.Thm_DeletionCode_BubbleLocalSpectrum_shared_prefix
import Theorems.Thm_DeletionCode_BubbleLocalSpectrum_shared_suffix
import Theorems.Thm_DeletionCode_BubbleLocalSpectrum_length_bounds
import Theorems.Thm_DeletionCode_SpectrumLocalization_context_replacement


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.BubbleLocalSpectrum
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (x y : List Bool)
    (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.shortWord ++ y)))
        (x ++ (bubble.shortWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.longWord ++ y)))
        (x ++ (bubble.longWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.shortWord) bubble.shortWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.longWord) bubble.longWord.length (windowLength k) g := by
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  simpa only [List.length_append, Nat.add_assoc] using
    SpectrumLocalization.context_replacement x bubble.longWord bubble.shortWord y
      (windowLength k) hL (length_bounds bubble).1 (length_bounds bubble).2
      (shared_prefix bubble) (shared_suffix bubble) g
end DeletionCode.BubbleLocalSpectrum
