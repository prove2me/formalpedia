-- Prove2me | solution 1 for DeletionCode.BubbleLocalSpectrum.length_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:23.756059+00:00
-- url     : https://prove2.me/submissions/161a94ce-8075-4759-933a-0a00e58ba453

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_longWord_length
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_shortWord_length


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.BubbleLocalSpectrum
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) :
    windowLength k ≤ bubble.longWord.length + 1 ∧
      windowLength k ≤ bubble.shortWord.length + 1 := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, shortLength, longLength,
    BubbleWord.header, windowLength]
  omega
end DeletionCode.BubbleLocalSpectrum
