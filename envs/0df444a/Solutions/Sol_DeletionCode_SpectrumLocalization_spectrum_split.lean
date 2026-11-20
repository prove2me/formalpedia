-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.spectrum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:13.813012+00:00
-- url     : https://prove2.me/submissions/6ac2da2f-7012-4be9-a74e-958fa2f8ab0f

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
import Theorems.Thm_DeletionCode_SpectrumLocalization_wordSpectrum_eq_windowSum
import Theorems.Thm_DeletionCode_SpectrumLocalization_windowSum_add
import Theorems.Thm_DeletionCode_SpectrumLocalization_windowSum_shift

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x : Letters) (a p b L : ℕ) (hp : L ≤ p + 1) (g : Gram L) :
    wordSpectrum x (a + p + b) L g =
      windowSum x L 0 a g + wordSpectrum (fun i => x (a + i)) p L g +
        windowSum x L (a + (p + 1 - L)) b g := by
  rw [wordSpectrum_eq_windowSum x _ L (by omega),
    wordSpectrum_eq_windowSum _ p L hp]
  have hcount : a + p + b + 1 - L = (a + (p + 1 - L)) + b := by omega
  rw [hcount, windowSum_add, windowSum_add]
  simp only [Nat.zero_add, windowSum_shift x L a]
end DeletionCode.SpectrumLocalization
