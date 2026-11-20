-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:23.448175+00:00
-- url     : https://prove2.me/submissions/90c54795-b701-482a-8b0c-f5ceff487767

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
import Theorems.Thm_DeletionCode_SpectrumLocalization_spectrum_split
import Theorems.Thm_DeletionCode_SpectrumLocalization_windowSum_congr
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_iff_agree


set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x y : Letters) (a p q b L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p + 1) (hq : L ≤ q + 1)
    (hleft : Agree x 0 y 0 (a + (L - 1)))
    (hright : Agree x (a + (p + 1 - L)) y (a + (q + 1 - L)) (b + (L - 1)))
    (g : Gram L) :
    wordSpectrum y (a + q + b) L g - wordSpectrum x (a + p + b) L g =
      wordSpectrum (fun i => y (a + i)) q L g -
        wordSpectrum (fun i => x (a + i)) p L g := by
  have hbefore : windowSum x L 0 a g = windowSum y L 0 a g := by
    apply windowSum_congr
    intro i hi
    apply (gram_eq_iff_agree _ _ _ _ _).mpr
    intro j hj
    simpa only [Nat.zero_add] using hleft (i + j) (by omega)
  have hafter : windowSum x L (a + (p + 1 - L)) b g =
      windowSum y L (a + (q + 1 - L)) b g := by
    apply windowSum_congr
    intro i hi
    apply (gram_eq_iff_agree _ _ _ _ _).mpr
    intro j hj
    simpa only [Nat.add_assoc] using hright (i + j) (by omega)
  rw [spectrum_split x a p b L hp, spectrum_split y a q b L hq, hbefore, hafter]
  omega
end DeletionCode.SpectrumLocalization
