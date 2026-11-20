-- Prove2me | solution 1 for DeletionCode.SpectrumPrefixChange.spectrum_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:23.91251+00:00
-- url     : https://prove2.me/submissions/a71f19ae-85b1-4bfd-9597-7a8272cc6480

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_right
import Theorems.Thm_DeletionCode_SpectrumLocalization_spectrum_split
import Theorems.Thm_DeletionCode_SpectrumLocalization_wordSpectrum_congr

section
namespace DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization
private theorem windowSum_zero (x : Letters) (L start : ℕ) (g : Gram L) :
    windowSum x L start 0 g = 0 := by simp [windowSum]
end DeletionCode.SpectrumPrefixChange
end

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.SpectrumPrefixChange
theorem _root_.solution (pre p : List Bool) (L : ℕ) (hp : L ≤ p.length + 1)
    (g : Gram L) :
    spectrum (pre ++ p) L g =
      windowSum (listLetters (pre ++ p)) L 0 pre.length g + spectrum p L g := by
  have h := spectrum_split (listLetters (pre ++ p)) pre.length p.length 0 L hp g
  rw [wordSpectrum_congr _ (listLetters p) p.length L
    (fun i _ => listLetters_append_right pre p i)] at h
  simpa only [spectrum, List.length_append, Nat.add_zero, windowSum_zero, add_zero] using h
end DeletionCode.SpectrumPrefixChange
