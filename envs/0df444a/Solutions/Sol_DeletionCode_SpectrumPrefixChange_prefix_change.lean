-- Prove2me | solution 1 for DeletionCode.SpectrumPrefixChange.prefix_change
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:39.538662+00:00
-- url     : https://prove2.me/submissions/05ddc3b7-6293-482f-847a-41cd1af70872

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Theorems.Thm_DeletionCode_SpectrumPrefixChange_spectrum_append
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_iff_agree
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_left
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_right
import Theorems.Thm_DeletionCode_SpectrumLocalization_windowSum_congr


set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.SpectrumPrefixChange
theorem _root_.solution (pre p q : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p.length + 1) (hq : L ≤ q.length + 1)
    (hprefix : Agree (listLetters p) 0 (listLetters q) 0 (L - 1)) (g : Gram L) :
    spectrum (pre ++ q) L g - spectrum (pre ++ p) L g =
      spectrum q L g - spectrum p L g := by
  have hbefore : windowSum (listLetters (pre ++ p)) L 0 pre.length g =
      windowSum (listLetters (pre ++ q)) L 0 pre.length g := by
    apply windowSum_congr
    intro i hi
    apply (gram_eq_iff_agree _ _ _ _ _).mpr
    intro j hj
    simp only [Nat.zero_add]
    by_cases hpre : i + j < pre.length
    · rw [listLetters_append_left pre p _ hpre, listLetters_append_left pre q _ hpre]
    · have hindex : i + j = pre.length + (i + j - pre.length) := by omega
      rw [hindex, listLetters_append_right, listLetters_append_right]
      simpa only [Nat.zero_add] using hprefix (i + j - pre.length) (by omega)
  rw [spectrum_append pre q L hq, spectrum_append pre p L hp, hbefore]
  omega
end DeletionCode.SpectrumPrefixChange
