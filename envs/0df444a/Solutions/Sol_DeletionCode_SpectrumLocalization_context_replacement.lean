-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.context_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:38.950127+00:00
-- url     : https://prove2.me/submissions/2e5788cd-99ad-48e4-a167-79dca6e07aeb

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
import Theorems.Thm_DeletionCode_SpectrumLocalization_replacement
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_left
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_middle
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_suffix
import Theorems.Thm_DeletionCode_SpectrumLocalization_wordSpectrum_congr

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x p q y : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p.length + 1) (hq : L ≤ q.length + 1)
    (hprefix : Agree (listLetters p) 0 (listLetters q) 0 (L - 1))
    (hsuffix : Agree (listLetters p) (p.length + 1 - L)
      (listLetters q) (q.length + 1 - L) (L - 1)) (g : Gram L) :
    wordSpectrum (listLetters (x ++ (q ++ y))) (x.length + q.length + y.length) L g -
      wordSpectrum (listLetters (x ++ (p ++ y))) (x.length + p.length + y.length) L g =
      wordSpectrum (listLetters q) q.length L g - wordSpectrum (listLetters p) p.length L g := by
  have hleft : Agree (listLetters (x ++ (p ++ y))) 0
      (listLetters (x ++ (q ++ y))) 0 (x.length + (L - 1)) := by
    intro i hi
    simp only [Nat.zero_add]
    by_cases hix : i < x.length
    · rw [listLetters_append_left x (p ++ y) i hix,
        listLetters_append_left x (q ++ y) i hix]
    · have heq : i = x.length + (i - x.length) := by omega
      rw [heq, listLetters_middle x p y _ (by omega),
        listLetters_middle x q y _ (by omega)]
      simpa only [Nat.zero_add] using hprefix (i - x.length) (by omega)
  have hright : Agree (listLetters (x ++ (p ++ y))) (x.length + (p.length + 1 - L))
      (listLetters (x ++ (q ++ y))) (x.length + (q.length + 1 - L))
      (y.length + (L - 1)) := by
    intro i hi
    by_cases hlocal : i < L - 1
    · rw [Nat.add_assoc, Nat.add_assoc,
        listLetters_middle x p y _ (by omega), listLetters_middle x q y _ (by omega)]
      exact hsuffix i hlocal
    · have hpindex : x.length + (p.length + 1 - L) + i =
          x.length + p.length + (i - (L - 1)) := by omega
      have hqindex : x.length + (q.length + 1 - L) + i =
          x.length + q.length + (i - (L - 1)) := by omega
      rw [hpindex, hqindex, listLetters_suffix, listLetters_suffix]
  have h := replacement (listLetters (x ++ (p ++ y))) (listLetters (x ++ (q ++ y)))
    x.length p.length q.length y.length L hL hp hq hleft hright g
  rw [wordSpectrum_congr _ (listLetters q) q.length L
      (fun i hi => listLetters_middle x q y i hi),
    wordSpectrum_congr _ (listLetters p) p.length L
      (fun i hi => listLetters_middle x p y i hi)] at h
  exact h
end DeletionCode.SpectrumLocalization
