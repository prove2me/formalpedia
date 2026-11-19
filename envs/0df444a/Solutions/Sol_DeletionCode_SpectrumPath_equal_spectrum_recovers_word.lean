-- Prove2me | solution 1 for DeletionCode.SpectrumPath.equal_spectrum_recovers_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:23:02.510819+00:00
-- url     : https://prove2.me/submissions/9e63d0e0-d549-4d17-9294-21f7ce2afa36

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_at_occurrence_positive
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_iff_agree
import Theorems.Thm_DeletionCode_SignedSupport_wordSpectrum_nonzero_occurs
import Theorems.Thm_DeletionCode_WordPaths_all_windows_occur_implies_subword


set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word z : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1))
    (hspectrum : wordSpectrum z n L = wordSpectrum word n L) :
    Agree z 0 word 0 n := by
  have hwindows : ∀ i, i ≤ n - L → WordPaths.Occurs word n z i L := by
    intro i hi
    have hibound : i + L ≤ n := by omega
    have hz : wordSpectrum z n L (gram z L i) ≠ 0 :=
      ne_of_gt (spectrum_at_occurrence_positive z n L i (gram z L i) hibound rfl)
    have hy : wordSpectrum word n L (gram z L i) ≠ 0 := by
      rw [← hspectrum]
      exact hz
    obtain ⟨a, ha, hgram⟩ := wordSpectrum_nonzero_occurs word n L (gram z L i) hy
    exact ⟨a, ha, (gram_eq_iff_agree word z L a i).mp hgram⟩
  obtain ⟨a, ha, hagree⟩ := WordPaths.all_windows_occur_implies_subword
    word z n (L - 1) L (n - L) hunique (by omega) hwindows
  have hlength : L + (n - L) = n := by omega
  rw [hlength] at ha hagree
  have ha0 : a = 0 := by omega
  subst a
  intro i hi
  exact (hagree i hi).symm
end DeletionCode.SpectrumPath
