-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.wordSpectrum_eq_windowSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:34:16.048041+00:00
-- url     : https://prove2.me/submissions/0cf87d11-634d-45db-afe4-cfd2019ff4f5

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x : Letters) (n L : ℕ) (hL : L ≤ n + 1)
    (g : Gram L) : wordSpectrum x n L g = windowSum x L 0 (n + 1 - L) g := by
  classical
  unfold wordSpectrum windowSum
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if i + L ≤ n ∧ gram x L i = g then (1 : ℤ) else 0) (n + 1)]
  have hsub : Finset.range (n + 1 - L) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub (by
    intro i _ hi
    have hib : ¬ i < n + 1 - L := by simpa only [Finset.mem_range] using hi
    have hbad : ¬ i + L ≤ n := by omega
    simp only [hbad, false_and, ite_false])]
  apply Finset.sum_congr rfl
  intro i hi
  have hib := Finset.mem_range.mp hi
  have hgood : i + L ≤ n := by omega
  simp only [hgood, true_and, Nat.zero_add]
end DeletionCode.SpectrumLocalization
