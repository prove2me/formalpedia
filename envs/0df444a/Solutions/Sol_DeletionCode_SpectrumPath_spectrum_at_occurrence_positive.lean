-- Prove2me | solution 1 for DeletionCode.SpectrumPath.spectrum_at_occurrence_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:21:52.701357+00:00
-- url     : https://prove2.me/submissions/ca089f55-8a15-49b8-825d-d4c49664fdc4

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word : Letters) (n L a : ℕ) (g : Gram L)
    (ha : a + L ≤ n) (hg : gram word L a = g) :
    0 < wordSpectrum word n L g := by
  classical
  let occurrence : Fin (n + 1) := ⟨a, by omega⟩
  have hsum :
      (if occurrence.val + L ≤ n ∧ gram word L occurrence.val = g then (1 : ℤ) else 0) ≤
      ∑ i : Fin (n + 1), if i.val + L ≤ n ∧ gram word L i.val = g then (1 : ℤ) else 0 := by
    apply Finset.single_le_sum (s := Finset.univ) (a := occurrence)
      (f := fun i : Fin (n + 1) =>
        if i.val + L ≤ n ∧ gram word L i.val = g then (1 : ℤ) else 0)
    · intro i hi
      split_ifs <;> omega
    · exact Finset.mem_univ occurrence
  have hone : (1 : ℤ) ≤ wordSpectrum word n L g := by
    simpa only [occurrence, ha, hg, and_self, ite_true, wordSpectrum] using hsum
  omega
end DeletionCode.SpectrumPath
