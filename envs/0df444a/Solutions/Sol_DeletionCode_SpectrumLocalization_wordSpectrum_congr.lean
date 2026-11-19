-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.wordSpectrum_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:34:50.76223+00:00
-- url     : https://prove2.me/submissions/527f99ca-2242-4fd4-9201-35bc69e5e77c

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x y : Letters) (n L : ℕ)
    (h : ∀ i, i < n → x i = y i) (g : Gram L) :
    wordSpectrum x n L g = wordSpectrum y n L g := by
  classical
  unfold wordSpectrum
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val + L ≤ n
  · have hgram : gram x L i.val = gram y L i.val := by
      funext j
      exact h (i.val + j.val) (by have := j.isLt; omega)
    rw [hgram]
  · simp only [hi, false_and, ite_false]
end DeletionCode.SpectrumLocalization
