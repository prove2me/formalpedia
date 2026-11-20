-- Prove2me | solution 1 for DeletionCode.SpectrumPath.spectrum_at_occurrence_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:41.83667+00:00
-- url     : https://prove2.me/submissions/d0de3f6f-c105-4fdb-ac48-cebf15fa42ca

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
import Theorems.Thm_DeletionCode_SpectrumPath_gram_position_unique

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word : Letters) (n L a : ℕ) (g : Gram L)
    (hunique : KUnique word n (L - 1))
    (ha : a + L ≤ n) (hg : gram word L a = g) :
    wordSpectrum word n L g = 1 := by
  classical
  let occurrence : Fin (n + 1) := ⟨a, by omega⟩
  unfold wordSpectrum
  have hsingle := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i : Fin (n + 1) => if i.val + L ≤ n ∧ gram word L i.val = g then (1 : ℤ) else 0)
    occurrence
    (by
      intro i hi hne
      apply if_neg
      rintro ⟨hibound, hgram⟩
      have hval := gram_position_unique word n L i.val a hunique hibound ha (hgram.trans hg.symm)
      exact hne (Fin.ext hval))
    (fun hnot => False.elim (hnot (Finset.mem_univ occurrence)))
  exact hsingle.trans (by simp [occurrence, ha, hg])
end DeletionCode.SpectrumPath
