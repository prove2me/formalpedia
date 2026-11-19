-- Prove2me | solution 1 for DeletionCode.SignedSupport.wordSpectrum_nonzero_occurs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:10:57.71419+00:00
-- url     : https://prove2.me/submissions/4b3901c0-3044-4a8c-9568-554066bcbe7c

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution (x : Letters) (n L : ℕ) (g : Gram L)
    (h : wordSpectrum x n L g ≠ 0) : ∃ a, a + L ≤ n ∧ gram x L a = g := by
  classical
  by_contra hnone
  apply h
  unfold wordSpectrum
  apply Finset.sum_eq_zero
  intro a ha
  exact if_neg (fun hh => hnone ⟨a.val, hh⟩)
end DeletionCode.SignedSupport
