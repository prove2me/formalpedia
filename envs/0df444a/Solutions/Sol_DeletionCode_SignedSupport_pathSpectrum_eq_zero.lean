-- Prove2me | solution 1 for DeletionCode.SignedSupport.pathSpectrum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:09:56.185148+00:00
-- url     : https://prove2.me/submissions/3f2beac4-4581-4765-9cb1-99b8179ffa02

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution (p : Letters) (L D : ℕ) (g : Gram L)
    (hg : g ∉ windowSet p L D) : pathSpectrum p L D g = 0 := by
  classical
  unfold pathSpectrum
  apply Finset.sum_eq_zero
  intro i hi
  exact if_neg (fun he => hg ⟨i, he⟩)
end DeletionCode.SignedSupport
