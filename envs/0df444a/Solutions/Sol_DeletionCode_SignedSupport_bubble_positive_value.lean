-- Prove2me | solution 1 for DeletionCode.SignedSupport.bubble_positive_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:03:37.943904+00:00
-- url     : https://prove2.me/submissions/ab1e4b8c-7ef6-4da2-b1e2-5fb9d98a3931

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_gram_injective_of_simple
import Theorems.Thm_DeletionCode_SignedSupport_no_common_bubble_gram
import Theorems.Thm_DeletionCode_SignedSupport_pathSpectrum_eq_one
import Theorems.Thm_DeletionCode_SignedSupport_pathSpectrum_eq_zero

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L)
    (hp : g ∈ windowSet (F.path b true) L (F.extra b true)) :
    bubbleSpectrum F L b g = 1 := by
  have hn : g ∉ windowSet (F.path b false) L (F.extra b false) :=
    fun hn => no_common_bubble_gram F L H b g hn hp
  rw [bubbleSpectrum,
    pathSpectrum_eq_one _ _ _ _ (gram_injective_of_simple F L H b true) hp,
    pathSpectrum_eq_zero _ _ _ _ hn]
  decide
end DeletionCode.SignedSupport
