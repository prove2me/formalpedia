-- Prove2me | solution 1 for DeletionCode.SignedSupport.bubble_negative_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:03:30.637176+00:00
-- url     : https://prove2.me/submissions/50bb2663-8f04-49a5-bc74-37ab9fd4ce36

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
    (hn : g ∈ windowSet (F.path b false) L (F.extra b false)) :
    bubbleSpectrum F L b g = -1 := by
  have hp : g ∉ windowSet (F.path b true) L (F.extra b true) :=
    no_common_bubble_gram F L H b g hn
  rw [bubbleSpectrum, pathSpectrum_eq_zero _ _ _ _ hp,
    pathSpectrum_eq_one _ _ _ _ (gram_injective_of_simple F L H b false) hn]
  decide
end DeletionCode.SignedSupport
