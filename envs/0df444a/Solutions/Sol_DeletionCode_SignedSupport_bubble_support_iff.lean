-- Prove2me | solution 1 for DeletionCode.SignedSupport.bubble_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:04:13.259561+00:00
-- url     : https://prove2.me/submissions/b168e0ab-d927-4fba-b0c4-864b8a4ab0d9

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_pathSpectrum_eq_zero
import Theorems.Thm_DeletionCode_SignedSupport_bubble_negative_value
import Theorems.Thm_DeletionCode_SignedSupport_bubble_positive_value

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L) :
    bubbleSpectrum F L b g ≠ 0 ↔ HasGram F L b g := by
  classical
  constructor
  · intro h
    by_contra hnone
    have hn : g ∉ windowSet (F.path b false) L (F.extra b false) :=
      fun hg => hnone ⟨false, hg⟩
    have hp : g ∉ windowSet (F.path b true) L (F.extra b true) :=
      fun hg => hnone ⟨true, hg⟩
    apply h
    rw [bubbleSpectrum, pathSpectrum_eq_zero _ _ _ _ hp,
      pathSpectrum_eq_zero _ _ _ _ hn]
    rfl
  · rintro ⟨side, hg⟩
    cases side with
    | false => rw [bubble_negative_value F L H b g hg]; decide
    | true => rw [bubble_positive_value F L H b g hg]; decide
end DeletionCode.SignedSupport
