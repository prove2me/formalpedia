-- Prove2me | solution 1 for GapCVP.Comparator.binaryNearestCodeword_yes_iff_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/89b75ef2-9f05-4838-993b-c39ffc851082

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_Comparator_toOriginal_ofOriginal
import Theorems.Thm_GapCVP_Comparator_toOriginalNearest_ofOriginalNearest
import Theorems.Thm_GapCVP_Comparator_toOriginalSyndrome_ofOriginalSyndrome
import Theorems.Thm_GapCVP_Comparator_encodeBinaryNearestCodewordInstance_eq_original
attribute [local simp] GapCVP.Comparator.toOriginal_ofOriginal
attribute [local simp] GapCVP.Comparator.toOriginalNearest_ofOriginalNearest
attribute [local simp] GapCVP.Comparator.toOriginalSyndrome_ofOriginalSyndrome

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
noncomputable section
open scoped BigOperators
open GapCVP.Comparator
namespace GapCVP.Comparator
theorem _root_.solution (bits : List Bool) :
    binaryNearestCodewordPromise.yes bits ↔
      GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise.yes bits := by
  simp only [binaryNearestCodewordPromise,
    GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise,
    decide_eq_true_eq]
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginalNearest_ofOriginalNearest).exists]
  exact exists_congr fun _ => by
    simp only [encodeBinaryNearestCodewordInstance_eq_original]
    rfl
end GapCVP.Comparator
