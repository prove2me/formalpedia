-- Prove2me | solution 1 for GapCVP.Comparator.binarySyndromeDecoding_yes_iff_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/4b1da76c-da89-4d9b-be30-6ea4cbccebf5

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_Comparator_toOriginal_ofOriginal
import Theorems.Thm_GapCVP_Comparator_toOriginalNearest_ofOriginalNearest
import Theorems.Thm_GapCVP_Comparator_toOriginalSyndrome_ofOriginalSyndrome
import Theorems.Thm_GapCVP_Comparator_encodeBinarySyndromeDecodingInstance_eq_original
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
    binarySyndromeDecodingPromise.yes bits ↔
      GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise.yes bits := by
  simp only [binarySyndromeDecodingPromise,
    GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise,
    decide_eq_true_eq]
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginalSyndrome_ofOriginalSyndrome).exists]
  exact exists_congr fun _ => by
    simp only [encodeBinarySyndromeDecodingInstance_eq_original]
    rfl
end GapCVP.Comparator
