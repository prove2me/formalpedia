-- Prove2me | solution 1 for GapCVP.Comparator.noLanguage_iff_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/e227c834-e5c7-4f65-a082-2c6b251da05a

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_Comparator_toOriginal_ofOriginal
import Theorems.Thm_GapCVP_Comparator_toOriginalNearest_ofOriginalNearest
import Theorems.Thm_GapCVP_Comparator_toOriginalSyndrome_ofOriginalSyndrome
import Theorems.Thm_GapCVP_Comparator_encodeInstance_eq_original
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
    noLanguage bits ↔
      GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine.integerTargetGapCVP400Promise.no bits := by
  simp only [noLanguage, hasIntegerTarget, gapNO400, wellFormed,
    GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine.integerTargetGapCVP400Promise,
    GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine.HasIntegerTarget,
    GapCVP.gapNO400, GapCVP.gapCVPWellFormed, decide_eq_true_eq]
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
  exact exists_congr fun _ => by
    simp only [encodeInstance_eq_original]
    rfl
end GapCVP.Comparator
