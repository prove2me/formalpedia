-- Prove2me | solution 1 for GapCVP.Comparator.yesLanguage_iff_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/c60a90dc-9890-4eb5-8fdf-31e462cac747

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
    yesLanguage bits ↔
      GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine.integerTargetGapCVP400Promise.yes bits := by
  simp only [yesLanguage, hasIntegerTarget, gapYES400, wellFormed,
    GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine.integerTargetGapCVP400Promise,
    GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine.HasIntegerTarget,
    GapCVP.gapYES400, GapCVP.gapCVPWellFormed, decide_eq_true_eq]
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
  exact exists_congr fun _ => by
    simp only [encodeInstance_eq_original]
    rfl
end GapCVP.Comparator
