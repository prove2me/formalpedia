-- Prove2me | solution 1 for GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine.paperVariableArityPhysicalIntegerTargetNPHardPromise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/75f9bbf9-48d2-4309-958d-801ab976bbcf

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_polynomialTimeClosedUnderComposition
import Theorems.Thm_GapCVP_nphardPromise_of_nphard_of_promiseReduction
import Theorems.Thm_GapCVP_OriginalThreeSATNPHardness_paperOriginalThreeSATIsNPHard

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine
open GapCVP.OriginalThreeSATNPHardness GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.ExactPhysicalSourceTM
namespace GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine
theorem _root_.solution :
    NPHardPromise integerTargetGapCVP400Promise :=
  nphardPromise_of_nphard_of_promiseReduction paperOriginalThreeSATIsNPHard
    paperVariableArityPhysicalIntegerTargetSourceReduction
    polynomialTimeClosedUnderComposition
end GapCVP.Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine
