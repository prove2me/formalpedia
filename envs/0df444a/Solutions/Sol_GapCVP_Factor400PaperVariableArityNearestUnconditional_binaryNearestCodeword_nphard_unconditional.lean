-- Prove2me | solution 1 for GapCVP.Factor400PaperVariableArityNearestUnconditional.binaryNearestCodeword_nphard_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/a57c6737-261e-4a08-ada1-7dc1c33c39a8

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
open GapCVP.Factor400PaperVariableArityNearestUnconditional
open GapCVP.Factor400BinaryDecodingPromiseHardness GapCVP.OriginalThreeSATNPHardness
open GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.PaperNearestGaussianPayloadTM GapCVP.PaperNearestRoutedSource
namespace GapCVP.Factor400PaperVariableArityNearestUnconditional
theorem _root_.solution :
    NPHardPromise binaryNearestCodewordPromise :=
  nphardPromise_of_nphard_of_promiseReduction
    paperOriginalThreeSATIsNPHard
    paperVariableArityNearestUnconditionalSourceReduction
    polynomialTimeClosedUnderComposition
end GapCVP.Factor400PaperVariableArityNearestUnconditional
