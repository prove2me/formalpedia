-- Prove2me | solution 1 for GapCVP.Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal.binarySyndromeDecoding_nphard_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/6dd8c35d-edc6-41b9-8965-9448f442c97b

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
open GapCVP.Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal
open GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness GapCVP.OriginalThreeSATNPHardness
open GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.PhysicalColumnOrder
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceConsistencyBridge
open GapCVP.PaperBinaryCodingTM GapCVP.PaperSyndromeInstance
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceWholeOutputAssemblyTM
namespace GapCVP.Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal
theorem _root_.solution :
    NPHardPromise binarySyndromeDecodingPromise :=
  nphardPromise_of_nphard_of_promiseReduction
    paperOriginalThreeSATIsNPHard
    (paperVariableAritySyndromeSourceReduction
      (paperVariableArityCanonicalPhysicalMatrixCellComputer
        paperCanonicalPhysicalMatrixShape))
    polynomialTimeClosedUnderComposition
end GapCVP.Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal
