-- Prove2me | solution 1 for GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFiniteP_nphard_of_sourceMachine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/6fca37f8-ac91-40ef-aef1-f508ea31f6e6

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
open GapCVP.PaperFinitePNormSourceReduction
open scoped BigOperators
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryInstanceBridge GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.OriginalThreeSATNPHardness
open GapCVP.SourcePreprocessingSemantics GapCVP.SourcePreprocessingTM GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.NormalizedRecordDecoder GapCVP.PhysicalWordSoundness
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePNormPromiseReduction
open GapCVP.Factor400FinitePNormSourceReduction GapCVP.Factor400FinitePNormUnconditional
open GapCVP.Factor400FinitePRadiusArithmetic GapCVP.Factor400FinitePRadiusBounds
namespace GapCVP.PaperFinitePNormSourceReduction
theorem _root_.solution
    (p : ℚ) (hp : 1 ≤ p)
    (machine : BitTM (paperVariableArityFinitePSourceMap p hp)) :
    NPHardPromise (finitePGapCVPPromise p hp) :=
  nphardPromise_of_nphard_of_promiseReduction
    paperOriginalThreeSATIsNPHard
    (paperVariableArityFinitePSourceReductionOfMachine p hp machine)
    polynomialTimeClosedUnderComposition
end GapCVP.PaperFinitePNormSourceReduction
