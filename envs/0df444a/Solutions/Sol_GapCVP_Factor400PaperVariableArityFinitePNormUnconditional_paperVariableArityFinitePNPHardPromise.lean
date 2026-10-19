-- Prove2me | solution 1 for GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePNPHardPromise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/6c4de950-c613-4d15-982d-4c039552dc06

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_PaperFinitePNormSourceReduction_paperVariableArityFiniteP_nphard_of_sourceMachine

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.Factor400PaperVariableArityFinitePNormUnconditional
open Turing GapCVP.BinaryEncoding GapCVP.CNFBoundedRecordFoldTM
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.FourFamilySoundness
open GapCVP.CanonicalMatrixShape GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.PhysicalNormalizedBranchTM GapCVP.PhysicalNormalizedCanonicalGuardTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianSourceConsistencyBridge
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceInitializerInstantiation
open GapCVP.GaussianOutputSerializerTM GapCVP.ExactPhysicalSourceTM
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePNormPromiseReduction
open GapCVP.Factor400FinitePRadiusArithmetic GapCVP.Factor400FinitePRadiusSourceTM
open GapCVP.Factor400FinitePRadiusRationalAtomTM GapCVP.PaperFinitePNormSourceReduction
namespace GapCVP.Factor400PaperVariableArityFinitePNormUnconditional
theorem _root_.solution
    (p : ℚ) (hp : 1 ≤ p) :
    NPHardPromise (finitePGapCVPPromise p hp) :=
  paperVariableArityFiniteP_nphard_of_sourceMachine p hp
    (paperVariableArityFinitePSourceMapMachine p hp)
end GapCVP.Factor400PaperVariableArityFinitePNormUnconditional
