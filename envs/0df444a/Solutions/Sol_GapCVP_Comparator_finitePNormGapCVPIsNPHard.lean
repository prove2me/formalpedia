-- Prove2me | solution 1 for GapCVP.Comparator.finitePNormGapCVPIsNPHard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/051515ba-48d2-492b-89ff-dc21a9a57ec7

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_Factor400PaperVariableArityFinitePNormUnconditional_paperVariableArityFinitePNPHardPromise
import Theorems.Thm_GapCVP_Comparator_toOriginal_ofOriginal
import Theorems.Thm_GapCVP_Comparator_toOriginalNearest_ofOriginalNearest
import Theorems.Thm_GapCVP_Comparator_toOriginalSyndrome_ofOriginalSyndrome
import Theorems.Thm_GapCVP_Comparator_finiteP_yes_iff_original
import Theorems.Thm_GapCVP_Comparator_finiteP_no_iff_original
attribute [local simp] GapCVP.Comparator.toOriginal_ofOriginal
attribute [local simp] GapCVP.Comparator.toOriginalNearest_ofOriginalNearest
attribute [local simp] GapCVP.Comparator.toOriginalSyndrome_ofOriginalSyndrome
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
macro "compact_machine_step_tac" "[" definitions:term,* "]" : tactic =>
  `(tactic|
    (simp [$[$definitions:term],*, Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
namespace GapCVP
namespace TraceGolf
end TraceGolf
open GapCVP.TraceGolf (oneStep rebound)
namespace Core
section
namespace GapCVPInstance
end GapCVPInstance
end
section
open scoped BigOperators
end
section
end
end Core
section
namespace BinaryEncoding
end BinaryEncoding
end
namespace BinaryEncoding
end BinaryEncoding
section
open Computability
end
section
namespace TMComposition
open Turing
end TMComposition
namespace PromiseReduction
end PromiseReduction
end
namespace CL
end CL
namespace ThreeCNFReduction
open GapCVP.CL
end ThreeCNFReduction
namespace CLVerifier
open Computability GapCVP.CL
end CLVerifier
namespace CLNondeterminism
open Computability GapCVP.CLVerifier
namespace FiniteRun
end FiniteRun
end CLNondeterminism
namespace CLBoundedStates
open Computability GapCVP.CLVerifier GapCVP.CLNondeterminism
end CLBoundedStates
namespace CLPushAlphabet
open Computability GapCVP.CLVerifier GapCVP.CLBoundedStates
end CLPushAlphabet
namespace CLStackSupport
open Computability GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
end CLStackSupport
namespace CLCellRows
open Computability GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
end CLCellRows
namespace CLCellRowBounds
open Computability GapCVP.CLNondeterminism
end CLCellRowBounds
namespace CLLocalWindows
open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows
end CLLocalWindows
namespace CLLocalRules
open Computability GapCVP.CLLocalWindows
end CLLocalRules
namespace CLTableauStitching
open Computability GapCVP.CLLocalWindows
end CLTableauStitching
namespace CLExactLocalRules
open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows
end CLExactLocalRules
namespace CLExactStackRules
open Computability GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
end CLExactStackRules
namespace CLExactVerifierRules
open Computability GapCVP.CLLocalWindows
end CLExactVerifierRules
namespace CLCompleteLocalCompiler
open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows
end CLCompleteLocalCompiler
namespace CLStackShiftSoundness2
open Computability GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRows
open GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler
end CLStackShiftSoundness2
namespace CLFiniteShiftWindows
open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows
open GapCVP.CLLocalWindows GapCVP.CLCompleteLocalCompiler
end CLFiniteShiftWindows
namespace CLStackWindowEquivalence
open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLStackShiftSoundness2 GapCVP.CLFiniteShiftWindows
end CLStackWindowEquivalence
namespace CLExactVerifierTransition
open Computability GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLExactStackRules
open GapCVP.CLCompleteLocalCompiler GapCVP.CLFiniteShiftWindows
end CLExactVerifierTransition
namespace CLEmittedCNFTM
open Computability Turing
end CLEmittedCNFTM
namespace CLWindowTruthTable
open Computability Turing GapCVP.CLEmittedCNFTM
end CLWindowTruthTable
namespace CLLocalTableauCompiler
open Computability Turing GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLExactStackRules GapCVP.CLExactVerifierRules GapCVP.CLCompleteLocalCompiler
end CLLocalTableauCompiler
namespace CLVerifierTableauEmission
open Computability Turing GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLFiniteShiftWindows
end CLVerifierTableauEmission
namespace CLUnconditionalTableau
open Computability Turing GapCVP.CLLocalWindows GapCVP.CLExactVerifierRules
end CLUnconditionalTableau
namespace CLGlobalTableauSimulation
open Computability Turing GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLExactStackRules GapCVP.CLExactVerifierRules GapCVP.CLCompleteLocalCompiler
open GapCVP.CLStackShiftSoundness2 GapCVP.CLFiniteShiftWindows GapCVP.CLStackWindowEquivalence
open GapCVP.CLExactVerifierTransition GapCVP.CLLocalTableauCompiler
open GapCVP.CLVerifierTableauEmission GapCVP.CLUnconditionalTableau
end CLGlobalTableauSimulation
namespace CLTableauSimulationCert
open Computability Turing GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLLocalRules GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler
open GapCVP.CLFiniteShiftWindows GapCVP.CLExactVerifierTransition GapCVP.CLLocalTableauCompiler
open GapCVP.CLGlobalTableauSimulation
end CLTableauSimulationCert
namespace CLFullTableauEmitter
open Computability Turing GapCVP.CLLocalWindows GapCVP.CLCompleteLocalCompiler
open GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
end CLFullTableauEmitter
namespace CLVerifierPhaseCert
open Computability Turing GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLPushAlphabet GapCVP.CLStackSupport GapCVP.CLCellRowBounds
end CLVerifierPhaseCert
namespace CLCompleteVerifierSimulation
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates
open GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactLocalRules GapCVP.CLExactStackRules GapCVP.CLExactVerifierTransition
open GapCVP.CLTableauSimulationCert GapCVP.CLFullTableauEmitter
end CLCompleteVerifierSimulation
namespace CLPhaseSoundness
open Computability Turing GapCVP.CLLocalWindows
end CLPhaseSoundness
namespace CLPhaseSpecification
open Computability Turing GapCVP.CLBoundedStates GapCVP.CLLocalWindows
open GapCVP.CLCompleteVerifierSimulation
end CLPhaseSpecification
namespace CLPhaseCompleteness
open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation
end CLPhaseCompleteness
namespace CLPhaseTableauSimulation
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLBoundedStates
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification GapCVP.CLPhaseCompleteness
end CLPhaseTableauSimulation
namespace CLPhaseTraceInduction
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates
open GapCVP.CLPushAlphabet GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
end CLPhaseTraceInduction
namespace CLPhaseGlobalSimulation
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRowBounds GapCVP.CLLocalWindows GapCVP.CLExactVerifierTransition
open GapCVP.CLTableauSimulationCert GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction
end CLPhaseGlobalSimulation
namespace CLPhaseVerifierSimulation
open Computability Turing GapCVP.CL GapCVP.CLPushAlphabet GapCVP.CLCellRowBounds
open GapCVP.CLExactVerifierTransition GapCVP.CLGlobalTableauSimulation
open GapCVP.CLTableauSimulationCert GapCVP.CLFullTableauEmitter GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
end CLPhaseVerifierSimulation
namespace CLValidTraceSoundness
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCellRowBounds
open GapCVP.CLLocalWindows GapCVP.CLTableauStitching GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation
end CLValidTraceSoundness
namespace CLWholeTraceSoundness
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLCellRowBounds
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLValidTraceSoundness
end CLWholeTraceSoundness
namespace CLFirstAcceptance
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLCellRowBounds
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation GapCVP.CLValidTraceSoundness
open GapCVP.CLWholeTraceSoundness
end CLFirstAcceptance
namespace CLArbitraryVerifierSoundness
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLLocalWindows
open GapCVP.CLTableauStitching GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseGlobalSimulation
end CLArbitraryVerifierSoundness
namespace CLStackShiftSoundness
open Computability Turing GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLExactVerifierTransition
end CLStackShiftSoundness
namespace CLStackVerifierSimulation
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRows
open GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler
open GapCVP.CLExactVerifierTransition GapCVP.CLLocalTableauCompiler
open GapCVP.CLVerifierTableauEmission GapCVP.CLUnconditionalTableau
open GapCVP.CLGlobalTableauSimulation GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseTableauSimulation GapCVP.CLStackShiftSoundness
end CLStackVerifierSimulation
namespace CLAnchoredTraceSimulation
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRowBounds GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLWholeTraceSoundness GapCVP.CLFirstAcceptance GapCVP.CLArbitraryVerifierSoundness
open GapCVP.CLStackVerifierSimulation
end CLAnchoredTraceSimulation
namespace CLArbitraryRowOccupancy
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLLocalWindows GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler
open GapCVP.CLTableauSimulationCert GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseGlobalSimulation GapCVP.CLStackVerifierSimulation
end CLArbitraryRowOccupancy
namespace CLWholeTimeOccupancy
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLCellRowBounds
open GapCVP.CLLocalWindows GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation GapCVP.CLValidTraceSoundness
open GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLArbitraryRowOccupancy
end CLWholeTimeOccupancy
namespace CLRawTrackSimulation
open Computability Turing GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLStackShiftSoundness
end CLRawTrackSimulation
namespace CLCompactWindowSoundness
open Computability Turing GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLStackShiftSoundness2
end CLCompactWindowSoundness
namespace CLNoHoleTimeInduction
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRows GapCVP.CLLocalWindows GapCVP.CLCompleteLocalCompiler
open GapCVP.CLStackShiftSoundness2 GapCVP.CLFiniteShiftWindows
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseGlobalSimulation GapCVP.CLStackShiftSoundness GapCVP.CLCompactWindowSoundness
end CLNoHoleTimeInduction
namespace CLBoundedRowInduction
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLFiniteShiftWindows GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation GapCVP.CLWholeTraceSoundness
open GapCVP.CLArbitraryVerifierSoundness GapCVP.CLStackShiftSoundness
open GapCVP.CLStackVerifierSimulation GapCVP.CLAnchoredTraceSimulation
open GapCVP.CLArbitraryRowOccupancy GapCVP.CLRawTrackSimulation GapCVP.CLCompactWindowSoundness
open GapCVP.CLNoHoleTimeInduction
end CLBoundedRowInduction
namespace CLFullStackStepSoundness
open Computability Turing GapCVP.CL GapCVP.CLBoundedStates GapCVP.CLPushAlphabet
open GapCVP.CLCellRows GapCVP.CLLocalWindows GapCVP.CLExactVerifierRules
open GapCVP.CLCompleteLocalCompiler GapCVP.CLStackShiftSoundness2 GapCVP.CLFiniteShiftWindows
open GapCVP.CLLocalTableauCompiler GapCVP.CLUnconditionalTableau
open GapCVP.CLGlobalTableauSimulation GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseGlobalSimulation GapCVP.CLValidTraceSoundness GapCVP.CLStackShiftSoundness
open GapCVP.CLStackVerifierSimulation GapCVP.CLArbitraryRowOccupancy GapCVP.CLRawTrackSimulation
open GapCVP.CLCompactWindowSoundness GapCVP.CLNoHoleTimeInduction GapCVP.CLBoundedRowInduction
end CLFullStackStepSoundness
namespace CLFullTraceReachability
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLBoundedStates
open GapCVP.CLCellRowBounds GapCVP.CLTableauSimulationCert GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLArbitraryRowOccupancy GapCVP.CLWholeTimeOccupancy
open GapCVP.CLCompactWindowSoundness GapCVP.CLNoHoleTimeInduction GapCVP.CLBoundedRowInduction
open GapCVP.CLFullStackStepSoundness
end CLFullTraceReachability
namespace CLGuessPayloadReachability
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactLocalRules GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction
open GapCVP.CLPhaseGlobalSimulation GapCVP.CLValidTraceSoundness GapCVP.CLWholeTraceSoundness
open GapCVP.CLStackVerifierSimulation GapCVP.CLAnchoredTraceSimulation
end CLGuessPayloadReachability
namespace CLReachableTableauCompiler
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds
open GapCVP.CLLocalWindows GapCVP.CLExactStackRules GapCVP.CLFiniteShiftWindows
open GapCVP.CLLocalTableauCompiler GapCVP.CLGlobalTableauSimulation
open GapCVP.CLTableauSimulationCert GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSoundness
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLRawTrackSimulation
open GapCVP.CLCompactWindowSoundness GapCVP.CLNoHoleTimeInduction GapCVP.CLBoundedRowInduction
open GapCVP.CLFullStackStepSoundness GapCVP.CLFullTraceReachability
open GapCVP.CLGuessPayloadReachability
end CLReachableTableauCompiler
namespace CLNaturalTimeCompiler
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLCellRowBounds GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseCompleteness GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLValidTraceSoundness GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLCompactWindowSoundness
open GapCVP.CLNoHoleTimeInduction GapCVP.CLBoundedRowInduction GapCVP.CLFullStackStepSoundness
open GapCVP.CLFullTraceReachability GapCVP.CLGuessPayloadReachability
open GapCVP.CLReachableTableauCompiler
end CLNaturalTimeCompiler
namespace CLAcceptanceAnchor
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates
open GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler GapCVP.CLExactVerifierTransition
open GapCVP.CLLocalTableauCompiler GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseTableauSimulation
open GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLStackVerifierSimulation GapCVP.CLArbitraryRowOccupancy
open GapCVP.CLCompactWindowSoundness GapCVP.CLBoundedRowInduction
open GapCVP.CLFullStackStepSoundness GapCVP.CLFullTraceReachability GapCVP.CLNaturalTimeCompiler
end CLAcceptanceAnchor
namespace CLVerifiedLocalTableauCompiler
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds
open GapCVP.CLLocalWindows GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLFullTableauEmitter GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLPhaseVerifierSimulation GapCVP.CLArbitraryVerifierSoundness
open GapCVP.CLStackVerifierSimulation GapCVP.CLAnchoredTraceSimulation
open GapCVP.CLGuessPayloadReachability GapCVP.CLAcceptanceAnchor
end CLVerifiedLocalTableauCompiler
namespace CLFinalTableauAssembly
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates
open GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactLocalRules GapCVP.CLExactStackRules GapCVP.CLFiniteShiftWindows
open GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseSpecification
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLStackVerifierSimulation GapCVP.CLGuessPayloadReachability
open GapCVP.CLReachableTableauCompiler GapCVP.CLAcceptanceAnchor
open GapCVP.CLVerifiedLocalTableauCompiler
end CLFinalTableauAssembly
namespace CLPaddedAcceptanceCompiler
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLTableauStitching GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert
open GapCVP.CLVerifierPhaseCert GapCVP.CLCompleteVerifierSimulation GapCVP.CLPhaseCompleteness
open GapCVP.CLPhaseTableauSimulation GapCVP.CLPhaseTraceInduction GapCVP.CLPhaseGlobalSimulation
open GapCVP.CLWholeTraceSoundness GapCVP.CLStackVerifierSimulation
open GapCVP.CLAnchoredTraceSimulation GapCVP.CLWholeTimeOccupancy
open GapCVP.CLCompactWindowSoundness GapCVP.CLBoundedRowInduction
open GapCVP.CLFullStackStepSoundness GapCVP.CLNaturalTimeCompiler GapCVP.CLAcceptanceAnchor
open GapCVP.CLVerifiedLocalTableauCompiler GapCVP.CLFinalTableauAssembly
end CLPaddedAcceptanceCompiler
namespace CLStructuralCNFVariableBounds
open GapCVP.CL GapCVP.ThreeCNFReduction
end CLStructuralCNFVariableBounds
namespace CLStructuralPrefixWriter
open Turing GapCVP.BinaryEncoding
macro "prefix_writer_step_tac" : tactic =>
  `(tactic|
    (simp [structuralPrefixWriter, prefixWriterConfiguration,
      prefixWriterPeek, prefixWriterPop, prefixWriterPushBit,
      prefixWriterPushMarker, prefixWriterGoto,
      prefixWriterScanStatement, prefixWriterRestoreStatement,
      prefixWriterMarkerStatement, Turing.haltList,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CLStructuralPrefixWriter
namespace SourceMachineCert
open Turing
end SourceMachineCert
namespace SourceMachineRouting
open SourceMachineCert
end SourceMachineRouting
namespace SourceUniformTuringTM
open Turing
end SourceUniformTuringTM
namespace SourceStructuralTuringTM
open Turing
end SourceStructuralTuringTM
namespace SourceStructuralDecoder
open Turing
end SourceStructuralDecoder
namespace SourceTotalStructuralDecoder
open Turing GapCVP.SourceStructuralDecoder
end SourceTotalStructuralDecoder
namespace SourceFormulaStructuralDecoder
open Turing GapCVP.SourceTotalStructuralDecoder
end SourceFormulaStructuralDecoder
namespace SourceVariableFormulaDecoder
open Turing GapCVP.SourceFormulaStructuralDecoder
end SourceVariableFormulaDecoder
namespace FormulaTuringTM
open Turing GapCVP.SourceVariableFormulaDecoder
end FormulaTuringTM
namespace FormulaCert
open Turing GapCVP.SourceVariableFormulaDecoder GapCVP.FormulaTuringTM
end FormulaCert
namespace FormulaTotalCert
open Turing GapCVP.SourceTotalStructuralDecoder GapCVP.SourceVariableFormulaDecoder
open GapCVP.FormulaTuringTM GapCVP.FormulaCert
end FormulaTotalCert
namespace FormulaSemanticCert
open Turing GapCVP.SourceTotalStructuralDecoder GapCVP.SourceVariableFormulaDecoder
open GapCVP.FormulaTuringTM GapCVP.FormulaCert GapCVP.FormulaTotalCert
end FormulaSemanticCert
namespace CLStructuralNaturalBinaryWriter
open Turing
macro "natural_binary_writer_step_tac" : tactic =>
  `(tactic|
    (simp [structuralNaturalBinaryWriter,
      naturalBinaryWriterConfiguration, naturalBinaryWriterPeek,
      naturalBinaryWriterPop, naturalBinaryWriterPushBit,
      naturalBinaryWriterPushConstant, naturalBinaryWriterGoto,
      naturalBinaryWriterInputStatement,
      naturalBinaryWriterCarryStatement,
      naturalBinaryWriterRestoreStatement,
      naturalBinaryWriterPrepareStatement,
      naturalBinaryWriterOutputStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CLStructuralNaturalBinaryWriter
namespace CLStructuralAtomicNaturalWriter
open GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter
open GapCVP.CLStructuralNaturalBinaryWriter
end CLStructuralAtomicNaturalWriter
namespace CLStructuralWholeCNFOutputTM
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLCellRowBounds GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
end CLStructuralWholeCNFOutputTM
namespace CNFClauseLoop
open Computability Turing
end CNFClauseLoop
namespace CNFSortingDedup
open Computability Turing
end CNFSortingDedup
namespace CNFEncodedClauseSort
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.CNFSortingDedup
macro "delimited_compare_step_tac" : tactic =>
  `(tactic|
    (simp [delimitedPairComparisonMachine,
      delimitedCompareConfiguration,
      delimitedComparePeekFirst, delimitedComparePeekSecond,
      delimitedComparePop, delimitedComparePushFirst,
      delimitedComparePushConstant, delimitedCompareGoto,
      delimitedCompareSetOutcome,
      delimitedCompareFirstPrefixStatement,
      delimitedCompareFirstPayloadStatement,
      delimitedCompareSecondPrefixStatement,
      delimitedCompareSecondPayloadStatement,
      delimitedCompareReverseFirstStatement,
      delimitedCompareReverseSecondStatement,
      delimitedCompareWordsStatement,
      delimitedCompareCleanupStatement,
      delimitedCompareTrailingStatement,
      delimitedCompareOutcomeStatement,
      delimitedCompareSourceStatement,
      delimitedComparePrefixStatement,
      encodedWordOrderingWord,
      encodedWordOrderingFirst, encodedWordOrderingSecond,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CNFEncodedClauseSort
namespace CNFFiniteRecordSort
open Computability Turing GapCVP.ThreeCNFReduction
end CNFFiniteRecordSort
namespace CNFInputDependentRecordSort
open Computability Turing GapCVP.CNFFiniteRecordSort
end CNFInputDependentRecordSort
namespace CNFNaturalOrderComparator
open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFEncodedClauseSort
macro "natural_compare_step_tac" : tactic =>
  `(tactic|
    (simp [delimitedNaturalComparisonMachine,
      naturalCompareConfiguration, delimitedCompareConfiguration,
      naturalCompareWordsStatement, naturalCompareConsumeBoth,
      delimitedComparePeekFirst, delimitedComparePeekSecond,
      delimitedComparePop, delimitedComparePushFirst,
      delimitedComparePushConstant, delimitedCompareGoto,
      delimitedCompareSetOutcome,
      delimitedCompareFirstPrefixStatement,
      delimitedCompareFirstPayloadStatement,
      delimitedCompareSecondPrefixStatement,
      delimitedCompareSecondPayloadStatement,
      delimitedCompareReverseFirstStatement,
      delimitedCompareReverseSecondStatement,
      delimitedCompareCleanupStatement,
      delimitedCompareTrailingStatement,
      delimitedCompareOutcomeStatement,
      delimitedCompareSourceStatement,
      delimitedComparePrefixStatement,
      encodedWordOrderingWord,
      encodedWordOrderingFirst, encodedWordOrderingSecond,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CNFNaturalOrderComparator
namespace CNFNaturalOrderTotalComparator
open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFEncodedClauseSort
open GapCVP.CNFNaturalOrderComparator
end CNFNaturalOrderTotalComparator
namespace CNFNaturalOrderCertifiedComparator
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.CNFSortingDedup GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator
open GapCVP.CNFNaturalOrderTotalComparator
end CNFNaturalOrderCertifiedComparator
namespace CNFPolynomialRowMarkerTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
macro "polynomial_row_marker_step_tac" : tactic =>
  `(tactic|
    (simp [polynomialRowMarkerMachine,
      polynomialRowMarkerConfiguration,
      polynomialRowMarkerPeek, polynomialRowMarkerPop,
      polynomialRowMarkerPushBit,
      polynomialRowMarkerPushConstant,
      polynomialRowMarkerGoto,
      polynomialRowMarkerScanStatement,
      polynomialRowMarkerMultiplyStatement,
      polynomialRowMarkerBaseStatement,
      polynomialRowMarkerRestoreBaseStatement,
      polynomialRowMarkerCoefficientStatement,
      polynomialRowMarkerPayloadStatement,
      polynomialRowMarkerHeaderStatement,
      polynomialRowMarkerSourceStatement,
      polynomialRowMarkerPrefixStatement,
      polynomialRowMarkerPushBits_stepAux,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CNFPolynomialRowMarkerTM
namespace CLStructuralCNFOutputMachinesUnconditional
open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFSortingDedup
open GapCVP.CNFPolynomialRowMarkerTM
end CLStructuralCNFOutputMachinesUnconditional
namespace CNFDependentFiveFamilyRecordTM
open Computability Turing GapCVP.CL GapCVP.CNFClauseLoop
end CNFDependentFiveFamilyRecordTM
namespace OutputPolynomialCompositionClosure
open Turing
end OutputPolynomialCompositionClosure
namespace CNFBoundedRecordFoldTM
open Computability Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFClauseLoop GapCVP.CNFFiniteRecordSort
open GapCVP.CNFPolynomialRowMarkerTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralCNFOutputMachinesUnconditional GapCVP.CNFDependentFiveFamilyRecordTM
end CNFBoundedRecordFoldTM
namespace OutputBoundedDependentRecordFold
open Turing
end OutputBoundedDependentRecordFold
namespace CNFTypedRecordWorkerTM
open Turing GapCVP.CL GapCVP.OutputBoundedDependentRecordFold
end CNFTypedRecordWorkerTM
namespace OutputBoundedDependentRecordFold
open Turing
end OutputBoundedDependentRecordFold
namespace CNFFlatStructuralRecordWorkerTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CNFTypedRecordWorkerTM
macro "flat_literal_record_step_tac" : tactic =>
  `(tactic|
    (simp [actualFlatLiteralRecordWorker,
      flatLiteralRecordConfiguration, flatLiteralRecordPeek,
      flatLiteralRecordPop, flatLiteralRecordPushBit,
      flatLiteralRecordPushConstant, flatLiteralRecordGoto,
      flatLiteralRecordPrefixStatement,
      flatLiteralRecordSignStatement,
      flatLiteralRecordPayloadStatement,
      flatLiteralRecordRestoreStatement,
      flatLiteralRecordMarkerStatement,
      flatLiteralRecordSuffixScanStatement,
      flatLiteralRecordSuffixRestoreStatement,
      flatLiteralRecordInvalidStatement,
      Turing.haltList, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CNFFlatStructuralRecordWorkerTM
namespace CNFFlatSourceOrder
open GapCVP.ThreeCNFReduction GapCVP.CNFEncodedClauseSort
end CNFFlatSourceOrder
namespace CNFFlatWholeWordFoldTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFFiniteRecordSort
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.OutputBoundedDependentRecordFold
end CNFFlatWholeWordFoldTM
namespace CNFFlatSourceOrderPolynomialBounds
open GapCVP.CL GapCVP.CLStructuralCNFVariableBounds GapCVP.CNFFlatSourceOrder
end CNFFlatSourceOrderPolynomialBounds
namespace CNFFlatSourceGridDescriptorTM
open Computability Turing GapCVP.CL GapCVP.ThreeCNFReduction GapCVP.BinaryEncoding
open GapCVP.CLStructuralPrefixWriter GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.SourceMachineCert GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatStructuralRecordWorkerTM
end CNFFlatSourceGridDescriptorTM
namespace CNFUnaryPairIndexTM
open Computability Turing GapCVP.BinaryEncoding
macro "unary_pair_step_tac" : tactic =>
  `(tactic|
    (simp [actualUnaryPairIndexMachine, unaryPairConfiguration,
      unaryPairPeek, unaryPairPop, unaryPairPush, unaryPairGoto,
      unaryPairFirstStatement, unaryPairSecondStatement,
      unaryPairCompareStatement, unaryPairGreaterBaseStatement,
      unaryPairGreaterOffsetStatement, unaryPairLessBaseStatement,
      unaryPairLessOffsetStatement, unaryPairOuterStatement,
      unaryPairSquareCopyStatement, unaryPairSquareRestoreStatement,
      unaryPairSquareCleanupStatement, unaryPairFailureStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CNFUnaryPairIndexTM
namespace CNFUnaryPairIndexTotalCert
open Computability Turing GapCVP.CNFUnaryPairIndexTM
end CNFUnaryPairIndexTotalCert
namespace CNFUnaryPairIndexTotalRuntimeCert
open Computability Turing GapCVP.SourceTotalStructuralDecoder GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalCert
end CNFUnaryPairIndexTotalRuntimeCert
namespace CNFPairedSourceGridDescriptorTM
open Computability Turing GapCVP.ThreeCNFReduction GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.CNFFlatSourceGridDescriptorTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert
end CNFPairedSourceGridDescriptorTM
namespace CNFSourcePairPrefixWorkerTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFUnaryPairIndexTM
macro "source_pair_prefix_step_tac" : tactic =>
  `(tactic|
    (simp [actualSourcePairPrefixMachine,
      sourcePairPrefixConfiguration,
      sourcePairPrefixPeek, sourcePairPrefixPop,
      sourcePairPrefixPush, sourcePairPrefixGoto,
      sourcePairPrefixFirstStatement,
      sourcePairPrefixSecondStatement,
      sourcePairPrefixSuffixStatement,
      sourcePairPrefixSecondRestoreStatement,
      sourcePairPrefixFirstRestoreStatement,
      sourcePairPrefixFailureStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CNFSourcePairPrefixWorkerTM
namespace CNFSourcePairPrefixWorkerTotalCert
open Computability Turing GapCVP.SourceTotalStructuralDecoder GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFSourcePairPrefixWorkerTM
end CNFSourcePairPrefixWorkerTotalCert
namespace SourceLatticeFormulaPreservation
open Turing GapCVP.FormulaTuringTM GapCVP.FormulaTotalCert GapCVP.FormulaSemanticCert
macro "formula_preservation_step_tac" : tactic =>
  `(tactic|
    (simp [formulaPreservationMachine,
      formulaPreservationConfiguration,
      formulaPreservationCopyStatement,
      formulaPreservationRestoreStatement,
      formulaPreservationOutputStatement,
      formulaPreservationPeek,
      formulaPreservationPop, formulaPreservationPush,
      formulaPreservationGoto, Turing.haltList,
      Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux] <;>
     try { congr 2; funext stack; fin_cases stack <;>
       simp [Function.update] } <;>
     try rfl))
end SourceLatticeFormulaPreservation
namespace SourceLatticeDependentSectionComputation
open Turing GapCVP.SourceLatticeFormulaPreservation
macro "source_marker_step_tac" : tactic =>
  `(tactic|
    (simp [sourceMarkerRotationMachine,
      sourceMarkerConfiguration, sourceMarkerPeek,
      sourceMarkerPop, sourceMarkerPush, sourceMarkerGoto,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
     try { congr 2; funext stack; fin_cases stack <;>
       simp [Function.update] } <;>
     try rfl))
end SourceLatticeDependentSectionComputation
namespace SourceLatticeNormalizedSectionSynthesis
open Turing
end SourceLatticeNormalizedSectionSynthesis
namespace SourceLatticeStructuralRadiusNumerator
open Turing
macro "radius_marker_tail_step_tac" : tactic =>
  `(tactic|
    (simp [radiusMarkerTailMachine, radiusMarkerTailConfiguration,
      radiusMarkerTailPeek, radiusMarkerTailPop,
      radiusMarkerTailPush, radiusMarkerTailGoto,
      radiusMarkerTailDropStatement,
      radiusMarkerTailCopyStatement,
      radiusMarkerTailOutputStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end SourceLatticeStructuralRadiusNumerator
namespace SourceLatticeStructuralRationalRadius
open GapCVP.BinaryEncoding
end SourceLatticeStructuralRationalRadius
namespace SourceLatticeStructuralRationalRadiusTM
open Turing GapCVP.SourceLatticeNormalizedSectionSynthesis
macro "rational_radius_step_tac" : tactic =>
  `(tactic|
    (simp [rationalRadiusMachine,
      rationalRadiusConfiguration,
      rationalRadiusFailureStatement,
      normalizedRadiusPeek, normalizedRadiusPop,
      normalizedRadiusPush, normalizedRadiusGoto,
      normalizedRadiusFailureCheck,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end SourceLatticeStructuralRationalRadiusTM
namespace SourceInterpolationRowTM
open GapCVP.BinaryEncoding
end SourceInterpolationRowTM
namespace SourceWholeOutputAssemblyTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceLatticeFormulaPreservation
open GapCVP.SourceLatticeDependentSectionComputation GapCVP.FormulaTotalCert
open GapCVP.OutputBoundedDependentRecordFold
end SourceWholeOutputAssemblyTM
namespace SourceWholeOutputValidBranchRecordTM
open Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputAssemblyTM
macro "source_flat_atomic_step_tac" : tactic =>
  `(tactic|
    (simp [sourceFlatAtomicRecordMachine,
      sourceFlatAtomicConfiguration,
      sourceFlatAtomicPeek, sourceFlatAtomicPop,
      sourceFlatAtomicPushBit, sourceFlatAtomicPushConstant,
      sourceFlatAtomicGoto, sourceFlatAtomicPrefixStatement,
      sourceFlatAtomicPayloadStatement,
      sourceFlatAtomicPayloadOutputStatement,
      sourceFlatAtomicPendingStatement,
      sourceFlatAtomicRestoreStatement,
      sourceFlatAtomicFailureStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end SourceWholeOutputValidBranchRecordTM
namespace SourceCanonicalUnaryGridIndexTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceWholeOutputValidBranchRecordTM
macro "source_grid_index_step_tac" : tactic =>
  `(tactic|
    (simp [sourceCanonicalUnaryGridIndexMachine,
      sourceGridIndexConfiguration,
      sourceGridIndexPeek, sourceGridIndexPop,
      sourceGridIndexPushBit, sourceGridIndexPushConstant,
      sourceGridIndexGoto,
      sourceGridIndexPrefixStatement,
      sourceGridIndexArchiveStatement,
      sourceGridIndexSourceRestoreStatement,
      sourceGridIndexOuterStatement,
      sourceGridIndexCopyStatement,
      sourceGridIndexTemplateRestoreStatement,
      sourceGridIndexFailureStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end SourceCanonicalUnaryGridIndexTM
namespace SourceOriginalSourcePreservingTM
section
open Turing
macro "original_source_preservation_step_tac" : tactic =>
  `(tactic|
    (simp +instances [originalSourcePreservingMachine,
      originalSourceCopyConfiguration,
      originalSourceOutputConfiguration,
      sourcePhaseConfiguration,
      sourceInputSymbols,
      sourceOutputSymbols,
      Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux] <;>
      first
      | rfl
      | (congr 2
         first
         | exact originalSourcePreserving_embedded_haltStacks _ _
         | rw! (castMode := .all)
             [← sourceStacks_update_worker,
             ← originalSourcePreservingStacks_update_backup,
             ← sourceStacks_update_scratch,
             originalSourcePreserving_initialStacks_update]
         | rw! (castMode := .all)
             [← sourceStacks_update_worker,
             originalSourcePreserving_initialStacks_update]
         | rw! (castMode := .all)
             [← sourceStacks_update_scratch,
             ← sourceStacks_update_worker,
             originalSourcePreserving_initialStacks_update]
         | rw! (castMode := .all)
             [← sourceStacks_update_scratch]
         | rw! (castMode := .all)
             [← sourceStacks_update_worker,
             ← sourceStacks_update_result,
             originalSourcePreserving_haltStacks_update]
         | rw! (castMode := .all)
             [← sourceStacks_update_worker,
             originalSourcePreserving_haltStacks_update]
         | rw! (castMode := .all)
             [← originalSourcePreservingStacks_update_backup,
             ← sourceStacks_update_worker,
             originalSourcePreserving_haltStacks_update]
         | rw! (castMode := .all)
             [← sourceStacks_update_result,
             ← sourceStacks_update_worker,
             originalSourcePreserving_haltStacks_update]
         | rw! (castMode := .all)
             [← sourceStacks_update_result,
             originalSourcePreserving_embedded_haltStacks])))
end
end SourceOriginalSourcePreservingTM
namespace CNFGuardedSourceDescriptorRotationBoundedFoldTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
end CNFGuardedSourceDescriptorRotationBoundedFoldTM
namespace CNFFlatAdjacentRecordSwapTM
open Turing GapCVP.BinaryEncoding GapCVP.CNFGuardedSourceDescriptorRotationBoundedFoldTM
macro "flat_adjacent_record_step_tac" : tactic =>
  `(tactic|
    (simp [actualFlatAdjacentRecordSwapMachine,
      flatAdjacentRecordConfiguration,
      flatAdjacentRecordPeek, flatAdjacentRecordPop,
      flatAdjacentRecordPushBit, flatAdjacentRecordPushConstant,
      flatAdjacentRecordGoto,
      flatAdjacentRecordFirstPrefixStatement,
      flatAdjacentRecordFirstPayloadStatement,
      flatAdjacentRecordSecondPrefixStatement,
      flatAdjacentRecordSecondPayloadStatement,
      flatAdjacentRecordRestoreFirstStatement,
      flatAdjacentRecordRestoreSecondStatement,
      flatAdjacentRecordFailureStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CNFFlatAdjacentRecordSwapTM
namespace CNFFlatAdjacentRecordSwapTotalCert
open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFFlatAdjacentRecordSwapTM
end CNFFlatAdjacentRecordSwapTotalCert
namespace CNFFlatPhysicalBinaryAppendTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceWholeOutputValidBranchRecordTM GapCVP.CNFFlatAdjacentRecordSwapTotalCert
end CNFFlatPhysicalBinaryAppendTM
namespace CNFCappedUnaryMinimumTM
open Turing GapCVP.BinaryEncoding GapCVP.CNFUnaryPairIndexTM
macro "capped_unary_minimum_step_tac" : tactic =>
  `(tactic|
    (simp [actualCappedUnaryMinimumMachine,
      cappedUnaryMinimumConfiguration,
      cappedUnaryMinimumPeek,
      cappedUnaryMinimumPop,
      cappedUnaryMinimumPush,
      cappedUnaryMinimumGoto,
      cappedUnaryMinimumFirstStatement,
      cappedUnaryMinimumSecondStatement,
      cappedUnaryMinimumSuccessStatement,
      cappedUnaryMinimumFailureStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end CNFCappedUnaryMinimumTM
namespace CNFCappedUnaryMinimumTotalCert
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFCappedUnaryMinimumTM
end CNFCappedUnaryMinimumTotalCert
namespace CNFCappedUnaryPairArithmeticTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceMachineCert GapCVP.SourceOriginalSourcePreservingTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFSourcePairPrefixWorkerTM
open GapCVP.CNFSourcePairPrefixWorkerTotalCert GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedUnaryMinimumTotalCert
end CNFCappedUnaryPairArithmeticTM
namespace CNFCappedFlatSourceListFoldTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceUniformTuringTM GapCVP.CNFUnaryPairIndexTM GapCVP.CNFSourcePairPrefixWorkerTM
open GapCVP.CNFSourcePairPrefixWorkerTotalCert GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedUnaryMinimumTotalCert GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end CNFCappedFlatSourceListFoldTM
namespace CNFCappedFlatSourceListFoldTotalCert
open Computability Turing GapCVP.BinaryEncoding GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFTypedRecordWorkerTM GapCVP.CNFUnaryPairIndexTM GapCVP.CNFSourcePairPrefixWorkerTM
open GapCVP.CNFCappedUnaryMinimumTM GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFFlatSourceOrder GapCVP.CNFCappedFlatSourceListFoldTM
open GapCVP.CNFGuardedSourceDescriptorRotationBoundedFoldTM
end CNFCappedFlatSourceListFoldTotalCert
namespace CNFFiveFamilyFlatCandidateGenerationTM
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds GapCVP.BinaryEncoding
open GapCVP.ThreeCNFReduction GapCVP.SourceMachineCert GapCVP.SourceUniformTuringTM
open GapCVP.CLStructuralCNFVariableBounds GapCVP.CLStructuralWholeCNFOutputTM
open GapCVP.CNFFlatSourceOrder GapCVP.CNFFlatSourceOrderPolynomialBounds
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFUnaryPairIndexTotalRuntimeCert
open GapCVP.CNFCappedFlatSourceListFoldTM
end CNFFiveFamilyFlatCandidateGenerationTM
namespace CNFCappedFlatSourceListComparatorTM
open Computability Turing GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralNaturalBinaryWriter GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedUnaryMinimumTotalCert GapCVP.CNFFlatSourceOrder
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListFoldTotalCert
end CNFCappedFlatSourceListComparatorTM
namespace SourceCanonicalFixedWordTuringTM
open Turing GapCVP.SourceMachineCert
end SourceCanonicalFixedWordTuringTM
namespace CNFAnnotatedSourceClausePairPreparationTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFCappedUnaryMinimumTM GapCVP.CNFCappedUnaryMinimumTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end CNFAnnotatedSourceClausePairPreparationTM
namespace CNFFlatAdjacentConditionalSwapTM
open Turing GapCVP.OutputPolynomialCompositionClosure GapCVP.CNFFlatAdjacentRecordSwapTM
open GapCVP.CNFFlatAdjacentRecordSwapTotalCert
end CNFFlatAdjacentConditionalSwapTM
namespace CNFGuardedFiveFamilyTagDispatchTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.CNFEncodedClauseSort
end CNFGuardedFiveFamilyTagDispatchTM
namespace CNFFlatCappedComparisonControlledSwapTM
open Turing GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CNFFlatAdjacentRecordSwapTM
open GapCVP.CNFFlatAdjacentConditionalSwapTM
end CNFFlatCappedComparisonControlledSwapTM
namespace CNFAnnotatedSourceClauseBubblePassTM
open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFGuardedSourceDescriptorRotationBoundedFoldTM
open GapCVP.CNFTypedRecordWorkerTM GapCVP.CNFFlatAdjacentRecordSwapTM
open GapCVP.CNFFlatCappedComparisonControlledSwapTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
end CNFAnnotatedSourceClauseBubblePassTM
namespace SourceUnaryIntegerMultiplicationTM
section
open Turing GapCVP.BinaryEncoding
macro "source_integer_multiplication_step_tac" : tactic =>
  `(tactic|
    (simp [sourceUnaryIntegerMultiplicationMachine,
      sourceIntegerMultiplicationConfiguration,
      sourceIntegerMultiplicationPeek,
      sourceIntegerMultiplicationPop,
      sourceIntegerMultiplicationPush,
      sourceIntegerMultiplicationGoto,
      sourceIntegerMultiplicationLeftStatement,
      sourceIntegerMultiplicationRightStatement,
      sourceIntegerMultiplicationOuterStatement,
      sourceIntegerMultiplicationCopyStatement,
      sourceIntegerMultiplicationRestoreStatement,
      sourceIntegerMultiplicationSuccessCleanupStatement,
      sourceIntegerMultiplicationFailureInputStatement,
      sourceIntegerMultiplicationFailureLeftStatement,
      sourceIntegerMultiplicationFailureRightStatement,
      sourceIntegerMultiplicationFailureRestoreStatement,
      sourceIntegerMultiplicationFailureOutputStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
     try { congr 2; funext stack; fin_cases stack <;>
       simp [Function.update] } <;>
     try rfl))
end
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
end
end SourceUnaryIntegerMultiplicationTM
namespace SourceMixedRadixPreservedFourFamilyRecordTM
open Turing GapCVP.BinaryEncoding
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.CLStructuralPrefixWriter
end SourceMixedRadixPreservedFourFamilyRecordTM
namespace SourceMixedRadixUnaryQuotientRemainderTM
section
open Turing
macro "source_unary_division_step_tac" : tactic =>
  `(tactic|
    (simp [sourceUnaryDivisionMachine,
      sourceUnaryDivisionConfiguration,
      sourceUnaryDivisionControl,
      sourceUnaryDivisionPeek, sourceUnaryDivisionPop,
      sourceUnaryDivisionGoto,
      sourceUnaryDivisionDividendStatement,
      sourceUnaryDivisionModulusStatement,
      sourceUnaryDivisionArchiveSuffixStatement,
      sourceUnaryDivisionRestoreSourceStatement,
      sourceUnaryDivisionDispatchStatement,
      sourceUnaryDivisionMatchStatement,
      sourceUnaryDivisionRestoreModulusStatement,
      sourceUnaryDivisionEmitRemainderStatement,
      sourceUnaryDivisionEmitQuotientStatement,
      sourceUnaryDivisionCleanupModulusStatement,
      sourceUnaryDivisionCleanupScratchStatement,
      sourceUnaryDivisionCleanupDividendStatement,
      sourceUnaryDivisionCleanupPartialStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end
section
open Turing GapCVP.BinaryEncoding
end
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceInterpolationRowTM
end
end SourceMixedRadixUnaryQuotientRemainderTM
namespace SourceMixedRadixDimensionRowMajorIndexTM
open Turing GapCVP.SourceStructuralTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
end SourceMixedRadixDimensionRowMajorIndexTM
namespace SourceMixedRadixOriginalSourceDescriptorRotationTM
open Turing GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder
end SourceMixedRadixOriginalSourceDescriptorRotationTM
namespace SourceMixedRadixPolynomialPaddedDescriptorFoldTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceTotalStructuralDecoder GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceWholeOutputAssemblyTM
end SourceMixedRadixPolynomialPaddedDescriptorFoldTM
namespace SourceIndexedClauseLookupTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixDimensionRowMajorIndexTM
open GapCVP.SourceMixedRadixPolynomialPaddedDescriptorFoldTM
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFFlatPhysicalBinaryAppendTM
end SourceIndexedClauseLookupTM
namespace SourceIndexedClauseSignTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceIndexedClauseLookupTM
end SourceIndexedClauseSignTM
namespace SourceAnchoredGridRecordFoldTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixPolynomialPaddedDescriptorFoldTM
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator
open GapCVP.CNFNaturalOrderCertifiedComparator GapCVP.CNFGuardedFiveFamilyTagDispatchTM
open GapCVP.CNFFlatAdjacentRecordSwapTM GapCVP.CNFFlatAdjacentRecordSwapTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end SourceAnchoredGridRecordFoldTM
namespace CNFFiveFamilyFlatIndexedCatalogueTM
open Computability Turing GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
end CNFFiveFamilyFlatIndexedCatalogueTM
namespace CNFFiveFamilyFlatIndexedRankArithmeticTM
open Computability Turing GapCVP.CLNondeterminism GapCVP.CLCellRowBounds GapCVP.BinaryEncoding
open GapCVP.SourceMachineCert GapCVP.SourceUniformTuringTM GapCVP.SourceStructuralTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
end CNFFiveFamilyFlatIndexedRankArithmeticTM
namespace CNFFiveFamilyFlatRowMajorCatalogueTM
open Computability Turing GapCVP.CL GapCVP.CNFDependentFiveFamilyRecordTM
open GapCVP.CNFBoundedRecordFoldTM
end CNFFiveFamilyFlatRowMajorCatalogueTM
namespace CNFFiveFamilyOriginalIndexedBitTM
open Computability Turing GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end CNFFiveFamilyOriginalIndexedBitTM
namespace CNFFiveFamilyFlatSortedLiteralFamilies
open GapCVP.CL GapCVP.ThreeCNFReduction GapCVP.CNFFiniteRecordSort
open GapCVP.CNFInputDependentRecordSort
end CNFFiveFamilyFlatSortedLiteralFamilies
namespace CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatSourceOrder GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.CNFFlatSourceGridDescriptorTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyFlatSortedLiteralFamilies
end CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
namespace CNFFiveFamilyFlatAcceptanceVariableTM
open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceUniformTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
end CNFFiveFamilyFlatAcceptanceVariableTM
namespace CNFFiveFamilyFlatAcceptanceClauseFoldTM
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLCellRowBounds GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.SourceMachineCert GapCVP.SourceUniformTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceCanonicalUnaryGridIndexTM GapCVP.SourceAnchoredGridRecordFoldTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatSourceOrder
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM GapCVP.CNFTypedRecordWorkerTM
open GapCVP.CNFFiveFamilyFlatSortedLiteralFamilies GapCVP.CNFFiveFamilyFlatAcceptanceVariableTM
end CNFFiveFamilyFlatAcceptanceClauseFoldTM
namespace CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM
open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction GapCVP.SourceUniformTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatSourceOrder
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyFlatSortedLiteralFamilies
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM
end CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM
namespace SourceFourFamilyMarkerRotationTM
open Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceMixedRadixPreservedFourFamilyRecordTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
end SourceFourFamilyMarkerRotationTM
namespace SourceFourFamilyBooleanPredicateTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.CNFEncodedClauseSort
open GapCVP.CNFNaturalOrderComparator GapCVP.CNFNaturalOrderTotalComparator
open GapCVP.CNFNaturalOrderCertifiedComparator GapCVP.CNFGuardedFiveFamilyTagDispatchTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end SourceFourFamilyBooleanPredicateTM
namespace SourceFourFamilyInterpolationMembershipPredicateTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceUnaryIntegerMultiplicationTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
end SourceFourFamilyInterpolationMembershipPredicateTM
namespace SourceFourFamilyDiagonalMembershipPredicateTM
open Turing GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
end SourceFourFamilyDiagonalMembershipPredicateTM
namespace CNFFiveFamilyPackedInitialOffsetFeatureTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM
end CNFFiveFamilyPackedInitialOffsetFeatureTM
namespace CNFFiveFamilyPackedInitialCellDecoderTM
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates GapCVP.CLCellRows
open GapCVP.CLLocalWindows GapCVP.CLCellRowBounds GapCVP.CLFullTableauEmitter
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding
open GapCVP.SourceUniformTuringTM GapCVP.SourceMachineCert
open GapCVP.OutputPolynomialCompositionClosure GapCVP.CLEmittedCNFTM GapCVP.CLWindowTruthTable
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM
open GapCVP.CNFFiveFamilyPackedInitialOffsetFeatureTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM
end CNFFiveFamilyPackedInitialCellDecoderTM
namespace CNFFiveFamilyForbiddenWindowCoordinateTM
open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM GapCVP.SourceMachineCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFUnaryPairIndexTotalRuntimeCert
open GapCVP.CNFCappedUnaryMinimumTM GapCVP.CNFCappedUnaryMinimumTotalCert
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
end CNFFiveFamilyForbiddenWindowCoordinateTM
namespace CNFAnnotatedSourceClausePairZipTM
open Turing GapCVP.CNFSourcePairPrefixWorkerTM GapCVP.CNFSourcePairPrefixWorkerTotalCert
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
end CNFAnnotatedSourceClausePairZipTM
namespace CNFAnnotatedSourceCountedClausePairZipTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFSourcePairPrefixWorkerTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListFoldTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFTypedRecordWorkerTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM GapCVP.CNFAnnotatedSourceClausePairZipTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM
end CNFAnnotatedSourceCountedClausePairZipTM
namespace CNFAnnotatedSourceUnaryTailReversalTM
open Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceTotalStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFSourcePairPrefixWorkerTM GapCVP.CNFSourcePairPrefixWorkerTotalCert
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListFoldTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFTypedRecordWorkerTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
end CNFAnnotatedSourceUnaryTailReversalTM
namespace CNFAnnotatedSourceCountedResidualTailTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFUnaryPairIndexTM GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFFlatSourceOrder
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListComparatorTM
open GapCVP.CNFSourcePairPrefixWorkerTM GapCVP.CNFSourcePairPrefixWorkerTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceCountedClausePairZipTM
open GapCVP.CNFAnnotatedSourceUnaryTailReversalTM
end CNFAnnotatedSourceCountedResidualTailTM
namespace SourceFourFamilyTaggedPredicateDispatchTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CNFFlatPhysicalBinaryAppendTM
end SourceFourFamilyTaggedPredicateDispatchTM
namespace CNFAnnotatedSourceSquareMajorResolutionTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator
open GapCVP.CNFNaturalOrderCertifiedComparator GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListFoldTotalCert
open GapCVP.CNFFlatSourceOrder GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClausePairZipTM GapCVP.CNFTypedRecordWorkerTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM
end CNFAnnotatedSourceSquareMajorResolutionTM
namespace CNFAnnotatedSourceCompleteFiniteSetComparatorTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator
open GapCVP.CNFNaturalOrderCertifiedComparator GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM GapCVP.CNFAnnotatedSourceClausePairZipTM
open GapCVP.CNFAnnotatedSourceCountedClausePairZipTM
open GapCVP.CNFAnnotatedSourceCountedResidualTailTM
open GapCVP.CNFAnnotatedSourceSquareMajorResolutionTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM
end CNFAnnotatedSourceCompleteFiniteSetComparatorTM
namespace CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert
open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFEncodedClauseSort
open GapCVP.CNFNaturalOrderComparator GapCVP.CNFFlatSourceOrder
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFlatCappedComparisonControlledSwapTM
open GapCVP.CNFSourcePairPrefixWorkerTM GapCVP.CNFCappedFlatSourceListFoldTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM GapCVP.CNFAnnotatedSourceClausePairZipTM
open GapCVP.CNFAnnotatedSourceCountedClausePairZipTM
open GapCVP.CNFAnnotatedSourceCountedResidualTailTM
open GapCVP.CNFAnnotatedSourceSquareMajorResolutionTM
open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM
end CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert
namespace CNFFiveFamilyForbiddenWholeClauseWorkerTM
open Computability Turing GapCVP.CL GapCVP.ThreeCNFReduction
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CNFFiveFamilyFlatSortedLiteralFamilies
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
end CNFFiveFamilyForbiddenWholeClauseWorkerTM
namespace CNFFiveFamilyForbiddenWholeClauseSourceCert
open Computability Turing GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM
end CNFFiveFamilyForbiddenWholeClauseSourceCert
namespace CNFFiveFamilyForbiddenWholeClauseExactSourceTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert
end CNFFiveFamilyForbiddenWholeClauseExactSourceTM
namespace CNFFiveFamilyIndependentAnchoredFamilyStreamTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceUniformTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceCanonicalUnaryGridIndexTM
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM
end CNFFiveFamilyIndependentAnchoredFamilyStreamTM
namespace CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding
open GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM
open GapCVP.CNFFiveFamilyIndependentAnchoredFamilyStreamTM
end CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM
namespace CNFFiveFamilyForbiddenWindowGateSourceValidity
open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert
open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM
section
variable (bound : Polynomial ℕ)
variable {verifier : List Bool × List Bool → Bool}
variable (machine : VerifierTM verifier)
variable (original suffix : List Bool)
variable (window : Window (rowWidth bound machine original))
variable (symbols : WindowSymbols (completePhaseSymbolCount machine.tm))
end
end CNFFiveFamilyForbiddenWindowGateSourceValidity
namespace CNFFiveFamilyForbiddenWholeClauseValidity
open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction GapCVP.CNFFlatSourceOrder
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert
open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM
open GapCVP.CNFFiveFamilyForbiddenWindowGateSourceValidity
end CNFFiveFamilyForbiddenWholeClauseValidity
namespace CNFFiveFamilyIndependentFiveFamilyCatalogueSourceValidity
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseValidity
open GapCVP.CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM
end CNFFiveFamilyIndependentFiveFamilyCatalogueSourceValidity
namespace CNFAnnotatedSourceCompleteBubbleSortTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFTypedRecordWorkerTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert
end CNFAnnotatedSourceCompleteBubbleSortTM
namespace CNFAnnotatedSourceCompleteBubbleSortSourceCert
open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert
open GapCVP.CNFAnnotatedSourceCompleteBubbleSortTM
end CNFAnnotatedSourceCompleteBubbleSortSourceCert
namespace CNFAnnotatedSourceCompleteSortedDedupTM
open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFEncodedClauseSort GapCVP.CNFFlatSourceOrder GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFTypedRecordWorkerTM GapCVP.CNFGuardedFiveFamilyTagDispatchTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.SourceFourFamilyTaggedPredicateDispatchTM
end CNFAnnotatedSourceCompleteSortedDedupTM
namespace CNFAnnotatedSourceCompleteSortedDedupSourceCert
open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFiniteRecordSort
open GapCVP.CNFInputDependentRecordSort GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.CNFAnnotatedSourceCompleteBubbleSortTM
open GapCVP.CNFAnnotatedSourceCompleteBubbleSortSourceCert
open GapCVP.CNFAnnotatedSourceCompleteSortedDedupTM
end CNFAnnotatedSourceCompleteSortedDedupSourceCert
namespace CNFFiveFamilyIndependentFiveFamilyPhysicalBundledSourceCert
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding
open GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFFiniteRecordSort
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFAnnotatedSourceCompleteBubbleSortTM
open GapCVP.CNFAnnotatedSourceCompleteSortedDedupSourceCert
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatAcceptanceVariableTM GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM
open GapCVP.CNFFiveFamilyIndependentAnchoredFamilyStreamTM
open GapCVP.CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM
open GapCVP.CNFFiveFamilyIndependentFiveFamilyCatalogueSourceValidity
end CNFFiveFamilyIndependentFiveFamilyPhysicalBundledSourceCert
namespace CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceUniformTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.CNFFlatSourceGridDescriptorTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFPairedSourceGridDescriptorTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
end CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM
namespace CNFGuardedSourceDescriptorCompositeFoldTM
open Computability Turing GapCVP.CLVerifier GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CNFFlatStructuralRecordWorkerTM
end CNFGuardedSourceDescriptorCompositeFoldTM
namespace CNFFiveFamilySourceIndexedORGadgetFoldCoreTM
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM
end CNFFiveFamilySourceIndexedORGadgetFoldCoreTM
namespace CNFFiveFamilySourceIndexedORGadgetRecordWorkerBoundCert
open Computability Turing GapCVP.CLVerifier GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.SourceTotalStructuralDecoder GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFPairedSourceGridDescriptorTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFGuardedSourceDescriptorCompositeFoldTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM
end CNFFiveFamilySourceIndexedORGadgetRecordWorkerBoundCert
namespace CNFFiveFamilySourceIndexedORGadgetFoldBoundCert
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CNFTypedRecordWorkerTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetRecordWorkerBoundCert
open GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldCoreTM
end CNFFiveFamilySourceIndexedORGadgetFoldBoundCert
namespace CNFFiveFamilySourceIndexedORGadgetSourceIterationBudgetCert
open Computability Turing GapCVP.CL GapCVP.BinaryEncoding
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldCoreTM
end CNFFiveFamilySourceIndexedORGadgetSourceIterationBudgetCert
namespace CNFFiveFamilySourceIndexedGadgetDescriptorExpansionTM
open Computability Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.CNFFlatWholeWordFoldTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.CNFAnnotatedSourceCompleteSortedDedupTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldCoreTM
open GapCVP.CNFFiveFamilySourceIndexedORGadgetFoldBoundCert
open GapCVP.CNFFiveFamilySourceIndexedORGadgetSourceIterationBudgetCert
end CNFFiveFamilySourceIndexedGadgetDescriptorExpansionTM
namespace CNFFiveFamilySourceIndexedORGadgetFinalCert
open Computability Turing GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatWholeWordFoldTM
open GapCVP.CNFFiveFamilyIndependentFiveFamilyPhysicalBundledSourceCert
open GapCVP.CNFFiveFamilySourceIndexedGadgetDescriptorExpansionTM
end CNFFiveFamilySourceIndexedORGadgetFinalCert
section
end
namespace Factor400BinaryCanonicalNo
end Factor400BinaryCanonicalNo
namespace Core
end Core
namespace Factor400FormulaBridge
open GapCVP.SourceMachineCert
end Factor400FormulaBridge
namespace BinarySourceVariableCompaction
open GapCVP.SourceMachineCert
end BinarySourceVariableCompaction
namespace Core.EffectiveBinaryGaussian
open scoped BigOperators
open Matrix
end Core.EffectiveBinaryGaussian
namespace Core.EffectiveBinaryField
open scoped BigOperators
open Polynomial
end Core.EffectiveBinaryField
namespace BinaryFieldBasis
open Polynomial GapCVP.Core GapCVP.Core.EffectiveBinaryField
attribute [local instance] Classical.propDecidable
end BinaryFieldBasis
namespace Core
section
open Matrix
variable {K : Type*} [Field K] [Algebra (ZMod 2) K]
variable {e m n : ℕ}
end
section
open Matrix
variable {ι K : Type*} [Field K] [Algebra (ZMod 2) K]
variable {e n : ℕ}
end
section
open Matrix Finset
end
section
open Finset Polynomial
open scoped symmDiff
end
section
open scoped BigOperators
open Finset Matrix Polynomial
variable {K : Type*} [Field K]
end
section
open scoped BigOperators
end
section
open scoped BigOperators
open Finset Matrix Polynomial
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end
end Core
namespace Factor400BinaryConstructiveSourcePlaces
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryFieldBasis
end Factor400BinaryConstructiveSourcePlaces
namespace BinarySourceCoordinateOrder
open GapCVP.Core GapCVP.BinaryFieldBasis GapCVP.Factor400BinaryConstructiveSourcePlaces
attribute [local instance] Classical.propDecidable
end BinarySourceCoordinateOrder
namespace BinaryReedSolomonParity
open Polynomial Matrix
variable {K : Type*} [Field K]
end BinaryReedSolomonParity
namespace Core
section
open Polynomial IsDedekindDomain
variable {K E : Type*} [Field K] [Field E]
section
variable [Algebra (RatFunc K) E] [Algebra K[X] E]
variable [IsScalarTower K[X] (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]
variable [Algebra.IsSeparable (RatFunc K) E]
end
end
section
open Finset
end
section
open Finset Matrix Polynomial
end
section
open scoped BigOperators
open Matrix Finset Polynomial
variable {K : Type*} [Field K]
end
section
open scoped BigOperators
open Polynomial Matrix Finset
variable {K : Type*} [Field K]
end
section
open Finset Polynomial
end
section
open scoped BigOperators
open Polynomial Matrix Finset
variable {K : Type*} [Field K]
end
section
open Polynomial IsDedekindDomain
variable {K E : Type*} [Field K] [Field E]
variable [Algebra (RatFunc K) E] [Algebra K[X] E]
variable [IsScalarTower K[X] (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]
variable [Algebra.IsSeparable (RatFunc K) E]
end
section
open scoped BigOperators
open Finset Polynomial
variable {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K]
end
section
open Finset Polynomial
end
section
open scoped BigOperators
variable {E Γ₀ : Type*} [Field E] [LinearOrderedCommMonoidWithZero Γ₀]
end
section
open scoped BigOperators
open Finset Polynomial
end
section
open scoped BigOperators symmDiff
open Polynomial Finset
end
section
open scoped BigOperators
open Polynomial Finset
variable {K E : Type*} [Field K] [Field E]
variable [Algebra (RatFunc K) E] [Algebra K[X] E]
variable [IsScalarTower K[X] (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]
variable [Algebra.IsSeparable (RatFunc K) E]
end
section
open scoped BigOperators
open Polynomial Finset Matrix
end
section
variable {E Γ₀ : Type*} [Field E] [LinearOrderedCommMonoidWithZero Γ₀]
end
section
open scoped BigOperators
open Polynomial Finset Matrix
end
section
open scoped BigOperators
open Matrix
namespace EffectiveBinaryGaussian
end EffectiveBinaryGaussian
end
end Core
namespace Factor400BinarySourceTM
open GapCVP.OutputBoundedDependentRecordFold
end Factor400BinarySourceTM
namespace Factor400BinaryPreservingXorWorker
open Turing
macro "preserving_xor_step_tac" : tactic =>
  `(tactic|
    (simp [preservingXorMachine, preservingXorConfiguration,
      preservingXorPeek, preservingXorGoto,
      preservingXorFirstStatement, preservingXorSecondStatement,
      preservingXorScanStatement, preservingXorRestoreStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end Factor400BinaryPreservingXorWorker
namespace Factor400BinaryPhysicalParityTM
open GapCVP.OutputBoundedDependentRecordFold
open GapCVP.Factor400BinarySourceTM GapCVP.Factor400BinaryPreservingXorWorker
end Factor400BinaryPhysicalParityTM
namespace BinaryCoefficientTM
open Turing GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.Factor400BinaryPhysicalParityTM
end BinaryCoefficientTM
namespace GaussianXorWorker
open Turing
macro "binary_gaussian_xor_step_tac" : tactic =>
  `(tactic|
    (simp [binaryGaussianXorMachine, binaryGaussianXorConfiguration,
      binaryGaussianXorPeek, binaryGaussianXorGoto,
      binaryGaussianXorFirstStatement,
      binaryGaussianXorSecondStatement,
      binaryGaussianXorDrainStatement, Turing.haltList,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end GaussianXorWorker
namespace GaussianRowWorker
open Turing GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceCanonicalFixedWordTuringTM
end GaussianRowWorker
namespace BinaryModularReductionTM
open Turing GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.GaussianXorWorker GapCVP.GaussianRowWorker
end BinaryModularReductionTM
namespace BinaryExplicitAffineSystem
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.BinaryReedSolomonParity
end BinaryExplicitAffineSystem
namespace BinarySourceRowOrder
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryExplicitAffineSystem
attribute [local instance] Classical.propDecidable
end BinarySourceRowOrder
namespace BinaryOrderedAssembly
open GapCVP.Core
variable {ι K : Type*} [Field K] [Algebra (ZMod 2) K]
variable {degree dimension rowCount : ℕ}
end BinaryOrderedAssembly
namespace BinaryOrderedRefinement
open GapCVP.Core GapCVP.BinaryExplicitAffineSystem GapCVP.BinarySourceRowOrder
end BinaryOrderedRefinement
namespace BinaryExplicitFourFamilyKernel
open GapCVP.Core GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryReedSolomonParity
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K]
end BinaryExplicitFourFamilyKernel
namespace Factor400BinaryConstructiveSourcePlaces
section
open GapCVP.Core
open scoped BigOperators
open Finset Polynomial
end
section
open GapCVP.Core Finset Polynomial
end
section
open GapCVP.Core
export GapCVP.Core
  (genericMomentSupportPolynomial_natDegree
   rootSupportPolynomial_finiteSupportRoots
   exists_injective_roots_of_monic_separable_splits
   mem_enumeratedRootSupport_iff
   sourceParitySupport_card_le
   genericRoot_mem_subtype_of_characteristicTwo_moments)
open scoped BigOperators symmDiff
open Polynomial Finset
end
section
open GapCVP.Core
export GapCVP.Core
  (functionFieldExtendedValuation_ratFunc_eq_place_zpow
   discrete_place_root_term_valuations_ne
   valuation_finset_sum_ne_zero_of_distinct
   functionFieldExtendedValuation_monic_root_separation
   normalizedAffineRootPolynomial
   normalizedAffineRootPolynomial_monic
   normalizedAffineRootPolynomial_natDegree
   normalizedAffineRootPolynomial_eval₂_eq_zero
   valuation_highPower_separation_of_place_inverse_le)
open scoped BigOperators
open Polynomial Finset
variable {K E : Type*} [Field K] [Field E]
variable [Algebra (RatFunc K) E] [Algebra K[X] E]
variable [IsScalarTower K[X] (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]
variable [Algebra.IsSeparable (RatFunc K) E]
end
section
open GapCVP.Core
end
section
open GapCVP.Core
open scoped BigOperators
open Polynomial Finset
end
end Factor400BinaryConstructiveSourcePlaces
namespace SourceFactor400BinaryConstructionABounds
open scoped BigOperators
end SourceFactor400BinaryConstructionABounds
namespace Factor400BinaryConstructiveSourcePlaces
section
open GapCVP.Core GapCVP.SourceFactor400BinaryConstructionABounds
end
section
open GapCVP.Core
open scoped BigOperators
open Polynomial Finset Matrix
end
section
open GapCVP.Core
end
section
open GapCVP.Core Polynomial
end
end Factor400BinaryConstructiveSourcePlaces
namespace BinaryExplicitSourceSoundness
open GapCVP.Core
end BinaryExplicitSourceSoundness
namespace Factor400BinaryInstanceBridge
end Factor400BinaryInstanceBridge
namespace Factor400BinaryEffectiveBasisSerializerTM
open Turing GapCVP.BinaryEncoding GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceWholeOutputValidBranchRecordTM GapCVP.CNFFlatPhysicalBinaryAppendTM
end Factor400BinaryEffectiveBasisSerializerTM
namespace SourceAnchoredQaryGridCandidateCatalogueTM
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
end
section
open Turing
end
end SourceAnchoredQaryGridCandidateCatalogueTM
namespace SourceMixedRadixMaskSelectedFlatPreparationTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceAnchoredQaryGridCandidateCatalogueTM GapCVP.SourceAnchoredGridRecordFoldTM
open GapCVP.SourceCanonicalUnaryGridIndexTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFPolynomialRowMarkerTM GapCVP.CLStructuralCNFOutputMachinesUnconditional
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end SourceMixedRadixMaskSelectedFlatPreparationTM
namespace BinaryStructuralRecordTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.Factor400BinaryEffectiveBasisSerializerTM
end BinaryStructuralRecordTM
namespace Core
section
open scoped BigOperators
open Matrix
namespace EffectiveBinaryGaussian
end EffectiveBinaryGaussian
end
end Core
namespace Factor400BinaryPhysicalWorkers
open Turing GapCVP.SourceWholeOutputAssemblyTM GapCVP.CNFGuardedFiveFamilyTagDispatchTM
end Factor400BinaryPhysicalWorkers
namespace BinaryDimensionTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceVariableFormulaDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.Factor400BinarySourceTM
end BinaryDimensionTM
namespace SourceMixedRadixMaskSelectedSquareBasisIdentityAtomTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CNFEncodedClauseSort GapCVP.CNFGuardedFiveFamilyTagDispatchTM
end SourceMixedRadixMaskSelectedSquareBasisIdentityAtomTM
namespace SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedSquareBasisIdentityAtomTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
end SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
namespace SourceMixedRadixMaskSelectedRankTaggedLowerLeftSourceTM
open Turing GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM
end SourceMixedRadixMaskSelectedRankTaggedLowerLeftSourceTM
namespace SourceNormalizedVariableRankScanTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.FormulaSemanticCert
open GapCVP.SourceTotalStructuralDecoder GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceVariableFormulaDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedLowerLeftSourceTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFGuardedFiveFamilyTagDispatchTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end SourceNormalizedVariableRankScanTM
namespace BinaryCompactSourceFirstOccurrenceTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceNormalizedVariableRankScanTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedLowerLeftSourceTM
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryDimensionTM
end BinaryCompactSourceFirstOccurrenceTM
namespace BinaryCompactRankPrefixIdentity
open GapCVP.SourceMachineCert GapCVP.BinarySourceVariableCompaction
end BinaryCompactRankPrefixIdentity
namespace BinaryCompactSourceFirstOccurrenceTM
open GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceVariableCompaction GapCVP.BinaryCompactRankPrefixIdentity
end BinaryCompactSourceFirstOccurrenceTM
namespace BinaryExplicitAffineRows
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.GaussianXorWorker
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end BinaryExplicitAffineRows
namespace BinaryPhysicalWordRuntimeDegreeTM
open Turing GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.BinaryExplicitAffineRows
end BinaryPhysicalWordRuntimeDegreeTM
namespace BinaryPhysicalCellGridWordTM
open Turing GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM
end BinaryPhysicalCellGridWordTM
namespace BinaryRadiusTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CLStructuralAtomicNaturalWriter
open GapCVP.SourceLatticeStructuralRadiusNumerator GapCVP.SourceLatticeStructuralRationalRadius
open GapCVP.SourceLatticeStructuralRationalRadiusTM
end BinaryRadiusTM
namespace GaussianPivotScheduleTM
open Turing
macro "binary_gaussian_pivot_step_tac" : tactic =>
  `(tactic|
    (simp [binaryGaussianPivotMachine, pivotConfiguration,
      pivotPeek, pivotGoto, pivotScanStatement,
      pivotSuccessDrainStatement, pivotFailureStatement,
      Turing.haltList, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux] <;>
      try { congr 2; funext stack; fin_cases stack <;>
        simp [Function.update] } <;>
      try rfl))
end GaussianPivotScheduleTM
namespace GaussianPackedPivotColumnTM
open Turing GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
end GaussianPackedPivotColumnTM
namespace GaussianAdaptivePivotStepTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFlatAdjacentRecordSwapTM
open GapCVP.CNFFlatAdjacentConditionalSwapTM GapCVP.GaussianRowWorker
end GaussianAdaptivePivotStepTM
namespace BinaryGaussianStructuralAtomTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.BinaryStructuralRecordTM
end BinaryGaussianStructuralAtomTM
namespace BinaryGaussianStructuralRecordIndex
open GapCVP.BinaryEncoding GapCVP.SourceWholeOutputAssemblyTM
end BinaryGaussianStructuralRecordIndex
namespace BinaryPhysicalRowBasisDivisionTM
open Turing GapCVP.SourceStructuralTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMachineCert GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM GapCVP.CNFCappedUnaryPairArithmeticTM
end BinaryPhysicalRowBasisDivisionTM
namespace GaussianPhysicalWordRankIndexTM
open Turing GapCVP.BinaryDimensionTM GapCVP.BinaryGaussianStructuralAtomTM
open GapCVP.BinaryStructuralRecordTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end GaussianPhysicalWordRankIndexTM
namespace GaussianReducedConsistencyTM
open Turing GapCVP.GaussianRowWorker GapCVP.GaussianPivotScheduleTM
open GapCVP.GaussianPackedPivotColumnTM GapCVP.SourceFourFamilyBooleanPredicateTM
end GaussianReducedConsistencyTM
namespace GaussianAdaptiveEliminationCorrectness
open GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.GaussianPivotScheduleTM
open GapCVP.GaussianPackedPivotColumnTM
end GaussianAdaptiveEliminationCorrectness
namespace BinaryPhysicalWordEntries
open scoped BigOperators
open GapCVP.Core
attribute [local instance] Classical.propDecidable
end BinaryPhysicalWordEntries
namespace BinarySourceFieldMultiplicationTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.BinaryModularReductionTM
end BinarySourceFieldMultiplicationTM
namespace BinaryPhysicalLagrangeProductFoldTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceMixedRadixPolynomialPaddedDescriptorFoldTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceFieldMultiplicationTM
end BinaryPhysicalLagrangeProductFoldTM
namespace BinaryFieldInverseAlgebra
open GapCVP.Core GapCVP.Core.EffectiveBinaryField Polynomial
open scoped BigOperators
end BinaryFieldInverseAlgebra
namespace BinaryPhysicalLagrangeCoefficientTM
open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinarySourceFieldMultiplicationTM GapCVP.BinaryModularReductionTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
end BinaryPhysicalLagrangeCoefficientTM
namespace BinaryFieldInverseTM
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM
end
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceFieldMultiplicationTM
end
end BinaryFieldInverseTM
namespace BinarySourceConvolutionTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceStructuralTuringTM GapCVP.SourceMachineCert
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixDimensionRowMajorIndexTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CLStructuralPrefixWriter
open GapCVP.BinaryCoefficientTM GapCVP.BinarySourceFieldMultiplicationTM
end BinarySourceConvolutionTM
namespace BinarySourceConvolutionCorrectness
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceStructuralTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.SourceMixedRadixDimensionRowMajorIndexTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFEncodedClauseSort
open GapCVP.CNFNaturalOrderComparator GapCVP.CNFNaturalOrderTotalComparator
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.BinaryCoefficientTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.BinarySourceConvolutionTM
end
section
open Turing GapCVP.BinaryEncoding GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.BinarySourceConvolutionTM
end
end BinarySourceConvolutionCorrectness
namespace BinarySourceFieldMultiplicationTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceConvolutionTM
end BinarySourceFieldMultiplicationTM
namespace BinarySourceModularReductionFoldTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.BinaryDimensionTM GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceFieldMultiplicationTM
end BinarySourceModularReductionFoldTM
namespace BinarySourceFieldMultiplicationTM
open Turing GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceConvolutionTM GapCVP.BinarySourceConvolutionCorrectness
open GapCVP.BinarySourceModularReductionFoldTM
end BinarySourceFieldMultiplicationTM
namespace BinarySourceModularDegreeStepTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceConvolutionTM GapCVP.BinaryModularReductionTM
end BinarySourceModularDegreeStepTM
namespace BinarySourceModularDegreeStepCorrectness
open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceFormulaStructuralDecoder GapCVP.FormulaSemanticCert
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceConvolutionTM
open GapCVP.BinarySourceModularDegreeStepTM
end BinarySourceModularDegreeStepCorrectness
namespace BinarySourceModularDegreeStepSemanticSourceLemmas
open GapCVP.BinaryEncoding GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceConvolutionTM GapCVP.BinarySourceModularDegreeStepTM
end BinarySourceModularDegreeStepSemanticSourceLemmas
namespace BinarySourceModularDegreeStepSemanticCoefficientLemmas
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceModularDegreeStepTM
open GapCVP.BinarySourceModularDegreeStepSemanticSourceLemmas GapCVP.Core.EffectiveBinaryField
end BinarySourceModularDegreeStepSemanticCoefficientLemmas
namespace BinarySourceModularDegreeStepPhysicalCellCorrectness
open GapCVP.BinaryEncoding GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceModularDegreeStepTM
open GapCVP.BinarySourceModularDegreeStepSemanticSourceLemmas
open GapCVP.BinarySourceModularDegreeStepSemanticCoefficientLemmas
end BinarySourceModularDegreeStepPhysicalCellCorrectness
namespace BinarySourceModularDegreeStepSemanticCorrectness
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceConvolutionTM
open GapCVP.BinarySourceModularDegreeStepTM GapCVP.BinarySourceModularDegreeStepCorrectness
open GapCVP.BinarySourceModularDegreeStepPhysicalCellCorrectness
end BinarySourceModularDegreeStepSemanticCorrectness
namespace BinarySourceModularReductionFoldTM
open Turing GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceTotalStructuralDecoder GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryModularReductionTM
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.BinarySourceModularDegreeStepTM GapCVP.BinarySourceModularDegreeStepCorrectness
open GapCVP.BinarySourceModularDegreeStepSemanticCorrectness
end BinarySourceModularReductionFoldTM
namespace BinarySourceFieldMultiplicationTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.BinarySourceConvolutionTM GapCVP.BinarySourceModularDegreeStepCorrectness
open GapCVP.BinarySourceModularReductionFoldTM GapCVP.BinaryModularReductionTM
end BinarySourceFieldMultiplicationTM
namespace BinaryFieldInverseTM
open Turing GapCVP.BinaryFieldInverseAlgebra
end BinaryFieldInverseTM
namespace GaussianSourceConsistencyBridge
open Turing GapCVP.Factor400BinaryPhysicalWorkers GapCVP.GaussianRowWorker
open GapCVP.GaussianPivotScheduleTM GapCVP.GaussianPackedPivotColumnTM
open GapCVP.GaussianReducedConsistencyTM GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
end GaussianSourceConsistencyBridge
namespace BinaryPhysicalWordPackedMatrixTM
open Turing GapCVP.BinaryEncoding GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
end BinaryPhysicalWordPackedMatrixTM
namespace GaussianAdaptivePackedTraceCorrectness
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.BinaryPhysicalWordPackedMatrixTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePivotStepTM
end GaussianAdaptivePackedTraceCorrectness
namespace GaussianPhysicalWordReducedAtomTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.Factor400BinaryEffectiveBasisSerializerTM GapCVP.SourceWholeOutputAssemblyTM
end GaussianPhysicalWordReducedAtomTM
namespace GaussianPackedStateTargetAtomTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert GapCVP.GaussianRowWorker
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianPhysicalWordReducedAtomTM
open GapCVP.Factor400BinaryEffectiveBasisSerializerTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM
end GaussianPackedStateTargetAtomTM
namespace GaussianAdaptivePhysicalStateCellTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.SourceMachineCert
open GapCVP.SourceStructuralTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.BinaryDimensionTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
end GaussianAdaptivePhysicalStateCellTM
namespace GaussianAdaptivePackedStateLookupTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM GapCVP.GaussianAdaptivePivotStepTM
end GaussianAdaptivePackedStateLookupTM
namespace GaussianPackedStateBasisAtomTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.BinaryExplicitAffineRows GapCVP.GaussianRowWorker
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePackedStateLookupTM GapCVP.GaussianPackedStateTargetAtomTM
open GapCVP.GaussianPhysicalWordReducedAtomTM GapCVP.Factor400BinaryEffectiveBasisSerializerTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM
end GaussianPackedStateBasisAtomTM
namespace Factor400FinitePNormCorollary
open scoped BigOperators ENNReal
end Factor400FinitePNormCorollary
namespace Factor400FinitePRadiusArithmetic
open GapCVP.Factor400FinitePNormCorollary
end Factor400FinitePRadiusArithmetic
namespace Factor400BinaryCodeDecodingCorollary
open scoped BigOperators
open GapCVP.Factor400BinaryConstructiveSourcePlaces
end Factor400BinaryCodeDecodingCorollary
namespace Factor400FinitePRadiusSourceTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceAnchoredGridRecordFoldTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryRadiusTM
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePRadiusArithmetic
end Factor400FinitePRadiusSourceTM
namespace Factor400FinitePRadiusRationalAtomTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceStructuralTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFUnaryPairIndexTotalRuntimeCert
open GapCVP.CLStructuralAtomicNaturalWriter
end Factor400FinitePRadiusRationalAtomTM
namespace Factor400BinaryCompactPhysicalGaussianOutputSerializerTM
open Turing GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryStructuralRecordTM
open GapCVP.BinaryGaussianStructuralAtomTM GapCVP.GaussianPhysicalWordRankIndexTM
open GapCVP.GaussianPackedStateTargetAtomTM GapCVP.SourceWholeOutputAssemblyTM
end Factor400BinaryCompactPhysicalGaussianOutputSerializerTM
namespace OriginalThreeSATNPHardness
open Computability GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFFiveFamilySourceIndexedORGadgetFinalCert
end OriginalThreeSATNPHardness
namespace BinarySourceTautologyNormalizationExact
end BinarySourceTautologyNormalizationExact
namespace SourcePreprocessingSemantics
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.BinarySourceVariableCompaction
end SourcePreprocessingSemantics
namespace FormulaBridge
open GapCVP.Factor400FormulaBridge GapCVP.SourcePreprocessingSemantics
open GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinaryExplicitSourceSoundness
end FormulaBridge
namespace Factor400BinaryDecodingPromiseReduction
open scoped BigOperators
open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.BinaryEncoding
end Factor400BinaryDecodingPromiseReduction
namespace FourFamilySoundness
open scoped BigOperators
open GapCVP.FormulaBridge GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryExplicitFourFamilyKernel
open GapCVP.BinaryExplicitSourceSoundness GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryDecodingPromiseReduction
end FourFamilySoundness
namespace SourcePreprocessingTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.CNFGuardedFiveFamilyTagDispatchTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CLStructuralNaturalBinaryWriter GapCVP.BinaryDimensionTM
end SourcePreprocessingTM
namespace SourcePreprocessingPairwiseIdentity
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics
end SourcePreprocessingPairwiseIdentity
namespace SourcePreprocessingTM
open GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceIndexedClauseSignTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingPairwiseIdentity
end SourcePreprocessingTM
namespace NormalizedRecordDecoder
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.SourcePreprocessingTM
end NormalizedRecordDecoder
namespace ClauseCardinality
open GapCVP.SourcePreprocessingSemantics GapCVP.BinarySourceTautologyNormalizationExact
end ClauseCardinality
namespace SourceOrder
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryFieldBasis GapCVP.BinarySourceCoordinateOrder
open GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryOrderedAssembly
open GapCVP.BinaryOrderedRefinement GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge
open GapCVP.ClauseCardinality
end SourceOrder
namespace PhysicalColumnOrder
open GapCVP.Core GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryExplicitFourFamilyKernel
open GapCVP.FormulaBridge GapCVP.SourceOrder
end PhysicalColumnOrder
namespace PhysicalWordSoundness
open GapCVP.Core GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.PhysicalColumnOrder
end PhysicalWordSoundness
namespace Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open Turing GapCVP.Core GapCVP.Factor400BinaryInstanceBridge
open GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.OriginalThreeSATNPHardness
open GapCVP.SourcePreprocessingSemantics GapCVP.SourcePreprocessingTM GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.NormalizedRecordDecoder GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalWordSoundness
end Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
namespace ClauseOffsetTM
open Turing
open scoped BigOperators
open GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceStructuralTuringTM
open GapCVP.SourceMachineCert GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CLStructuralPrefixWriter GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingTM
end ClauseOffsetTM
namespace BinaryPhysicalWordQueryCatalogueTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
end BinaryPhysicalWordQueryCatalogueTM
namespace CanonicalMatrixShape
open scoped BigOperators
open Turing GapCVP.Core GapCVP.BinaryEncoding
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.ClauseOffsetTM
open GapCVP.PhysicalColumnOrder GapCVP.BinaryExplicitAffineRows
end CanonicalMatrixShape
namespace CanonicalSourceCatalogue
open scoped BigOperators
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMachineCert GapCVP.SourceStructuralTuringTM
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.SourceMixedRadixDimensionRowMajorIndexTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.GaussianRowWorker
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalWordPackedMatrixTM
open GapCVP.BinaryPhysicalWordQueryCatalogueTM GapCVP.CanonicalMatrixShape
open GapCVP.PhysicalColumnOrder
end CanonicalSourceCatalogue
namespace GaussianAdaptivePhysicalCandidateCatalogueTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryExplicitAffineRows
open GapCVP.GaussianPivotScheduleTM GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePackedStateLookupTM
end GaussianAdaptivePhysicalCandidateCatalogueTM
namespace GaussianAdaptivePhysicalColumnCellUpdateSemantics
open GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian
end GaussianAdaptivePhysicalColumnCellUpdateSemantics
namespace GaussianAdaptivePhysicalColumnCellUpdateTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.GaussianRowWorker GapCVP.GaussianAdaptivePivotStepTM
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianAdaptivePackedStateLookupTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
open GapCVP.GaussianAdaptivePhysicalColumnCellUpdateSemantics
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM
end GaussianAdaptivePhysicalColumnCellUpdateTM
namespace GaussianAdaptivePhysicalColumnStateTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM GapCVP.BinaryExplicitAffineRows
open GapCVP.Factor400BinaryPhysicalWorkers GapCVP.GaussianRowWorker
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePackedStateLookupTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
end GaussianAdaptivePhysicalColumnStateTM
namespace GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceMachineCert GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceStructuralTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.BinaryPhysicalWordQueryCatalogueTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
open GapCVP.GaussianAdaptivePhysicalColumnStateTM
open GapCVP.GaussianAdaptivePhysicalColumnCellUpdateTM
end GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM
namespace GaussianAdaptivePhysicalInitialStateTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceStructuralTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM
end GaussianAdaptivePhysicalInitialStateTM
namespace GaussianAdaptivePhysicalColumnIterationBoundTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.BinaryDimensionTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePhysicalColumnStateTM
open GapCVP.GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM
open GapCVP.GaussianAdaptivePhysicalInitialStateTM
end GaussianAdaptivePhysicalColumnIterationBoundTM
namespace GaussianAdaptivePhysicalPackedStateBoundTM
open GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
end GaussianAdaptivePhysicalPackedStateBoundTM
namespace GaussianAdaptivePhysicalColumnIterationBoundTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.OutputBoundedDependentRecordFold GapCVP.BinaryPhysicalWordPackedMatrixTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
open GapCVP.GaussianAdaptivePhysicalColumnStateTM
open GapCVP.GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM
open GapCVP.GaussianAdaptivePhysicalInitialStateTM
open GapCVP.GaussianAdaptivePhysicalPackedStateBoundTM
end GaussianAdaptivePhysicalColumnIterationBoundTM
namespace GaussianSourceInitializer
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.FormulaBridge GapCVP.PhysicalColumnOrder GapCVP.SourceOrder
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalColumnIterationBoundTM
end GaussianSourceInitializer
namespace GaussianAdaptivePhysicalReducedConsistencyCatalogueTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.OutputBoundedDependentRecordFold GapCVP.BinaryExplicitAffineRows
open GapCVP.GaussianPackedPivotColumnTM GapCVP.GaussianReducedConsistencyTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM GapCVP.GaussianAdaptivePackedStateLookupTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
end GaussianAdaptivePhysicalReducedConsistencyCatalogueTM
namespace GaussianSourceReducedConsistency
open Turing GapCVP.BinaryEncoding GapCVP.PhysicalColumnOrder GapCVP.GaussianSourceInitializer
open GapCVP.GaussianAdaptivePhysicalReducedConsistencyCatalogueTM
open GapCVP.GaussianReducedConsistencyTM
end GaussianSourceReducedConsistency
namespace GaussianSourceInitializerInstantiation
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.CanonicalMatrixShape
open GapCVP.CanonicalSourceCatalogue GapCVP.PhysicalColumnOrder
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianReducedConsistencyTM
open GapCVP.GaussianSourceInitializer GapCVP.GaussianSourceReducedConsistency
end GaussianSourceInitializerInstantiation
namespace GaussianOutputSerializerTM
open Turing GapCVP.Core GapCVP.Factor400BinaryInstanceBridge GapCVP.BinaryEncoding
open GapCVP.SourceMachineCert GapCVP.CLStructuralPrefixWriter
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.BinaryDimensionTM GapCVP.BinaryExplicitAffineRows GapCVP.BinaryStructuralRecordTM
open GapCVP.BinaryGaussianStructuralAtomTM GapCVP.BinaryGaussianStructuralRecordIndex
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.GaussianPhysicalWordRankIndexTM
open GapCVP.GaussianPackedStateTargetAtomTM GapCVP.GaussianPackedStateBasisAtomTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.Factor400BinaryCompactPhysicalGaussianOutputSerializerTM GapCVP.CanonicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end GaussianOutputSerializerTM
namespace PhysicalFamilyRowTM
open scoped BigOperators
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMachineCert GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CLStructuralNaturalBinaryWriter GapCVP.CLVerifier GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.BinarySourceVariableCompaction
open GapCVP.BinaryCompactSourceFirstOccurrenceTM GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingTM GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
end PhysicalFamilyRowTM
namespace Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap GapCVP.BinaryRadiusTM
end Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
namespace PhysicalNormalizedBranchTM
open Turing GapCVP.BinaryEncoding GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.PhysicalFamilyRowTM GapCVP.GaussianRowWorker
open GapCVP.Factor400BinaryPhysicalWorkers
end PhysicalNormalizedBranchTM
namespace PhysicalNormalizedCanonicalGuardTM
open Turing GapCVP.SourceOriginalSourcePreservingTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.PhysicalNormalizedBranchTM
open GapCVP.Factor400BinaryPhysicalWorkers
end PhysicalNormalizedCanonicalGuardTM
namespace GaussianExactSourceInitializer
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.CanonicalMatrixShape GapCVP.PhysicalColumnOrder
open GapCVP.GaussianSourceConsistencyBridge GapCVP.GaussianSourceInitializerInstantiation
end GaussianExactSourceInitializer
namespace ExactPhysicalSourceTM
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianSourceConsistencyBridge
open GapCVP.SourcePreprocessingSemantics GapCVP.CanonicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.PhysicalNormalizedBranchTM GapCVP.PhysicalNormalizedCanonicalGuardTM
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceInitializerInstantiation
open GapCVP.GaussianOutputSerializerTM
end ExactPhysicalSourceTM
namespace PhysicalFamilyMarkerTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.PhysicalFamilyRowTM
end PhysicalFamilyMarkerTM
namespace ShiftedTupleTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingTM GapCVP.ClauseOffsetTM
end ShiftedTupleTM
namespace CanonicalOffsetIdentity
open scoped BigOperators
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleTM GapCVP.SourceOrder
end CanonicalOffsetIdentity
namespace Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine
open scoped BigOperators
open Turing GapCVP.Core GapCVP.BinaryEncoding
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.BinaryExplicitAffineSystem
open GapCVP.FormulaBridge GapCVP.ClauseOffsetTM GapCVP.SourceOrder GapCVP.ShiftedTupleTM
open GapCVP.CanonicalOffsetIdentity GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalFamilyMarkerTM
end Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine
namespace CanonicalPhysicalMatrixShape
open Turing GapCVP.BinaryEncoding GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.FormulaBridge GapCVP.CanonicalMatrixShape GapCVP.PhysicalColumnOrder
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine
end CanonicalPhysicalMatrixShape
namespace BinaryCompactPhysicalFieldCoefficientBitTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalCellGridWordTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM
end BinaryCompactPhysicalFieldCoefficientBitTM
namespace BinaryCompactPhysicalFieldBasisCoordinates
open Polynomial GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra
end BinaryCompactPhysicalFieldBasisCoordinates
namespace MatrixEntrySemantics
open scoped BigOperators
open GapCVP.Core GapCVP.Core.EffectiveBinaryField
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryOrderedRefinement GapCVP.FormulaBridge
open GapCVP.PhysicalColumnOrder GapCVP.SourceOrder GapCVP.BinaryPhysicalWordEntries
open GapCVP.BinaryReedSolomonParity GapCVP.BinarySourceRowOrder
attribute [local instance] Classical.propDecidable
end MatrixEntrySemantics
namespace PhysicalRowOrderProjection
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge
open GapCVP.SourceOrder GapCVP.PhysicalColumnOrder GapCVP.MatrixEntrySemantics
end PhysicalRowOrderProjection
namespace PhysicalRightHandSideTM
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalRowOrderProjection
end PhysicalRightHandSideTM
namespace BinaryAllWordRankOrder
open GapCVP.BinaryFieldBasis GapCVP.Core.EffectiveBinaryField
end BinaryAllWordRankOrder
namespace BinarySelectedIrreducibleWordTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM
open GapCVP.BinarySourceConvolutionTM
end BinarySelectedIrreducibleWordTM
namespace BinarySelectedIrreducibleFactorCorrectness
open Turing GapCVP.BinaryFieldBasis
open GapCVP.BinaryAllWordRankOrder GapCVP.Core.EffectiveBinaryField
end BinarySelectedIrreducibleFactorCorrectness
namespace BinarySelectedIrreducibleWordOrderCorrectness
open GapCVP.BinaryAllWordRankOrder GapCVP.BinaryFieldBasis GapCVP.BinaryModularReductionTM
open GapCVP.BinarySelectedIrreducibleWordTM GapCVP.Core.EffectiveBinaryField
end BinarySelectedIrreducibleWordOrderCorrectness
namespace Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceStructuralTuringTM GapCVP.SourceMixedRadixDimensionRowMajorIndexTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.GaussianPivotScheduleTM GapCVP.GaussianRowWorker GapCVP.BinaryFieldBasis
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.BinarySourceConvolutionTM GapCVP.BinarySourceConvolutionCorrectness
open GapCVP.BinarySelectedIrreducibleWordTM GapCVP.BinarySelectedIrreducibleWordOrderCorrectness
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.Core.EffectiveBinaryField
end
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryModularReductionTM GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.BinarySelectedIrreducibleWordTM GapCVP.BinarySelectedIrreducibleWordOrderCorrectness
open GapCVP.BinarySelectedIrreducibleFactorCorrectness GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.GaussianPivotScheduleTM GapCVP.GaussianRowWorker GapCVP.Core.EffectiveBinaryField
end
end Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
namespace PhysicalMatrixCellTM
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRightHandSideTM
open GapCVP.SourceOrder GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.BinaryCompactPhysicalFieldCoefficientBitTM
open GapCVP.CanonicalMatrixShape GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
end PhysicalMatrixCellTM
namespace PhysicalGlobalRefinementCoefficientTM
open scoped BigOperators
open Turing GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalFamilyMarkerTM GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalRightHandSideTM
attribute [local instance] Classical.propDecidable
end PhysicalGlobalRefinementCoefficientTM
namespace PhysicalColumnOrderProjection
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceCoordinateOrder GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRowOrderProjection
end PhysicalColumnOrderProjection
namespace PhysicalGlobalCoefficientCorrectness
open scoped BigOperators
open GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinarySourceCoordinateOrder GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.PhysicalColumnOrder GapCVP.PhysicalColumnOrderProjection GapCVP.PhysicalFamilyRowTM
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalGlobalRefinementCoefficientTM
attribute [local instance] Classical.propDecidable
end PhysicalGlobalCoefficientCorrectness
namespace PhysicalRefinementFieldCoordinateCorrectness
open scoped BigOperators
open GapCVP.Core GapCVP.BinarySourceRowOrder GapCVP.BinaryExplicitAffineSystem
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalGlobalCoefficientCorrectness
attribute [local instance] Classical.propDecidable
end PhysicalRefinementFieldCoordinateCorrectness
namespace PhysicalRefinementRowProjection
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinarySourceCoordinateOrder GapCVP.BinarySourceRowOrder GapCVP.FormulaBridge
open GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalRowOrderProjection
end PhysicalRefinementRowProjection
namespace PhysicalRefinementSelectedRowProjection
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalRefinementRowProjection
end PhysicalRefinementSelectedRowProjection
namespace PhysicalRefinementSelectedProductProjection
open GapCVP.BinaryEncoding GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.MatrixEntrySemantics
end PhysicalRefinementSelectedProductProjection
namespace PhysicalRefinementColumnTagProjection
open scoped BigOperators
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.ClauseOffsetTM
end PhysicalRefinementColumnTagProjection
namespace SourceClausePrefixBridge
open scoped BigOperators
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
open GapCVP.SourceOrder GapCVP.CanonicalOffsetIdentity
end SourceClausePrefixBridge
namespace PhysicalRefinementColumnTagSourceCorrectness
open scoped BigOperators
open GapCVP.BinaryEncoding GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.ClauseOffsetTM GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalColumnOrderProjection
open GapCVP.PhysicalRefinementColumnTagProjection GapCVP.SourceClausePrefixBridge
end PhysicalRefinementColumnTagSourceCorrectness
namespace RefinementClauseOffsetTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingTM GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleTM
end RefinementClauseOffsetTM
namespace PhysicalRefinementClauseLocalTagTM
open Turing
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleTM
open GapCVP.RefinementClauseOffsetTM GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalRightHandSideTM GapCVP.PhysicalGlobalRefinementCoefficientTM
open GapCVP.PhysicalRefinementRowProjection
end PhysicalRefinementClauseLocalTagTM
namespace PhysicalRefinementCheckSourceCorrectness
open scoped BigOperators
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.ClauseOffsetTM GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalRightHandSideTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.PhysicalRefinementSelectedRowProjection
open GapCVP.PhysicalRefinementColumnTagProjection
open GapCVP.PhysicalRefinementColumnTagSourceCorrectness
open GapCVP.PhysicalRefinementClauseLocalTagTM
attribute [local instance] Classical.propDecidable
end PhysicalRefinementCheckSourceCorrectness
namespace PhysicalRefinementGuardAbsorption
open GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryExplicitAffineSystem GapCVP.BinarySourceCoordinateOrder
open GapCVP.BinarySourceRowOrder GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalColumnOrderProjection GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalFamilyMarkerTM GapCVP.MatrixEntrySemantics GapCVP.PhysicalRightHandSideTM
open GapCVP.PhysicalRefinementRowProjection GapCVP.PhysicalRefinementSelectedRowProjection
open GapCVP.PhysicalRefinementSelectedProductProjection
open GapCVP.PhysicalRefinementFieldCoordinateCorrectness
open GapCVP.PhysicalRefinementClauseLocalTagTM GapCVP.PhysicalRefinementCheckSourceCorrectness
attribute [local instance] Classical.propDecidable
end PhysicalRefinementGuardAbsorption
namespace Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceAnchoredGridRecordFoldTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.BinaryDimensionTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryFieldInverseTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM
end
section
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryFieldInverseTM
open GapCVP.BinaryModularReductionTM GapCVP.PhysicalFamilyRowTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM
end
section
open Turing GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
end
end Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
namespace BinaryCompactPhysicalFieldWordXorTM
open Turing Polynomial GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.GaussianXorWorker GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalCellGridWordTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalWordRuntimeDegreeTM
end BinaryCompactPhysicalFieldWordXorTM
namespace BinaryCompactPhysicalLagrangeProductFoldTM
open Turing GapCVP.SourceFormulaStructuralDecoder GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceFieldMultiplicationTM GapCVP.BinaryPhysicalLagrangeProductFoldTM
end BinaryCompactPhysicalLagrangeProductFoldTM
namespace BinaryCompactPhysicalLagrangeFactorStreamTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalLagrangeProductFoldTM
open GapCVP.BinaryCompactPhysicalLagrangeProductFoldTM
end BinaryCompactPhysicalLagrangeFactorStreamTM
namespace PhysicalOrdinaryShiftedCoefficientTM
open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinarySourceFieldMultiplicationTM GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
end PhysicalOrdinaryShiftedCoefficientTM
namespace BinaryCompactPhysicalNodeParityTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.Factor400BinaryPhysicalParityTM
end BinaryCompactPhysicalNodeParityTM
namespace PhysicalOrdinaryShiftedCoefficientSumTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalNodeParityTM GapCVP.PhysicalFamilyRowTM
end PhysicalOrdinaryShiftedCoefficientSumTM
namespace BinaryCompactPhysicalLagrangeNestedNodeTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM
end BinaryCompactPhysicalLagrangeNestedNodeTM
namespace BinaryCompactPhysicalLagrangeMomentWeightTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalLagrangeProductFoldTM
open GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
end BinaryCompactPhysicalLagrangeMomentWeightTM
namespace BinaryCompactPhysicalLagrangeNodeProductTM
open Turing GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end BinaryCompactPhysicalLagrangeNodeProductTM
namespace BinaryCompactPhysicalLagrangeMomentWeightTM
open Turing GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
end BinaryCompactPhysicalLagrangeMomentWeightTM
namespace SourceFieldMomentOperationsTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
open GapCVP.BinaryCompactPhysicalLagrangeMomentWeightTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
end SourceFieldMomentOperationsTM
namespace PhysicalInterpolationDirectMomentBitTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.PhysicalMatrixCellTM
end PhysicalInterpolationDirectMomentBitTM
namespace PhysicalMaskedInterpolationNodeParityTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalFieldCoefficientBitTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalGlobalRefinementCoefficientTM
open GapCVP.PhysicalMatrixCellTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end PhysicalMaskedInterpolationNodeParityTM
namespace Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis
open GapCVP.BinaryModularReductionTM GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinarySelectedIrreducibleWordTM
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
end Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
namespace PhysicalInterpolationNodeGridMaskTM
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalCellGridWordTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
end PhysicalInterpolationNodeGridMaskTM
namespace PhysicalInterpolationNodeFactorTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalInterpolationNodeGridMaskTM
open GapCVP.Factor400BinaryConstructiveSourcePlaces
end PhysicalInterpolationNodeFactorTM
namespace BinaryCompactPhysicalLagrangeNodeProductAlgebra
open scoped BigOperators
open GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryFieldInverseAlgebra
end BinaryCompactPhysicalLagrangeNodeProductAlgebra
namespace PhysicalFieldWordSemantics
open GapCVP.Core GapCVP.Core.EffectiveBinaryField
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics
end PhysicalFieldWordSemantics
namespace PhysicalLagrangeNodeProductAlgebra
open scoped BigOperators
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.BinaryCompactPhysicalLagrangeNodeProductAlgebra GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientTM GapCVP.BinarySourceCoordinateOrder
open GapCVP.Factor400BinaryConstructiveSourcePlaces
end PhysicalLagrangeNodeProductAlgebra
namespace PhysicalLagrangeNodeProductCatalogueCorrectness
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalLagrangeProductFoldTM
open GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
open GapCVP.BinaryCompactPhysicalLagrangeNodeProductTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalLagrangeNodeProductAlgebra
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end PhysicalLagrangeNodeProductCatalogueCorrectness
namespace PhysicalInterpolationNestedNodeProductTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalLagrangeProductFoldTM
open GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
open GapCVP.BinaryCompactPhysicalLagrangeNodeProductTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.PhysicalInterpolationNodeGridMaskTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalLagrangeNodeProductAlgebra
open GapCVP.PhysicalLagrangeNodeProductCatalogueCorrectness
open GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end PhysicalInterpolationNestedNodeProductTM
namespace PhysicalLagrangeNodeDenominatorNonzero
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFieldWordSemantics
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.BinarySourceCoordinateOrder
open GapCVP.Factor400BinaryConstructiveSourcePlaces
end PhysicalLagrangeNodeDenominatorNonzero
namespace PhysicalInterpolationNodeWeightTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalInterpolationNestedNodeProductTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end PhysicalInterpolationNodeWeightTM
namespace PhysicalInterpolationNodeWeightCorrectness
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.PhysicalInterpolationNodeFactorTM GapCVP.PhysicalLagrangeNodeProductAlgebra
open GapCVP.PhysicalInterpolationNestedNodeProductTM GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end PhysicalInterpolationNodeWeightCorrectness
namespace PhysicalOrdinaryShiftedCheckBitInstantiation
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalInterpolationDirectMomentBitTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.PhysicalInterpolationNodeWeightCorrectness
end PhysicalOrdinaryShiftedCheckBitInstantiation
namespace BinaryPhysicalLagrangeParityEntry
open scoped BigOperators
open Polynomial GapCVP.BinaryReedSolomonParity
end BinaryPhysicalLagrangeParityEntry
namespace PhysicalSelectedInterpolationCoefficientProjection
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryReedSolomonParity
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalColumnOrder
open GapCVP.MatrixEntrySemantics
attribute [local instance] Classical.propDecidable
end PhysicalSelectedInterpolationCoefficientProjection
namespace PhysicalInterpolationNodeParitySemanticCorrectness
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField
end PhysicalInterpolationNodeParitySemanticCorrectness
namespace PhysicalMaskedInterpolationNodeParitySemanticCorrectness
open GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeParitySemanticCorrectness
open GapCVP.PhysicalOrdinaryShiftedCoefficientTM
end PhysicalMaskedInterpolationNodeParitySemanticCorrectness
namespace PhysicalInterpolationNodeWeightSourceFieldCorrectness
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalInterpolationNodeWeightTM GapCVP.PhysicalLagrangeNodeDenominatorNonzero
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.SourceFieldMomentOperationsTM
open GapCVP.BinarySourceCoordinateOrder
end PhysicalInterpolationNodeWeightSourceFieldCorrectness
namespace PhysicalOrdinaryShiftedCheckBitInstantiation
open Turing GapCVP.Core GapCVP.BinaryEncoding
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalMaskedInterpolationNodeParitySemanticCorrectness
end PhysicalOrdinaryShiftedCheckBitInstantiation
namespace ShiftedTupleBetaTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceIndexedClauseSignTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingTM
open GapCVP.SourcePreprocessingSemantics GapCVP.ClauseOffsetTM
end ShiftedTupleBetaTM
namespace SatisfyingWordSourceRankSemantics
open GapCVP.SourceOrder GapCVP.ShiftedTupleBetaTM
end SatisfyingWordSourceRankSemantics
namespace PhysicalInterpolationRowFamilyProjection
open scoped BigOperators
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
open GapCVP.ShiftedTupleTM GapCVP.SourceOrder GapCVP.CanonicalOffsetIdentity
open GapCVP.PhysicalRowOrderProjection GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine
end PhysicalInterpolationRowFamilyProjection
namespace PhysicalOrdinaryInterpolationRowTagCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection GapCVP.PhysicalRefinementRowProjection
open GapCVP.PhysicalRowOrderProjection GapCVP.SourceOrder
end PhysicalOrdinaryInterpolationRowTagCorrectness
namespace PhysicalOrdinaryInterpolationCheckFieldCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalOrdinaryInterpolationRowTagCorrectness
open GapCVP.PhysicalSelectedInterpolationCoefficientProjection GapCVP.SourceOrder
open GapCVP.BinaryReedSolomonParity
end PhysicalOrdinaryInterpolationCheckFieldCorrectness
namespace PhysicalOrdinaryInterpolationTypeMatchCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.MatrixEntrySemantics GapCVP.PhysicalColumnOrderProjection
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalOrdinaryInterpolationRowTagCorrectness GapCVP.SourceOrder
end PhysicalOrdinaryInterpolationTypeMatchCorrectness
namespace PhysicalOrdinaryShiftedCheckBitInstantiation
open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.SourceFieldMomentOperationsTM
end PhysicalOrdinaryShiftedCheckBitInstantiation
namespace PhysicalOrdinaryInterpolationRowGridBasisCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationRowTagCorrectness GapCVP.PhysicalRowOrderProjection
open GapCVP.SourceOrder
end PhysicalOrdinaryInterpolationRowGridBasisCorrectness
namespace PhysicalInterpolationNodeCountBounds
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalColumnOrderProjection
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalMaskedInterpolationNodeParityTM
end PhysicalInterpolationNodeCountBounds
namespace BinaryCompactSourceVariableRankTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceNormalizedVariableRankScanTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinarySourceVariableCompaction
open GapCVP.BinaryCompactRankPrefixIdentity GapCVP.BinaryCompactSourceFirstOccurrenceTM
end BinaryCompactSourceVariableRankTM
namespace ShiftedTupleBetaSourceCorrectness
open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryCompactSourceVariableRankTM
open GapCVP.BinarySourceVariableCompaction GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingTM GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingPairwiseIdentity
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM
end ShiftedTupleBetaSourceCorrectness
namespace SourceVariableRankBridge
open Turing GapCVP.SourceMachineCert GapCVP.BinarySourceVariableCompaction
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingPairwiseIdentity GapCVP.FormulaBridge
end SourceVariableRankBridge
namespace ShiftedTupleAnchorSourceFieldCorrectness
open Turing GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.SourceVariableRankBridge
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM GapCVP.ShiftedTupleBetaSourceCorrectness
end ShiftedTupleAnchorSourceFieldCorrectness
namespace ShiftedTupleBetaSourceFieldCorrectness
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceIndexedClauseSignTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeMomentWeightTM GapCVP.FormulaBridge
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM
end ShiftedTupleBetaSourceFieldCorrectness
namespace PhysicalShiftedInterpolationBaseTM
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalFieldWordXorTM GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.PhysicalOrdinaryShiftedCoefficientTM
open GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM GapCVP.ShiftedTupleBetaSourceCorrectness
open GapCVP.ShiftedTupleBetaSourceFieldCorrectness
open GapCVP.ShiftedTupleAnchorSourceFieldCorrectness
end PhysicalShiftedInterpolationBaseTM
namespace PhysicalInterpolationColumnSourceFieldCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinarySourceCoordinateOrder GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalColumnOrderProjection
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.SourceOrder
end PhysicalInterpolationColumnSourceFieldCorrectness
namespace PhysicalOrdinaryShiftedCheckBitInstantiation
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalFamilyMarkerTM GapCVP.PhysicalFieldWordSemantics
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationTypeMatchCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.SourceOrder
open GapCVP.SourceFieldMomentOperationsTM
end PhysicalOrdinaryShiftedCheckBitInstantiation
namespace PhysicalOrdinaryInterpolationParityFieldCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinaryPhysicalLagrangeParityEntry GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationRowGridBasisCorrectness
open GapCVP.SourceFieldMomentOperationsTM GapCVP.SourceOrder GapCVP.BinaryReedSolomonParity
open GapCVP.BinarySourceCoordinateOrder
end PhysicalOrdinaryInterpolationParityFieldCorrectness
namespace PhysicalOrdinaryInterpolationSelectedSourceWeightCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationColumnSourceFieldCorrectness
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.PhysicalInterpolationNodeWeightSourceFieldCorrectness
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationRowGridBasisCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.SourceOrder GapCVP.BinarySourceCoordinateOrder
end PhysicalOrdinaryInterpolationSelectedSourceWeightCorrectness
namespace PhysicalOrdinaryInterpolationSourceParityCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationSelectedSourceWeightCorrectness
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.SourceOrder GapCVP.BinaryReedSolomonParity
end PhysicalOrdinaryInterpolationSourceParityCorrectness
namespace PhysicalShiftedSourceColumnGridProjection
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalColumnOrderProjection GapCVP.SourceOrder
end PhysicalShiftedSourceColumnGridProjection
namespace PhysicalOrdinaryInterpolationBinaryCheckBitCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeCountBounds
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationRowGridBasisCorrectness
open GapCVP.PhysicalOrdinaryInterpolationSourceParityCorrectness
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.PhysicalShiftedSourceColumnGridProjection
open GapCVP.SourceFieldMomentOperationsTM GapCVP.SourceOrder
end PhysicalOrdinaryInterpolationBinaryCheckBitCorrectness
namespace PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalInterpolationDirectMomentBitTM GapCVP.PhysicalInterpolationNodeCountBounds
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationBinaryCheckBitCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.SourceOrder
end PhysicalOrdinaryShiftedCheckBitInstantiation
namespace ShiftedClauseOffsetTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingTM GapCVP.ClauseOffsetTM GapCVP.RefinementClauseOffsetTM
open GapCVP.ShiftedTupleTM
end ShiftedClauseOffsetTM
namespace PhysicalShiftedRowTupleRankTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.SourcePreprocessingTM GapCVP.SourcePreprocessingSemantics GapCVP.ClauseOffsetTM
open GapCVP.ShiftedTupleTM GapCVP.ShiftedClauseOffsetTM GapCVP.ShiftedTupleBetaTM
open GapCVP.PhysicalFamilyRowTM GapCVP.SourceFieldMomentOperationsTM
end PhysicalShiftedRowTupleRankTM
namespace PhysicalShiftedExpectedTypeRankTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleBetaTM
open GapCVP.RefinementClauseOffsetTM GapCVP.PhysicalShiftedRowTupleRankTM
end PhysicalShiftedExpectedTypeRankTM
namespace PhysicalShiftedInterpolationBaseCorrectness
open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.PhysicalOrdinaryShiftedCoefficientTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM GapCVP.ShiftedTupleBetaSourceCorrectness
open GapCVP.ShiftedTupleBetaSourceFieldCorrectness
open GapCVP.ShiftedTupleAnchorSourceFieldCorrectness GapCVP.PhysicalShiftedInterpolationBaseTM
end PhysicalShiftedInterpolationBaseCorrectness
namespace PhysicalShiftedInterpolationBaseInstantiation
open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.PhysicalFamilyRowTM GapCVP.ShiftedTupleBetaTM
open GapCVP.ShiftedTupleBetaSourceCorrectness GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationBaseCorrectness
end PhysicalShiftedInterpolationBaseInstantiation
namespace PhysicalOrdinaryShiftedCheckBitInstantiation
open Turing GapCVP.PhysicalFamilyMarkerTM GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation
end PhysicalOrdinaryShiftedCheckBitInstantiation
namespace PhysicalShiftedRowTupleRankBounds
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourceOrder
open GapCVP.ShiftedTupleTM GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalShiftedRowTupleRankTM
end PhysicalShiftedRowTupleRankBounds
namespace PhysicalOrdinaryShiftedCheckBitInstantiation
open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.SourceOrder GapCVP.BinarySourceTautologyNormalizationExact
end PhysicalOrdinaryShiftedCheckBitInstantiation
namespace PhysicalShiftedInterpolationBaseSourceFieldCorrectness
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryCompactPhysicalFieldWordXorTM GapCVP.BinarySourceCoordinateOrder
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalLagrangeNodeDenominatorNonzero
open GapCVP.ShiftedTupleAnchorSourceFieldCorrectness
open GapCVP.ShiftedTupleBetaSourceFieldCorrectness GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation
end PhysicalShiftedInterpolationBaseSourceFieldCorrectness
namespace PhysicalShiftedInterpolationParityFieldCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryReedSolomonParity
open GapCVP.BinarySourceCoordinateOrder GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.PhysicalInterpolationNodeWeightSourceFieldCorrectness
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation GapCVP.SourceFieldMomentOperationsTM
end PhysicalShiftedInterpolationParityFieldCorrectness
namespace PhysicalShiftedInterpolationRowSourceProjection
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge
open GapCVP.SourceOrder GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalRefinementRowProjection GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalInterpolationRowFamilyProjection
end PhysicalShiftedInterpolationRowSourceProjection
namespace PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryReedSolomonParity
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedRowTupleRankBounds
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationParityFieldCorrectness
open GapCVP.SourceFieldMomentOperationsTM
end PhysicalShiftedInterpolationParityMaskedFieldCorrectness
namespace PhysicalShiftedInterpolationRowFieldCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryReedSolomonParity
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalSelectedInterpolationCoefficientProjection
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
end PhysicalShiftedInterpolationRowFieldCorrectness
namespace PhysicalShiftedInterpolationRowDigitCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalLagrangeNodeProductAlgebra
open GapCVP.PhysicalInterpolationNodeFactorTM GapCVP.PhysicalInterpolationNodeCountBounds
open GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
end PhysicalShiftedInterpolationRowDigitCorrectness
namespace PhysicalShiftedInterpolationBinaryCheckBitCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra GapCVP.FormulaBridge
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.SourceFieldMomentOperationsTM GapCVP.SourceOrder
end PhysicalShiftedInterpolationBinaryCheckBitCorrectness
namespace PhysicalShiftedInterpolationParityDecodedFieldCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryReedSolomonParity GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowDigitCorrectness
open GapCVP.PhysicalShiftedSourceColumnGridProjection
open GapCVP.PhysicalShiftedInterpolationParityFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.SourceFieldMomentOperationsTM
end PhysicalShiftedInterpolationParityDecodedFieldCorrectness
namespace PhysicalShiftedInterpolationRowCanonicalRankCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
open GapCVP.ShiftedTupleTM GapCVP.CanonicalOffsetIdentity GapCVP.SourceClausePrefixBridge
open GapCVP.SourceOrder GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalColumnOrderProjection GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalRefinementColumnTagSourceCorrectness GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedRowTupleRankBounds GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
end PhysicalShiftedInterpolationRowCanonicalRankCorrectness
namespace PhysicalShiftedInterpolationRowCanonicalSourceDigits
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge
open GapCVP.ShiftedTupleTM GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalRankCorrectness
end PhysicalShiftedInterpolationRowCanonicalSourceDigits
namespace PhysicalShiftedInterpolationLocalVariableWordRank
open GapCVP.Core GapCVP.FormulaBridge GapCVP.SourceOrder
end PhysicalShiftedInterpolationLocalVariableWordRank
namespace PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.CanonicalOffsetIdentity
open GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedRowTupleRankBounds
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalRankCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceDigits
open GapCVP.PhysicalShiftedInterpolationLocalVariableWordRank
end PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits
namespace PhysicalShiftedInterpolationRowCanonicalRankCorrectness
open scoped BigOperators
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
open GapCVP.ShiftedTupleTM GapCVP.CanonicalOffsetIdentity GapCVP.SourceClausePrefixBridge
open GapCVP.SourceOrder GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalColumnOrderProjection GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalRefinementColumnTagSourceCorrectness GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedRowTupleRankBounds GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceDigits
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits
end PhysicalShiftedInterpolationRowCanonicalRankCorrectness
namespace PhysicalShiftedInterpolationBinaryHCoreCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationBinaryCheckBitCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationParityDecodedFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalRankCorrectness
open GapCVP.PhysicalShiftedInterpolationRowDigitCorrectness
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedRowTupleRankBounds GapCVP.SourceFieldMomentOperationsTM
open GapCVP.SourceOrder GapCVP.PhysicalInterpolationNodeCountBounds
end PhysicalShiftedInterpolationBinaryHCoreCorrectness
namespace PhysicalShiftedCanonicalInterpolationBaseSourceWordSemanticBridge
open GapCVP.SourcePreprocessingSemantics GapCVP.SourceOrder
end PhysicalShiftedCanonicalInterpolationBaseSourceWordSemanticBridge
namespace PhysicalShiftedCanonicalRetainedClauseSourceCorrectness
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.CanonicalOffsetIdentity GapCVP.SourceOrder
end PhysicalShiftedCanonicalRetainedClauseSourceCorrectness
namespace PhysicalShiftedCanonicalInterpolationBaseSourceFormulaTransport
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.CanonicalOffsetIdentity
open GapCVP.PhysicalShiftedCanonicalInterpolationBaseSourceWordSemanticBridge
end PhysicalShiftedCanonicalInterpolationBaseSourceFormulaTransport
namespace PhysicalShiftedCanonicalBetaSourceCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.CanonicalOffsetIdentity GapCVP.SatisfyingWordSourceRankSemantics
open GapCVP.ShiftedTupleBetaTM GapCVP.ShiftedTupleBetaSourceCorrectness
open GapCVP.ShiftedTupleAnchorSourceFieldCorrectness GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalShiftedRowTupleRankTM GapCVP.PhysicalShiftedRowTupleRankBounds
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceDigits
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits
open GapCVP.PhysicalShiftedCanonicalInterpolationBaseSourceFormulaTransport
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation
end PhysicalShiftedCanonicalBetaSourceCorrectness
namespace PhysicalShiftedCanonicalAnchorSourceCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.CanonicalOffsetIdentity
open GapCVP.SourceOrder GapCVP.ShiftedTupleAnchorSourceFieldCorrectness
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedRowTupleRankBounds
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceDigits
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits
open GapCVP.PhysicalShiftedCanonicalInterpolationBaseSourceFormulaTransport
end PhysicalShiftedCanonicalAnchorSourceCorrectness
namespace PhysicalShiftedCanonicalInterpolationBaseSemanticCorrectness
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedCanonicalBetaSourceCorrectness
open GapCVP.PhysicalShiftedCanonicalAnchorSourceCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseSourceFieldCorrectness
open GapCVP.PhysicalInterpolationColumnSourceFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
end PhysicalShiftedCanonicalInterpolationBaseSemanticCorrectness
namespace PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalInterpolationDirectMomentBitTM GapCVP.PhysicalInterpolationNodeCountBounds
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationBinaryCheckBitCorrectness
open GapCVP.PhysicalShiftedCanonicalInterpolationBaseSemanticCorrectness
open GapCVP.PhysicalShiftedInterpolationBinaryHCoreCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.PhysicalShiftedRowTupleRankBounds GapCVP.SourceFieldMomentOperationsTM
open GapCVP.SourceOrder
end PhysicalOrdinaryShiftedCheckBitInstantiation
namespace Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows GapCVP.CanonicalMatrixShape
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalGlobalCoefficientCorrectness GapCVP.PhysicalGlobalRefinementCoefficientTM
open GapCVP.PhysicalMatrixCellTM GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalRefinementCheckSourceCorrectness GapCVP.PhysicalRefinementGuardAbsorption
open GapCVP.SourceOrder
end Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
namespace Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine
open GapCVP.OriginalThreeSATNPHardness GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.ExactPhysicalSourceTM
end Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine
namespace Factor400BinaryDecodingPromiseHardness
open scoped BigOperators
open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.Factor400BinaryDecodingPromiseReduction
end Factor400BinaryDecodingPromiseHardness
namespace PaperSyndromeInstance
open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.PhysicalColumnOrder GapCVP.PhysicalWordSoundness
end PaperSyndromeInstance
namespace Factor400BinaryDecodingPhysicalWordSourceTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.Factor400BinaryDecodingPromiseReduction GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.GaussianPackedStateTargetAtomTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianPhysicalWordReducedAtomTM GapCVP.Factor400BinaryEffectiveBasisSerializerTM
end Factor400BinaryDecodingPhysicalWordSourceTM
namespace PaperBinaryCodingTM
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPhysicalWordSourceTM GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.PhysicalColumnOrder GapCVP.CanonicalMatrixShape
open GapCVP.CanonicalPhysicalMatrixShape GapCVP.CanonicalSourceCatalogue
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
open GapCVP.PaperSyndromeInstance GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.OutputBoundedDependentRecordFold
end PaperBinaryCodingTM
namespace Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal
open GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness GapCVP.OriginalThreeSATNPHardness
open GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.PhysicalColumnOrder
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceConsistencyBridge
open GapCVP.PaperBinaryCodingTM GapCVP.PaperSyndromeInstance
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceWholeOutputAssemblyTM
end Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal
namespace Factor400FinitePNormPromiseReduction
open scoped BigOperators
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryInstanceBridge
end Factor400FinitePNormPromiseReduction
namespace Factor400FinitePRadiusBounds
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePRadiusArithmetic
end Factor400FinitePRadiusBounds
namespace Factor400FinitePNormSourceReduction
open scoped BigOperators
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePNormPromiseReduction
open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.Factor400BinaryDecodingPromiseReduction
end Factor400FinitePNormSourceReduction
namespace Factor400FinitePNormUnconditional
open scoped BigOperators
open GapCVP.Factor400FinitePNormCorollary
end Factor400FinitePNormUnconditional
namespace PaperFinitePNormSourceReduction
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
end PaperFinitePNormSourceReduction
namespace Factor400PaperVariableArityFinitePNormUnconditional
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
end Factor400PaperVariableArityFinitePNormUnconditional
namespace PaperNearestAffineGeneric
open scoped BigOperators
open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness
end PaperNearestAffineGeneric
namespace PaperNearestInstance
open GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.PhysicalColumnOrder GapCVP.PhysicalWordSoundness
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.PaperNearestAffineGeneric
end PaperNearestInstance
namespace Factor400BinaryDecodingPhysicalWordGaussianPayloadTM
open Turing GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.BinaryStructuralRecordTM GapCVP.BinaryGaussianStructuralRecordIndex
open GapCVP.Factor400BinaryEffectiveBasisSerializerTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
end Factor400BinaryDecodingPhysicalWordGaussianPayloadTM
namespace PaperNearestIntegerTargetAtom
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPhysicalWordSourceTM
open GapCVP.GaussianPhysicalWordRankIndexTM
open GapCVP.Factor400BinaryCompactPhysicalGaussianOutputSerializerTM GapCVP.CanonicalMatrixShape
open GapCVP.BinaryStructuralRecordTM
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianOutputSerializerTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.SourceWholeOutputAssemblyTM
end PaperNearestIntegerTargetAtom
namespace PaperNearestStructuralAtom
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.CLStructuralAtomicNaturalWriter
open GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPhysicalWordSourceTM
open GapCVP.Factor400BinaryDecodingPhysicalWordGaussianPayloadTM GapCVP.BinaryStructuralRecordTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryGaussianStructuralAtomTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianPackedStateBasisAtomTM
open GapCVP.Factor400BinaryCompactPhysicalGaussianOutputSerializerTM GapCVP.CanonicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianOutputSerializerTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.PaperBinaryCodingTM GapCVP.PaperNearestInstance GapCVP.PaperNearestIntegerTargetAtom
end PaperNearestStructuralAtom
namespace PaperNearestGaussianPayloadTM
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPhysicalWordGaussianPayloadTM GapCVP.CanonicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.BinaryStructuralRecordTM GapCVP.GaussianSourceInitializerInstantiation
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianOutputSerializerTM
open GapCVP.PaperBinaryCodingTM GapCVP.PaperNearestAffineGeneric GapCVP.PaperNearestInstance
open GapCVP.PaperNearestStructuralAtom
end PaperNearestGaussianPayloadTM
namespace PaperNearestRoutedSource
open GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness GapCVP.OriginalThreeSATNPHardness
open GapCVP.CanonicalPhysicalMatrixShape GapCVP.PhysicalColumnOrder
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceConsistencyBridge
open GapCVP.PaperNearestInstance GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceWholeOutputAssemblyTM
end PaperNearestRoutedSource
namespace Factor400PaperVariableArityNearestUnconditional
open GapCVP.Factor400BinaryDecodingPromiseHardness GapCVP.OriginalThreeSATNPHardness
open GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.PaperNearestGaussianPayloadTM GapCVP.PaperNearestRoutedSource
end Factor400PaperVariableArityNearestUnconditional
noncomputable section
open scoped BigOperators
namespace Comparator
export GapCVP.BinaryEncoding
  (lengthPrefixedWord
   readUnaryPrefix
   readUnaryPrefix_replicate
   readLengthPrefixedWord
   readLengthPrefixedWord_append
   encodeAtomic
   readAtomic
   readAtomic_append
   encodeFinValues
   readFinValues
   readFinValues_append
   encodeMatrixRows
   readMatrixRows
   readMatrixRows_append)
export GapCVP (BitLanguage bitEncoding pairBitEncoding IsNP)
private theorem isNPHardPromise_of_original
    {problem : PromiseProblem} {original : GapCVP.PromiseProblem}
    (hyes : ∀ bits, problem.yes bits ↔ original.yes bits)
    (hno : ∀ bits, problem.no bits ↔ original.no bits)
    (hard : GapCVP.NPHardPromise original) :
    IsNPHardPromise problem := by
  simp only [IsNPHardPromise, decide_eq_true_eq]
  intro language hnp
  have original_hnp : GapCVP.IsNP language := hnp
  have original_hard :
      ∀ language : GapCVP.BitLanguage,
        GapCVP.IsNP language →
          Nonempty (GapCVP.PromiseReduction language original) := by
    simpa only [GapCVP.NPHardPromise, decide_eq_true_eq] using hard
  obtain ⟨reduction⟩ := original_hard language original_hnp
  exact ⟨{
    map := reduction.map
    polynomial_time := reduction.polynomial_time
    completeness := fun input hinput =>
      (hyes _).mpr (reduction.completeness input hinput)
    soundness := fun input hinput =>
      (hno _).mpr (reduction.soundness input hinput)
  }⟩
end Comparator
end
end GapCVP
end
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
theorem _root_.solution (p : ℚ) (hp : 1 ≤ p) :
    IsNPHardPromise (finitePGapCVPPromise p hp) :=
  isNPHardPromise_of_original
    (finiteP_yes_iff_original p hp)
    (finiteP_no_iff_original p hp)
    (GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePNPHardPromise
      p hp)
end GapCVP.Comparator
