-- Prove2me | solution 1 for Formalism.L2.Th1.D.letter_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:45.281566+00:00
-- url     : https://prove2.me/submissions/18129e91-4649-4ba3-bacd-22484fc96fbc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_shiftType_gLog
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
open KernelCokernelKilling
namespace Formalism.L2.Th1.D
theorem _root_.solution : LetterShift := by
  unfold LetterShift
  intro K _ _ _ l d _ σ hl
  refine ⟨fun b => ?_, ?_, fun N0 N1 a b => ?_⟩
  · exact shiftType_gLog (K := K) hl σ (fun s : ZMod d => (b, s))
  · exact shiftType_gLog (K := K) hl σ (fun s : ZMod d => s)
  · exact shiftType_gLog (K := K) hl σ (fun s : ZMod d => ((s, a, b) : ZMod d × Fin N0 × Fin N1))
end Formalism.L2.Th1.D
