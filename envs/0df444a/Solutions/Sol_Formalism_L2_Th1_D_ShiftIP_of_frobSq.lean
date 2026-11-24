-- Prove2me | solution 1 for Formalism.L2.Th1.D.ShiftIP_of_frobSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:35:23.6418+00:00
-- url     : https://prove2.me/submissions/57b30f69-e463-41d0-9ca5-1423f95d1d1c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_combo
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
theorem _root_.solution : FrobSq → ShiftIP := by
  intro hF
  unfold ShiftIP
  intro K _ _ _ l d _ σ hU hd τ _ L hL c hc hcd
  have hσ := (hF K l σ hU).2
  have hl0 : l ≠ 0 := hU.1.ne_zero
  constructor
  · have h := combo hl0 σ hσ hd L hL hc hcd (fun x => x = 0)
    unfold linEL
    exact h
  · have h := combo hl0 σ hσ hd L hL hc hcd (fun x => ¬ x = 0)
    unfold linOL
    simpa only [ite_not] using h
end Formalism.L2.Th1.D
