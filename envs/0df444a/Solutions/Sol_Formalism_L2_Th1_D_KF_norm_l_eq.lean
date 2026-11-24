-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.norm_l_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:55:56.167796+00:00
-- url     : https://prove2.me/submissions/1298a1a4-8610-4d24-9b8b-6cafa0f1bd83

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion

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
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]
namespace Formalism.L2.Th1.D.KF
theorem _root_.solution : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h1 : (((l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [← h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  first
    | exact Padic.norm_p
    | simp [Padic.norm_p]
end Formalism.L2.Th1.D.KF
