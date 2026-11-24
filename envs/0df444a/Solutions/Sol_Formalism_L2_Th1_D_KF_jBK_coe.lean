-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.jBK_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:00.425815+00:00
-- url     : https://prove2.me/submissions/0c9be17b-5b6b-46a0-a4e2-9ee7dcde5862

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
open KF
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
variable (σ0 : ringA l →+* ringA l) (hiso : ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖)
set_option maxHeartbeats 800000
namespace Formalism.L2.Th1.D.KF
theorem _root_.solution (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) (x : ringB l) :
    ((jBK hB x : MaximalUnramifiedExtension l) : ℂ_[l]) = x := by
  exact RingHom.codRestrict_apply _ _ _ x
end Formalism.L2.Th1.D.KF
