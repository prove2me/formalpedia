-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.frobenius_extension_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:56:01.935872+00:00
-- url     : https://prove2.me/submissions/f8d28025-b3f9-44ba-a986-aec3df626987

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
namespace Formalism.L2.Th1.D.KF
theorem _root_.solution : Continuous (sig1 σ0 hiso) :=
  (uniformContinuous_uniformly_extend (incAB_unif l) (incAB_dense l) (sigF_unif σ0 hiso)).continuous
end Formalism.L2.Th1.D.KF
