-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.l_inv_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:56:02.741874+00:00
-- url     : https://prove2.me/submissions/267d04b4-97cd-482c-bff6-aa59358e503b

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
theorem _root_.solution : (l : ℝ)⁻¹ < 1 := by
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
end Formalism.L2.Th1.D.KF
