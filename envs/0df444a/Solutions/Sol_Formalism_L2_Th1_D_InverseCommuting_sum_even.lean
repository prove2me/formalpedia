-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.sum_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:52.902802+00:00
-- url     : https://prove2.me/submissions/2cd09df5-da63-4a6a-96ab-4d8a15525a6f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D.InverseCommuting
variable {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.InverseCommuting
theorem _root_.solution {M : Type} [AddCommMonoid M] (f : ZMod d → M) :
    (∑ s : ZMod d, if s.val % 2 = 0 then f s else 0) =
      ∑ s : {s : ZMod d // s.val % 2 = 0}, f s.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) f
end Formalism.L2.Th1.D.InverseCommuting
