-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.iter_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:30.956581+00:00
-- url     : https://prove2.me/submissions/db88a533-5fb7-40da-864a-310f7810ec48

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
namespace Formalism.L2.Th1.D.InverseCommuting
theorem _root_.solution {α : Type} {f : α → α} {c : α} (h : f (f c) = c) {k : ℕ} (hk : k % 2 = 0) :
    f^[k] c = c := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
  rw [Function.iterate_mul]
  exact Function.iterate_fixed h m
end Formalism.L2.Th1.D.InverseCommuting
