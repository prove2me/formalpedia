-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.parity_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:39:00.833347+00:00
-- url     : https://prove2.me/submissions/6fc96420-8cb9-421c-bef8-9196dc8a1316

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
theorem _root_.solution (hd : Even d) (s : ZMod d) : (s + 1).val % 2 = (s.val + 1) % 2 := by
  have h2 : 2 ∣ d := hd.two_dvd
  have hd2 : 2 ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne d)) h2
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_mod_of_dvd _ h2, Nat.mod_eq_of_lt hd2]
end Formalism.L2.Th1.D.InverseCommuting
