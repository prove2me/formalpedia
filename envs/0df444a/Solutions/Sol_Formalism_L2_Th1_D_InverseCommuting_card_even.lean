-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.card_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:24.312852+00:00
-- url     : https://prove2.me/submissions/5290c667-a962-486b-8a43-cdc21d5dacd3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_parity_add_one

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
theorem _root_.solution (hd : Even d) : 2 * Fintype.card {s : ZMod d // s.val % 2 = 0} = d := by
  have e : {s : ZMod d // s.val % 2 = 0} ≃ {s : ZMod d // ¬ s.val % 2 = 0} :=
    (Equiv.addRight (1 : ZMod d)).subtypeEquiv (fun s => by
      simp only [Equiv.coe_addRight]
      rw [parity_add_one hd]
      omega)
  have h1 := Fintype.card_congr e
  have h2 := Fintype.card_subtype_compl (fun s : ZMod d => s.val % 2 = 0)
  have h3 := Fintype.card_subtype_le (fun s : ZMod d => s.val % 2 = 0)
  rw [ZMod.card] at h2 h3
  omega
end Formalism.L2.Th1.D.InverseCommuting
