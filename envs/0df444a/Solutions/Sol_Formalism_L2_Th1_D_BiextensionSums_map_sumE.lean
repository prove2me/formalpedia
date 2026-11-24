-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionSums.map_sumE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:47.878822+00:00
-- url     : https://prove2.me/submissions/371ffbcd-c4a2-4922-8d55-dac537e6c0c1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums
namespace Formalism.L2.Th1.D.BiextensionSums
theorem _root_.solution {K0 K ι : Type} [Field K0] [Field K] [Fintype ι] {N0 N1 : ℕ} (j : K0 →+* K)
    (be : MvPowerSeries (Fin 2) K0) :
    map j (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = sumE (map j be) := by
  unfold sumE
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_subst (hasSubst_of_constantCoeff_zero (by intro a; simp))]
  simp only [map_X]
end Formalism.L2.Th1.D.BiextensionSums
