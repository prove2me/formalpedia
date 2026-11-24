-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionSums.linSub_idM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:01.575776+00:00
-- url     : https://prove2.me/submissions/82939f05-8800-4f2b-8f87-73ba92afd08f

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
theorem _root_.solution {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] :
    linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) = X := by
  funext x
  unfold linSub idM
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    rw [if_neg (Ne.symm hy)]
    simp
  · simp
end Formalism.L2.Th1.D.BiextensionSums
