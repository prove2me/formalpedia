-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionAlongSeries.serAlong_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:08:18.187919+00:00
-- url     : https://prove2.me/submissions/cf7363df-13ec-4359-8e01-722564832c18

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RelativeThetaFactorization
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionAlongSeries_hsX
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hsX
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog bSum linSub idM ZV serAlong)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionAlongSeries
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.BiextensionAlongSeries
theorem _root_.solution {ι κ μ : Type} [Finite κ] (e : κ → μ) {φ : ι → MvPowerSeries κ K}
    (hφ : HasSubst φ) (f : MvPowerSeries ι K) :
    serAlong e (subst φ f) = subst (fun i => serAlong e (φ i)) f := by
  unfold serAlong
  rw [subst_comp_subst_apply hφ (hsX e)]
end Formalism.L2.Th1.D.BiextensionAlongSeries
