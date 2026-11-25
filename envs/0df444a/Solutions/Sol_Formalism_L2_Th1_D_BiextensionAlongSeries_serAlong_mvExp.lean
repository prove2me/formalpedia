-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionAlongSeries.serAlong_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:34.174809+00:00
-- url     : https://prove2.me/submissions/a7b4841c-eaad-4f04-b2c8-ba92804840d9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RelativeThetaFactorization
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionAlongSeries_hsX
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hsX
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_mvExp__fa9db9cd36a6


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
variable {K : Type} [NormedField K]
namespace Formalism.L2.Th1.D.BiextensionAlongSeries
theorem _root_.solution [CharZero K] {ι κ : Type} [Finite ι] (e : ι → κ) {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) : serAlong e (mvExp f) = mvExp (serAlong e f) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' (hsX e) hf
end Formalism.L2.Th1.D.BiextensionAlongSeries
