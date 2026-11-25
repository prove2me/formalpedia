-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionAlongSeries.cc_serAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:27:21.833516+00:00
-- url     : https://prove2.me/submissions/145ad1b6-ae34-46ff-a4a4-bfffaabfa201

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RelativeThetaFactorization
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionAlongSeries_hsX
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionAlongSeries_cc_serAlong
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hsX
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



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
theorem _root_.solution {ι κ : Type} [Finite ι] (e : ι → κ) (f : MvPowerSeries ι K) :
    constantCoeff (serAlong e f) = constantCoeff f := by
  have h : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  conv_lhs => rw [h]
  unfold serAlong
  rw [subst_add (hsX e), subst_C, map_add, constantCoeff_C]
  have := cc_serAlong e h0
  unfold serAlong at this
  rw [this, add_zero]
end Formalism.L2.Th1.D.BiextensionAlongSeries
