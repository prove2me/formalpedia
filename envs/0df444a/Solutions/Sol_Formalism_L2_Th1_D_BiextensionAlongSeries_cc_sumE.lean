-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionAlongSeries.cc_sumE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:13.791827+00:00
-- url     : https://prove2.me/submissions/78b90424-9607-4cb6-8ef6-b312b883a78b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RelativeThetaFactorization
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
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
theorem _root_.solution {ι : Type} [Fintype ι] {N0 N1 : ℕ} {be : MvPowerSeries (Fin 2) K}
    (h : constantCoeff be = 0) :
    constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = 0 := by
  unfold sumE
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by intro a; simp))
    (by intro a; simp) h
end Formalism.L2.Th1.D.BiextensionAlongSeries
