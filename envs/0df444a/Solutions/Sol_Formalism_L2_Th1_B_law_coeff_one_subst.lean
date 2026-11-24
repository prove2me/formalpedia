-- Prove2me | solution 1 for Formalism.L2.Th1.B.law_coeff_one_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:22:00.676778+00:00
-- url     : https://prove2.me/submissions/730846fb-6e6c-4e02-ac8e-32c33d2a4146

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective)
namespace Formalism.L2.Th1.B
theorem _root_.solution {K : Type} [Field K] (l D : PowerSeries K)
    (hD : PowerSeries.constantCoeff D = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst D l : PowerSeries K) =
      PowerSeries.coeff 1 l * PowerSeries.coeff 1 D := by
  have hs : PowerSeries.HasSubst D := PowerSeries.HasSubst.of_constantCoeff_zero' hD
  have key : ∀ g : PowerSeries K, PowerSeries.coeff 1 g =
      PowerSeries.constantCoeff (PowerSeries.derivative K g) := by
    intro g
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  have hc : ∀ g : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.subst D g : PowerSeries K) =
      PowerSeries.constantCoeff g := by
    intro g
    have e : g = PowerSeries.C (PowerSeries.constantCoeff g) +
        (g - PowerSeries.C (PowerSeries.constantCoeff g)) := by ring
    conv_lhs => rw [e]
    rw [PowerSeries.subst_add hs, map_add, PowerSeries.subst_C]
    have := PowerSeries.constantCoeff_subst_eq_zero (a := D) hD
      (g - PowerSeries.C (PowerSeries.constantCoeff g)) (by simp)
    erw [this, add_zero]
    exact MvPowerSeries.constantCoeff_C _
  rw [key, PowerSeries.derivative_subst hs, map_mul, hc, ← key, ← key]
end Formalism.L2.Th1.B
