-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParE.ParE_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:03.310145+00:00
-- url     : https://prove2.me/submissions/6b5d6b14-44da-4cc4-81b5-de19166433d3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Theorems.Thm_P2M_Formalism_L2_Th1_B_ParE_integral_sub__1fc90a44e6f2
import Theorems.Thm_P2M_Formalism_L2_Th1_B_ParE_integral_C__792a83f5671c
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_B_integral_series_at_variable
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
section Alg
variable {K : Type} [Field K] [CharZero K] {ι : Type}
end Alg
private theorem cc_subst_lemma {R : Type*} [CommRing R] {τ : Type*} {a : MvPowerSeries τ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha), map_mul, ha, zero_mul]
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type}
end Norm
end Formalism.L2.Th1.B.ParE
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
namespace Formalism.L2.Th1.B.ParE
theorem _root_.solution (hF : ParEFormula) (hL : SimeqLog) : ParE := by
  intro K _ _ _ A kap e1 s2 w l i F hW hLL hI hk hInt
  rw [hF K A kap e1 s2 w l i F hW hLL hI]
  refine (hL K (Fin 2) _ ?_ ?_).2
  · have hs : MvPowerSeries.constantCoeff (PowerSeries.subst l w) = 0 :=
      cc_subst_lemma hLL.2.2.1 hW.1
    have h0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (at1 x (PowerSeries.subst l w)) = 0 := by
      intro x
      unfold at1
      exact cc_subst_lemma (MvPowerSeries.constantCoeff_X x) hs
    rw [map_sub, map_one, map_mul, map_mul, h0 0, h0 1]
    simp
  · exact integral_sub' integral_one' (integral_mul' (integral_mul' (integral_C' hk)
      (integral_series_at_variable 0 _ hInt)) (integral_series_at_variable 1 _ hInt))
end Formalism.L2.Th1.B.ParE
