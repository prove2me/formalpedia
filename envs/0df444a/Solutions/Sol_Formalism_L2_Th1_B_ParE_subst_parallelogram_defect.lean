-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParE.subst_parallelogram_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:21:19.096272+00:00
-- url     : https://prove2.me/submissions/96d7bf41-a1f6-4fbe-99ea-de9fa8fea7d8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
variable {K : Type} [Field K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B.ParE
theorem _root_.solution (f : PowerSeries K) {U V : MvPowerSeries ι K}
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (par0 f) =
      PowerSeries.subst (U + V) f + PowerSeries.subst (U - V) f - 2 * PowerSeries.subst U f -
        2 * PowerSeries.subst V f := by
  have hb : MvPowerSeries.HasSubst ![U, V] :=
    ⟨fun s => by fin_cases s <;> simp [hU, hV, IsNilpotent.zero], fun _ => Set.toFinite _⟩
  have key : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst ![U, V] (PowerSeries.subst a f) =
        PowerSeries.subst (MvPowerSeries.subst ![U, V] a) f := fun a ha =>
    MvPowerSeries.subst_comp_subst_apply
      (⟨fun _ => by simp [ha, IsNilpotent.zero], fun _ => Set.toFinite _⟩ :
        MvPowerSeries.HasSubst (fun _ : Unit => a)) hb f
  have hX : ∀ s : Fin 2, MvPowerSeries.subst ![U, V] (MvPowerSeries.X s : MvPowerSeries (Fin 2) K) = ![U, V] s :=
    fun s => MvPowerSeries.subst_X hb s
  unfold par0 atS atD at1
  rw [← MvPowerSeries.coe_substAlgHom hb]
  simp only [map_add, map_sub, map_mul, map_ofNat]
  rw [MvPowerSeries.coe_substAlgHom hb, key _ (by simp), key _ (by simp), key _ (by simp), key _ (by simp),
    ← MvPowerSeries.coe_substAlgHom hb]
  simp only [map_add, map_sub]
  rw [MvPowerSeries.coe_substAlgHom hb, hX 0, hX 1]
  simp
end Formalism.L2.Th1.B.ParE
