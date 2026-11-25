-- Prove2me | solution 1 for Formalism.L2.Th1.B.formal_halving_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:51:14.373041+00:00
-- url     : https://prove2.me/submissions/6bce6735-638b-455d-b200-117654f58c35

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_L2_Th1_B_law_constantCoeff_subst2
import Theorems.Thm_Formalism_L2_Th1_B_law_subst
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_X
import Theorems.Thm_Formalism_L2_Th1_B_law_c0X
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_one_subst
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_integralInverse_statement
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9


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
theorem _root_.solution : HalfExists := by
  intro K _ _ _ F l h h2
  obtain ⟨hF, hFi, hl0, hl1, -⟩ := id h
  have hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
  have two0 : (2 : K) ≠ 0 := two_ne_zero
  let D : PowerSeries K := MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), PowerSeries.X] F
  have hD0 : PowerSeries.constantCoeff D = 0 := law_constantCoeff_subst2 F hF _ _ hX hX
  have hDi : Integral (ι := Unit) D :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun k => by fin_cases k <;> exact law_c0X)
      (fun k => by fin_cases k <;> exact law_integral_X ()) hFi
  have eX : PowerSeries.subst (PowerSeries.X : PowerSeries K) l = l := PowerSeries.X_subst l
  have hD1 : PowerSeries.coeff 1 D = 2 := by
    have e := law_subst h (PowerSeries.X : PowerSeries K) PowerSeries.X hX hX
    rw [eX] at e
    have e' := congrArg (PowerSeries.coeff 1) e
    rw [law_coeff_one_subst l D hD0, map_add, hl1] at e'
    linear_combination e'
  obtain ⟨X', hX0, hXi, hXT, -⟩ := Formalism.HermitianLattices.ExpSeriesBivariate.integralInverse_statement K Unit (fun _ => D)
    (Matrix.of fun _ _ => (2 : K)⁻¹) (fun _ => hD0) (fun _ => hDi)
    (fun _ _ => by rw [Matrix.of_apply, norm_inv, h2, inv_one])
    (by
      ext i j
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.of_apply,
        Matrix.one_apply]
      have : MvPowerSeries.coeff (Finsupp.single (default : Unit) 1) D = 2 := hD1
      rw [this, mul_inv_cancel₀ two0, if_pos trivial])
  have hsX : MvPowerSeries.HasSubst X' := MvPowerSeries.hasSubst_of_constantCoeff_zero hX0
  let g : PowerSeries K := X' ()
  have hg0 : PowerSeries.constantCoeff g = 0 := hX0 ()
  have e1 : MvPowerSeries.subst ![g, g] F = (PowerSeries.X : PowerSeries K) := by
    have := hXT ()
    rw [subst2_subst F hX hX hsX] at this
    have eg : MvPowerSeries.subst X' (PowerSeries.X : PowerSeries K) = g :=
      MvPowerSeries.subst_X hsX ()
    rw [eg] at this
    exact this
  refine ⟨g, hg0, hXi (), ?_⟩
  have e3 := law_subst h g g hg0 hg0
  rw [e1, eX] at e3
  have hC : (PowerSeries.C (2 : K)⁻¹ : PowerSeries K) * 2 = 1 := by
    have : (2 : PowerSeries K) = PowerSeries.C (2 : K) := (map_ofNat PowerSeries.C 2).symm
    rw [this, ← map_mul, inv_mul_cancel₀ two0, map_one]
  linear_combination (-(PowerSeries.C (2 : K)⁻¹ : PowerSeries K)) * e3 +
    (-(PowerSeries.subst g l : PowerSeries K)) * hC
end Formalism.L2.Th1.B
