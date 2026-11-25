-- Prove2me | solution 1 for Formalism.L2.Th1.B.formal_inverse_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:39:31.92812+00:00
-- url     : https://prove2.me/submissions/2d11286b-39f0-4abc-9051-6251fcbe8d9b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_L2_Th1_B_law_subst
import Theorems.Thm_Formalism_L2_Th1_B_law_subst_zero
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_single
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_X
import Theorems.Thm_Formalism_L2_Th1_B_law_c0X
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_zero
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hb0
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
theorem _root_.solution : InvExists := by
  intro K _ _ _ F l h
  obtain ⟨hF, hFi, hl0, hl1, -⟩ := id h
  let T : Fin 2 → MvPowerSeries (Fin 2) K := ![MvPowerSeries.X 0, F]
  let J' : Matrix (Fin 2) (Fin 2) K := !![1, 0; -1, 1]
  obtain ⟨X', hX0, hXi, hXT, -⟩ := Formalism.HermitianLattices.ExpSeriesBivariate.integralInverse_statement K (Fin 2) T J'
    (fun i => by fin_cases i <;> simp [T, hF])
    (fun i => by
      fin_cases i
      · exact law_integral_X 0
      · exact hFi)
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [J'])
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [T, J', Matrix.mul_apply, Fin.sum_univ_two, law_coeff_single h,
          MvPowerSeries.coeff_X, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)])
  have hsX : MvPowerSeries.HasSubst X' := MvPowerSeries.hasSubst_of_constantCoeff_zero hX0
  have e0 : X' 0 = MvPowerSeries.X 0 := by
    have := hXT 0
    simpa [T, MvPowerSeries.subst_X hsX] using this
  have e1 : MvPowerSeries.subst X' F = MvPowerSeries.X 1 := hXT 1
  have hb : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries K), 0] := Formalism.G.LogP.hb0
  let i : PowerSeries K := MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0] (X' 1)
  have hi0 : PowerSeries.constantCoeff i = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hb
      (fun k => by
        fin_cases k
        · exact law_c0X
        · exact map_zero _) (hX0 1)
  have hii : Integral (ι := Unit) i :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst'
      (fun k => by
        fin_cases k
        · exact law_c0X
        · exact map_zero _)
      (fun k => by
        fin_cases k
        · exact law_integral_X ()
        · exact law_integral_zero) (hXi 1)
  have e2 : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), i] F = 0 := by
    have := congrArg (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0]) e1
    rw [MvPowerSeries.subst_comp_subst_apply hsX hb, MvPowerSeries.subst_X hb] at this
    have this' : _ = (0 : PowerSeries K) := this
    rw [← this']
    congr 1
    funext k
    fin_cases k
    · show _ = MvPowerSeries.subst _ (X' 0)
      rw [e0, MvPowerSeries.subst_X hb]
      rfl
    · rfl
  refine ⟨i, hi0, hii, ?_⟩
  have e3 := law_subst h (PowerSeries.X : PowerSeries K) i law_c0X hi0
  rw [e2, law_subst_zero l hl0] at e3
  have e4 : PowerSeries.subst (PowerSeries.X : PowerSeries K) l = l := PowerSeries.X_subst l
  rw [e4] at e3
  linear_combination -e3
end Formalism.L2.Th1.B
