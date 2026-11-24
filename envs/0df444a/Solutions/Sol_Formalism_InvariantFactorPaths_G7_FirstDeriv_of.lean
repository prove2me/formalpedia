-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FirstDeriv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:05.072288+00:00
-- url     : https://prove2.me/submissions/e0328554-955c-4b46-a718-f2e2c3ebdad5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs3
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_subst2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_psubst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_single_variable
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_identity_two_vars
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_subst2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_psubst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_single_self
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_single_of_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_zero_left
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_zero_pderiv
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_constantCoeff_law_first_two_of_three
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_lin
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_single_log_derivative
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_constantCoeff_dlgF
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open GramFrameCompositionLinFacts MvPowerSeries
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hL : LawSymm) : FirstDeriv := by
  intro K _ _ _ p hp hnp F hF G hG hS
  obtain ⟨-, -, -, hF4⟩ := hL K p hp hnp F hF
  obtain ⟨hF0, hFi, hFc⟩ := hF
  obtain ⟨hD0, hDi⟩ := hS
  rw [sub_zero] at hD0 hDi
  have hX : ∀ {τ : Type} (x : τ), constantCoeff (X x : MvPowerSeries τ K) = 0 := fun x => by simp
  have he0 : HasSubst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] :=
    hs3 (hX 0) (map_zero _) (hX 1)
  have hin : HasSubst ![in3 F, (X 2 : MvPowerSeries (Fin 3) K)] :=
    hs2 (constantCoeff_law_first_two_of_three hF0) (hX 2)

  have hE : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (in3 F) = X 0 := by
    unfold in3
    rw [subst_subst2 he0 HasSubst.X_X, subst_X he0, subst_X he0]
    exact hF4
  have hx0 : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (X 0 : MvPowerSeries (Fin 3) K) = X 0 :=
    subst_X he0 0
  have hx1 : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (X 1 : MvPowerSeries (Fin 3) K) = 0 :=
    subst_X he0 1
  have hx2 : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (X 2 : MvPowerSeries (Fin 3) K) = X 1 :=
    subst_X he0 2
  have hA : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (d1 F G) = 0 := by
    unfold d1
    rw [subst_sub he0, subst_sub he0, subst_subst2 he0 hin, subst_subst2 he0 HasSubst.X_X,
      subst_subst2 he0 HasSubst.X_X, hE, hx0, hx1, hx2, subst_zero_left hG (hX 1)]
    simp
  have hI := integral_lin hD0 hDi (b := ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1])
    (fun i => by fin_cases i <;> simp)
    (fun i => by
      fin_cases i
      · exact integral_X 0
      · exact integral_zero
      · exact integral_X 1) hA 1

  set φ : MvPowerSeries (Fin 2) K :=
    subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (pderiv K 1 (in3 F)) with hφ
  have hφ' : φ = subst ![(X 0 : MvPowerSeries (Fin 2) K), 0] (pderiv K 1 F) := by
    rw [hφ]
    unfold in3
    rw [pderiv_subst2 HasSubst.X_X, pderiv_X_self, pderiv_X_of_ne (by decide), mul_zero, mul_one,
      zero_add, subst_subst2 he0 HasSubst.X_X, hx0, hx1]
  have hC : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (pderiv K 1 (d1 F G)) =
      pderiv K 0 G * φ - at1 1 (fLin G) := by
    unfold d1
    rw [map_sub, map_sub, pderiv_subst2 hin, pderiv_subst2 HasSubst.X_X,
      pderiv_subst2 HasSubst.X_X, pderiv_X_self, pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide),
      pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
    simp only [mul_zero, add_zero, sub_zero, mul_one]
    rw [subst_sub he0, subst_mul he0, subst_subst2 he0 hin, subst_subst2 he0 HasSubst.X_X, hE, hx1,
      hx2, subst_identity_two_vars, subst_zero_pderiv G (hX 1)]
    rfl
  have hs0 : HasSubst ![(X 0 : MvPowerSeries (Fin 2) K), 0] := HasSubst.X_zero
  have hlφ : at1 0 (PowerSeries.derivative K (lgF K p)) * φ = 1 := by
    have h1 := congrArg (pderiv K 1) hFc
    unfold cob at h1
    rw [map_sub, map_sub, map_zero, pderiv_single_self, pderiv_single_of_ne (by decide), sub_zero,
      pderiv_psubst (PowerSeries.HasSubst.of_constantCoeff_zero hF0), sub_eq_zero] at h1
    have h2 := congrArg (subst ![(X 0 : MvPowerSeries (Fin 2) K), 0]) h1
    rw [subst_mul hs0, subst_psubst hs0 (PowerSeries.HasSubst.of_constantCoeff_zero hF0), hF4,
      ← hφ', subst_single_variable hs0] at h2
    rw [at1, h2]
    change PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) _ = 1
    rw [PowerSeries.subst_zero_eq_C_constantCoeff, constantCoeff_dlgF hp.two_le]
    simp
  have hfin : pderiv K 0 G - at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (fLin G) =
      at1 0 (PowerSeries.derivative K (lgF K p)) * (pderiv K 0 G * φ - at1 1 (fLin G)) := by
    linear_combination (-(pderiv K 0 G)) * hlφ
  rw [hfin, ← hC]
  exact LogarithmEquivalence.integral_mul' (integral_single_log_derivative hp hnp 0) hI
end Formalism.InvariantFactorPaths.G7
