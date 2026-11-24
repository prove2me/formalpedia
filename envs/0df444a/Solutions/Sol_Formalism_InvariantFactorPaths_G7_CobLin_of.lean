-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CobLin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:21.039293+00:00
-- url     : https://prove2.me/submissions/fd9ad2f2-b660-44ef-a1bc-04f49dce3095

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs3
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_subst2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_identity_two_vars
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_subst2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_zero_left
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_zero_pderiv
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_constantCoeff_law_first_two_of_three
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_lin

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
theorem _root_.solution (_hL : LawSymm) : CobLin := by
  intro K _ _ _ p _ _ F hF G hG hS
  obtain ⟨hF0, -, -⟩ := hF
  obtain ⟨hD0, hDi⟩ := hS
  rw [sub_zero] at hD0 hDi
  have hX : ∀ {τ : Type} (x : τ), constantCoeff (X x : MvPowerSeries τ K) = 0 := fun x => by simp
  have he : HasSubst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] :=
    hs3 (hX 0) (hX 1) (map_zero _)
  have hx2 : subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (X 2 : MvPowerSeries (Fin 3) K) = 0 :=
    subst_X he 2

  have term : ∀ w : MvPowerSeries (Fin 3) K, constantCoeff w = 0 → pderiv K 2 w = 0 →
      subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (subst ![w, X 2] (swap2 G)) = 0 ∧
      subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (pderiv K 2 (subst ![w, X 2] (swap2 G))) =
        PowerSeries.subst (subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] w) (fLin G) := by
    intro w hw hdw
    have hs := hs2 hw (hX (2 : Fin 3))
    have hw' : constantCoeff (subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] w) = 0 :=
      constantCoeff_subst_eq_zero he (fun i => by fin_cases i <;> simp) hw
    have hs' := hs2 hw' (map_zero (constantCoeff (σ := Fin 2) (R := K)))
    constructor
    · rw [subst_subst2 he hs, hx2, subst_swap2 hs', subst_zero_left hG hw']
    · rw [pderiv_subst2 hs, hdw, pderiv_X_self, mul_zero, mul_one, zero_add, subst_subst2 he hs,
        hx2, pderiv_swap2, subst_swap2 hs', subst_zero_pderiv G hw']
  have hdF : pderiv K 2 (in3 F) = 0 := by
    unfold in3
    rw [pderiv_subst2 HasSubst.X_X, pderiv_X_of_ne (by decide), pderiv_X_of_ne (by decide),
      mul_zero, mul_zero, add_zero]
  obtain ⟨a1, b1⟩ := term (in3 F) (constantCoeff_law_first_two_of_three hF0) hdF
  obtain ⟨a2, b2⟩ := term (X 0) (hX 0) (pderiv_X_of_ne (by decide))
  obtain ⟨a3, b3⟩ := term (X 1) (hX 1) (pderiv_X_of_ne (by decide))
  have hA : subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (d1 F (swap2 G)) = 0 := by
    unfold d1
    rw [subst_sub he, subst_sub he, a1, a2, a3]
    simp
  have hI := integral_lin hD0 hDi (b := ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0])
    (fun i => by fin_cases i <;> simp)
    (fun i => by
      fin_cases i
      · exact integral_X 0
      · exact integral_X 1
      · exact integral_zero) hA 2
  have hE : subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (in3 F) = F := by
    unfold in3
    rw [subst_subst2 he HasSubst.X_X, subst_X he, subst_X he]
    exact subst_identity_two_vars F
  have hC : subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (pderiv K 2 (d1 F (swap2 G))) =
      cob F (fLin G) := by
    unfold d1 cob
    rw [map_sub, map_sub, subst_sub he, subst_sub he, b1, b2, b3, hE, subst_X he, subst_X he]
    rfl
  rw [← hC]
  exact hI
end Formalism.InvariantFactorPaths.G7
