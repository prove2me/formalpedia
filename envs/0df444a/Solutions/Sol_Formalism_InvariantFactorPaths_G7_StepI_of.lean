-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StepI_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:38.833037+00:00
-- url     : https://prove2.me/submissions/e6fb8f29-c0e6-492d-a394-be7438cec11d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_norm_coeff_dlgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_sq_modEq_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_powq_modEq_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_not_one_modEq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_product_single_variables


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
theorem _root_.solution (h1 : LemmaOne) (hF : FirstDeriv) (hC : CobLin) : StepI := by
  intro K _ _ _ _ p σ hU F hLaw G hS hd1 hd2
  have hp : p.Prime := hU.1
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := hU.2.2.1
  have hp2 : 2 ≤ p := hp.two_le
  have hDiv : DivAB G := by
    intro n hn
    by_contra h
    obtain ⟨a, b, -⟩ := hS n h
    omega
  have hFD := hF K p hp hnp F hLaw G hDiv hd1
  have hCL := hC K p hp hnp F hLaw G hDiv hd2
  have hf0 : PowerSeries.constantCoeff (fLin G) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, fLin, PowerSeries.coeff_mk]
    exact hDiv _ (Or.inr (by simp))
  obtain ⟨α, β, R, hα, hR, hf⟩ := h1 K p σ hU F hLaw (fLin G) hf0 hCL
  have key : ∀ j, ‖PowerSeries.coeff j (fLin G) - α * PowerSeries.coeff j (g0F K p)‖ ≤ 1 := by
    intro j
    by_cases hj : j ≡ p [MOD p ^ 2 - 1]
    · have hl : PowerSeries.coeff j (lgF K p) = 0 := by
        by_contra h
        obtain ⟨i, rfl⟩ := coeff_lgF_ne_zero h
        exact not_one_modEq hp2 ((powq_modEq_one hp2 i).symm.trans hj)
      have e : PowerSeries.coeff j (fLin G) - α * PowerSeries.coeff j (g0F K p) =
          PowerSeries.coeff j R := by
        rw [hf]
        simp only [map_add, PowerSeries.coeff_C_mul, hl]
        ring
      rw [e]
      exact hR j
    · have hfj : PowerSeries.coeff j (fLin G) = 0 := by
        by_contra h
        rw [fLin, PowerSeries.coeff_mk] at h
        obtain ⟨-, -, hc⟩ := hS _ h
        simp only [Finsupp.add_apply, Finsupp.single_apply] at hc
        simp only [if_true, Fin.isValue, one_ne_zero, zero_ne_one, if_false, add_zero,
          zero_add] at hc
        apply hj
        have h3 : p * 1 ≡ p * (p * j) [MOD p ^ 2 - 1] := hc.mul_left p
        have h4 : p * (p * j) ≡ 1 * j [MOD p ^ 2 - 1] := by
          rw [← mul_assoc, ← sq]
          exact (sq_modEq_one hp2).mul_right j
        simpa using (h3.trans h4).symm
      have hgj : PowerSeries.coeff j (g0F K p) = 0 := by
        by_contra h
        obtain ⟨i, rfl⟩ := coeff_g0F_ne_zero h
        apply hj
        simpa using (powq_modEq_one hp2 i).mul_left p
      rw [hfj, hgj]
      simp
  refine ⟨α, hα, ?_⟩
  intro n
  have e : coeff n (pderiv K 0 G -
        C α * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p))) =
      coeff n (pderiv K 0 G - at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (fLin G)) +
        PowerSeries.coeff (n 0) (PowerSeries.derivative K (lgF K p)) *
          (PowerSeries.coeff (n 1) (fLin G) - α * PowerSeries.coeff (n 1) (g0F K p)) := by
    rw [map_sub, map_sub, coeff_C_mul, coeff_product_single_variables (by decide) (by decide),
      coeff_product_single_variables (by decide) (by decide)]
    ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hFD n) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (norm_coeff_dlgF hp hnp _) (norm_nonneg _) (key _)
end Formalism.InvariantFactorPaths.G7
