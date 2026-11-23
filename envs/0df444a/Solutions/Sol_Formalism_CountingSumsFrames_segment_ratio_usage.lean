-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_ratio_usage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:14.74697+00:00
-- url     : https://prove2.me/submissions/7d695a88-986f-47ba-bad4-9452504f5cb7

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_binomial_ratio_exp_bound

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
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : UseSegRatio := by
  intro r s A0 A C i Cp a L P ha hP hKP hCCp hCpL hlo
  have hCCp' : (C i : ℝ) ≤ Cp := by exact_mod_cast hCCp
  have hLP : 0 ≤ L / P := by linarith
  have hL : 0 ≤ L := by
    have := mul_nonneg hLP hP.le
    rwa [div_mul_cancel₀ _ hP.ne'] at this
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hE1 : 1 ≤ Real.exp (((r : ℝ) + 1) * L / a) := Real.one_le_exp (by positivity)
  have key : (dimPol r Cp : ℝ) ≤ Real.exp (((r : ℝ) + 1) * L / a) * dimPol r (C i) := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa [dimPol] using hE1
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have haP : ((r : ℝ) + 1) ^ 2 ≤ a / P := by rw [le_div_iff₀ hP]; exact hKP
      have hlo' : 0 < a / P - ((r : ℝ) + 1) := by nlinarith
      have hC0 : (0 : ℝ) < C i := by linarith
      have hC1 : 1 ≤ C i := by exact_mod_cast hC0
      refine (binomial_ratio_exp_bound r (C i) Cp hC1 hCCp).trans ?_
      have harg : (r : ℝ) * ((Cp : ℝ) - C i) / C i ≤ ((r : ℝ) + 1) * L / a := by
        rw [div_le_div_iff₀ hC0 ha]
        have m1 : (r : ℝ) * (L / P) * a ≤ ((r : ℝ) + 1) * L * (a / P - ((r : ℝ) + 1)) := by
          have g1 : (r : ℝ) * (L / P) * a = (r : ℝ) * L * a / P := by ring
          have g2 : ((r : ℝ) + 1) * L * (a / P - ((r : ℝ) + 1)) =
              ((r : ℝ) + 1) * L * (a - ((r : ℝ) + 1) * P) / P := by field_simp
          rw [g1, g2]
          apply div_le_div_of_nonneg_right _ hP.le
          nlinarith [mul_nonneg hL (sub_nonneg.mpr hKP)]
        calc (r : ℝ) * ((Cp : ℝ) - C i) * a ≤ (r : ℝ) * (L / P) * a := by gcongr; linarith
          _ ≤ ((r : ℝ) + 1) * L * (a / P - ((r : ℝ) + 1)) := m1
          _ ≤ ((r : ℝ) + 1) * L * C i := by gcongr
      gcongr
  generalize Real.exp (((r : ℝ) + 1) * L / a) = E at *
  unfold dimMM
  push_cast
  have hprod : ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (Function.update C i Cp j)) ≤
      ∏ j, ((if j = i then E else 1) * ((dimPol r (A j) : ℝ) * dimPol r (C j))) := by
    apply Finset.prod_le_prod
    · intro j _; positivity
    · intro j _
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, if_true]
        calc (dimPol r (A j) : ℝ) * dimPol r Cp ≤ (dimPol r (A j) : ℝ) * (E * dimPol r (C j)) := by
              gcongr
          _ = E * ((dimPol r (A j) : ℝ) * dimPol r (C j)) := by ring
      · simp [hj]
  have e : ∏ j, ((if j = i then E else 1) * ((dimPol r (A j) : ℝ) * dimPol r (C j))) =
      E * ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (C j)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  rw [e] at hprod
  calc (dimPol r A0 : ℝ) * ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (Function.update C i Cp j))
      ≤ (dimPol r A0 : ℝ) * (E * ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (C j))) := by gcongr
    _ = E * ((dimPol r A0 : ℝ) * ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (C j))) := by ring
end Formalism.CountingSumsFrames
