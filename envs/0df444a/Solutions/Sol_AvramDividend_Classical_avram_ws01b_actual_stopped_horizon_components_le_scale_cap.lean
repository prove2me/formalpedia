-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_stopped_horizon_components_le_scale_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T14:12:07.833546+00:00
-- url     : https://prove2.me/submissions/a87a4c2f-3884-44bc-94a6-fc90bcebcf4c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_surviving_horizon_reserve_strip
import Theorems.Thm_AvramDividend_Classical_two_sided_up_exit_hits_level_of_no_positive_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Actual upper-exit plus surviving-horizon killed reward is uniformly capped by Wq(a). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (ω : Ω) :
    (let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
     let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
     (if U < D ∧ U.toNNReal ≤ T then
       Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
     (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
       Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else 0)) ≤ W a := by
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  change (if U < D ∧ U.toNNReal ≤ T then
      Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
     else 0) + (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
      Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
     else 0) ≤ W a
  have hcap : 0 ≤ W a := hW.2.1 a (le_of_lt ha)
  by_cases hA : U < D ∧ U.toNNReal ≤ T
  · have hUfin : U < ⊤ := lt_of_lt_of_le hA.1 le_top
    have hCoe : (U.toNNReal : ℝ≥0∞) = U :=
      ENNReal.coe_toNNReal (ne_of_lt hUfin)
    have hUT : U ≤ (T : ℝ≥0∞) := by
      rw [← hCoe]
      exact ENNReal.coe_le_coe.mpr hA.2
    have hNotB : ¬ ((T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D) := by
      intro hh
      exact (not_lt.mpr hUT) hh.1
    obtain ⟨t, ht, hit⟩ :=
      two_sided_up_exit_hits_level_of_no_positive_jumps
        X a x ha hx0 hxa ω hA.1
    have htime : U.toNNReal = t := by
      change (twoSidedExitUpTime X (a-x) ω).toNNReal = t
      rw [← ht]
      simp
    have hValue : W (x + X.X U.toNNReal ω) = W a := by
      rw [htime, hit]
      congr 1
      ring
    have hDisc : Real.exp (-(q * (U.toNNReal : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hp : 0 ≤ q * (U.toNNReal : ℝ) :=
        mul_nonneg (le_of_lt hq) (by positivity)
      linarith
    simpa only [if_pos hA, if_neg hNotB, add_zero, hValue, one_mul] using
      (mul_le_mul_of_nonneg_right hDisc hcap)
  · by_cases hB : (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D
    · have hStrip := avram_ws01b_true_surviving_horizon_reserve_strip
        X a x T ω hB.1 hB.2
      have h0 := (hStrip T le_rfl).1
      have ha' := (hStrip T le_rfl).2
      have hW0 : 0 ≤ W (x + X.X T ω) := hW.2.1 _ h0
      have hWle : W (x + X.X T ω) ≤ W a :=
        hW.2.2.2.1 (Set.mem_Ici.mpr h0)
          (Set.mem_Ici.mpr (le_of_lt ha)) ha'
      have hDisc : Real.exp (-(q * (T : ℝ))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have hp : 0 ≤ q * (T : ℝ) :=
          mul_nonneg (le_of_lt hq) (by positivity)
        linarith
      have hFinal : Real.exp (-(q * (T : ℝ))) *
          W (x + X.X T ω) ≤ W a := by
        calc
          _ ≤ 1 * W (x + X.X T ω) :=
            mul_le_mul_of_nonneg_right hDisc hW0
          _ = W (x + X.X T ω) := one_mul _
          _ ≤ W a := hWle
      simpa only [if_neg hA, if_pos hB, zero_add] using hFinal
    · simpa [hA, hB] using hcap
