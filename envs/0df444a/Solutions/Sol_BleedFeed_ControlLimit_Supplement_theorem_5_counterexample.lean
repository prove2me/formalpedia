-- Prove2me | solution 1 for BleedFeed.ControlLimit.Supplement.theorem_5_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:47.119985+00:00
-- url     : https://prove2.me/submissions/f91ed404-47ed-48fe-8bb7-770459325840

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Supplement_Condition8

open scoped ENNReal

open BleedFeed
open BleedFeed.ControlLimit
open BleedFeed.ControlLimit.Supplement

/-- Counterexample to Theorem 5 under its exact Condition (8), throughout the whole
    rate interval [1,2]. The failure occurs at the valid terminal decision age. -/
theorem solution :
    let P : Params := {
      m0 := 1, tau := 1, muL := 1, muU := 2, mtil := 3 / 2,
      nu := fun m => 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹,
      I := 2, N := 1,
      G := (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac 1 +
        (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac 2 }
    P.Standing ∧ Condition8 P ∧ Condition4 P ∧
      (∀ μ ∈ P.rates, critAge P μ = 1) ∧
      (2 : ℝ) ∈ P.rates ∧ 1 < P.I ∧ 0 < P.N ∧
      C P 1 2 0 = 6 ∧ B P 0 = 11 / 2 ∧ ¬ BleedOpt P 1 2 0 := by
        classical
        let P : Params := {
          m0 := 1, tau := 1, muL := 1, muU := 2, mtil := 3 / 2,
          nu := fun m => 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹,
          I := 2, N := 1,
          G := (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac 1 +
            (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac 2 }
        change P.Standing ∧ Condition8 P ∧ Condition4 P ∧
          (∀ μ ∈ P.rates, critAge P μ = 1) ∧
          (2 : ℝ) ∈ P.rates ∧ 1 < P.I ∧ 0 < P.N ∧
          C P 1 2 0 = 6 ∧ B P 0 = 11 / 2 ∧ ¬ BleedOpt P 1 2 0
        have hrates (μ : ℝ) : μ ∈ P.rates ↔ 1 ≤ μ ∧ μ ≤ 2 := Iff.rfl
        have hcrit (μ : ℝ) (hμ : μ ∈ P.rates) : critAge P μ = 1 := by
          have h1 : (1 : ℕ) ∈ {i : ℕ | P.mtil < mass P i μ} := by
            simp only [Set.mem_ofPred_eq, mass, P, pow_one, mul_one, one_mul]
            linarith [(hrates μ).mp hμ |>.1]
          unfold critAge
          apply le_antisymm (Nat.sInf_le h1)
          apply le_csInf ⟨1, h1⟩
          intro i hi
          by_contra hn
          have hi0 : i = 0 := by omega
          subst i
          norm_num [mass, P] at hi
        have hr0 (μ : ℝ) : r P 0 μ = μ := by simp [r, mass, P]
        have hr1 (μ : ℝ) : r P 1 μ = μ * (1 + μ) := by
          simp [r, mass, P]
          ring
        have hp0 (μ : ℝ) : p P 0 μ = 1 := by norm_num [p, mass, P]
        have hp1 (μ : ℝ) (hμ : μ ∈ P.rates) : p P 1 μ = (18 * μ - 8)⁻¹ := by
          have hm : 0 ≤ 1 + μ - 3 / 2 := by linarith [(hrates μ).mp hμ |>.1]
          simp only [p, mass, P, pow_one, mul_one, one_mul, max_eq_left hm]
          ring
        have hint (f : ℝ → ℝ) : (∫ μ, f μ ∂P.G) = (1 / 2) * f 1 + (1 / 2) * f 2 := by
          have hfi (a : ℝ) : MeasureTheory.Integrable f
              ((1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac a) :=
            (MeasureTheory.integrable_dirac (by simp)).smul_measure (by norm_num)
          change (∫ μ, f μ ∂((1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac 1 +
            (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac 2)) = _
          rw [MeasureTheory.integral_add_measure (hfi 1) (hfi 2)]
          simp
        have hmem1 : (1 : ℝ) ∈ P.rates := by norm_num [hrates]
        have hmem2 : (2 : ℝ) ∈ P.rates := by norm_num [hrates]
        have hstanding : P.Standing := by
          refine ⟨by norm_num [P], by norm_num [P], by norm_num [P], by norm_num [P],
            by norm_num [P], by norm_num [P], ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro m hm
            change 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹ = 0
            have hm' : m - 3 / 2 ≤ 0 := by simpa [P] using sub_nonpos.mpr hm
            rw [max_eq_right hm']
            norm_num
          · intro x hx y hy hxy
            change 1 - (1 + 18 * max (x - 3 / 2) 0)⁻¹ <
              1 - (1 + 18 * max (y - 3 / 2) 0)⁻¹
            have hx' : 0 ≤ x - 3 / 2 := by
              change 3 / 2 ≤ x at hx
              linarith
            have hy' : 0 ≤ y - 3 / 2 := by
              change 3 / 2 ≤ y at hy
              linarith
            rw [max_eq_left hx', max_eq_left hy']
            have hd : (1 + 18 * (y - 3 / 2))⁻¹ < (1 + 18 * (x - 3 / 2))⁻¹ :=
              (inv_lt_inv₀ (by positivity) (by positivity)).mpr (by linarith)
            linarith
          · intro m
            change (1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹) * 1 ≤ 1
            have : 0 ≤ (1 + 18 * max (m - 3 / 2) 0 : ℝ)⁻¹ := by positivity
            linarith
          · dsimp [P]
            fun_prop
          · apply MeasureTheory.isProbabilityMeasure_iff.mpr
            norm_num [P, MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
              ENNReal.inv_two_add_inv_two]
          · norm_num [P, Params.rates, MeasureTheory.Measure.add_apply,
              MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply']
        have hc4 : Condition4 P := by
          intro μ hμ i hci hi
          have hi1 : i = 1 := by rw [hcrit μ hμ] at hci; change i < 2 at hi; omega
          subst i
          have hμ1 := ((hrates μ).mp hμ).1
          have hd : 0 < 18 * μ - 8 := by linarith
          have hr : 0 < μ * (1 + μ) := by positivity
          simp only [Nat.sub_self, hr1, hr0, hp0, hp1 μ hμ]
          apply (div_le_iff₀ hr).mpr
          rw [sub_mul, inv_mul_eq_div, le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
          apply (div_le_iff₀ hd).mpr
          nlinarith [sq_nonneg (μ - 1)]
        have hJ : (∫ μ, p P (critAge P μ) μ * r P (P.I - 1) μ ∂P.G) = 29 / 140 := by
          rw [hint]
          rw [hcrit 1 hmem1, hcrit 2 hmem2]
          change (1 / 2 : ℝ) * (p P 1 1 * r P 1 1) + (1 / 2) * (p P 1 2 * r P 1 2) = _
          rw [hp1 1 hmem1, hp1 2 hmem2, hr1, hr1]
          norm_num
        have hc8 : Condition8 P := by
          intro μ hμ i hci hi
          have hi1 : i = 1 := by rw [hcrit μ hμ] at hci; change i < 2 at hi; omega
          subst i
          rw [hcrit μ hμ, hJ]
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hr0, hr1, hp1 μ hμ]
          have hμ1 := ((hrates μ).mp hμ).1
          have hd : 0 < 18 * μ - 8 := by linarith
          have hden : 0 < μ + μ * (1 + μ) + 29 / 140 := by positivity
          apply (div_le_iff₀ hden).mpr
          rw [sub_mul, inv_mul_eq_div]
          rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
          apply (div_le_iff₀ hd).mpr
          nlinarith [sq_nonneg (μ - 1)]
        have hW2 (b μ : ℝ) : W P b μ 2 = 0 := by rw [W]; norm_num [P]
        have hW1 (b μ : ℝ) : W P b μ 1 = max (r P 1 μ) b := by
          rw [W]
          norm_num only [P, show ¬ (2 : ℕ) ≤ 1 by omega, if_false]
          rw [hW2]
          simp
        have hB : B P 0 = 11 / 2 := by
          change (∫ μ, Ck P (Bk P 0) 0 μ ∂P.G) = _
          rw [hint]
          simp only [Bk, Ck, hW1, hp0, hr0, hr1]
          norm_num
        have hC : C P 1 2 0 = 6 := by
          unfold C Ck
          rw [hW2, hr1]
          norm_num
        refine ⟨hstanding, hc8, hc4, hcrit, hmem2, by norm_num [P], by norm_num [P], hC, hB, ?_⟩
        intro h
        have := h.2
        rw [hC, hB] at this
        norm_num at this
