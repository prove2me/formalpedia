-- Prove2me | solution 1 for CorreaThreshold.Adaptive.beta_star_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:55:36.353855+00:00
-- url     : https://prove2.me/submissions/e2eaa1a4-2230-43f4-8c5a-00d6463b651c

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

open MeasureTheory ProbabilityTheory CorreaThreshold.Adaptive

namespace Correa2Beta

/-- `g(y) = y (1 − ln y)`. -/
noncomputable def g (y : ℝ) : ℝ := y * (1 - Real.log y)

lemma g_cont : Continuous g := by
  have : g = fun y => y - y * Real.log y := by funext y; simp [g]; ring
  rw [this]
  exact continuous_id.sub Real.continuous_mul_log

lemma g_nonneg {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ g y := by
  unfold g
  have := Real.log_nonpos h0 h1
  nlinarith

lemma g_pos {y : ℝ} (h0 : 0 < y) (h1 : y ≤ 1) : 0 < g y := by
  unfold g
  have := Real.log_nonpos h0.le h1
  nlinarith

lemma g_mono : MonotoneOn g (Set.Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) g_cont.continuousOn
  · intro y hy
    rw [interior_Icc] at hy
    have hy0 : y ≠ 0 := hy.1.ne'
    exact ((differentiableAt_id.mul ((differentiableAt_const _).sub
      (Real.differentiableAt_log hy0)))).differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    have hy0 : y ≠ 0 := hy.1.ne'
    have hd : HasDerivAt g (1 * (1 - Real.log y) + y * (0 - y⁻¹)) y :=
      (hasDerivAt_id y).mul ((hasDerivAt_const y (1 : ℝ)).sub (Real.hasDerivAt_log hy0))
    rw [hd.deriv]
    have := Real.log_nonpos hy.1.le hy.2.le
    field_simp
    linarith

/-- the integrand -/
noncomputable def f (β y : ℝ) : ℝ := 1 / (g y + (β - 1))

lemma f_contOn {β : ℝ} (hβ : 1 < β) : ContinuousOn (f β) (Set.Icc 0 1) := by
  unfold f
  apply ContinuousOn.div continuousOn_const
  · exact (g_cont.add continuous_const).continuousOn
  · intro y hy
    have := g_nonneg hy.1 hy.2
    linarith

lemma G_eq (β : ℝ) :
    ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (β - 1)) = ∫ y in (0 : ℝ)..1, f β y := rfl

lemma G_strictAnti {β₁ β₂ : ℝ} (h1 : 1 < β₁) (h12 : β₁ < β₂) :
    ∫ y in (0 : ℝ)..1, f β₂ y < ∫ y in (0 : ℝ)..1, f β₁ y := by
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
    (f_contOn (by linarith)) (f_contOn h1)
  · intro y hy
    have := g_nonneg hy.1.le hy.2
    unfold f
    apply one_div_le_one_div_of_le (by linarith); linarith
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    have := g_nonneg (le_refl (0 : ℝ)) zero_le_one
    unfold f
    apply one_div_lt_one_div_of_lt (by linarith); linarith

lemma G_two_lt : ∫ y in (0 : ℝ)..1, f 2 y < 1 := by
  have : ∫ y in (0 : ℝ)..1, f 2 y < ∫ y in (0 : ℝ)..1, (1 : ℝ) := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
      (f_contOn (by norm_num)) continuousOn_const
    · intro y hy
      have := g_nonneg hy.1.le hy.2
      unfold f
      rw [div_le_one (by linarith)]; linarith
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      have := g_pos zero_lt_one le_rfl
      unfold f
      rw [div_lt_one (by linarith)]; linarith
  simpa using this

/-- piece lower bound -/
lemma piece {β a b : ℝ} (hβ : 1 < β) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) * (1 / (g b + (β - 1))) ≤ ∫ y in a..b, f β y := by
  have hint : IntervalIntegrable (f β) volume a b :=
    ((f_contOn hβ).mono (Set.Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have := intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
    (f := fun _ => 1 / (g b + (β - 1))) (g := f β) (by
      intro y hy
      have hy0 : 0 ≤ y := le_trans ha hy.1
      have hgy := g_nonneg hy0 (le_trans hy.2 hb)
      have hgb : g y ≤ g b := g_mono ⟨hy0, le_trans hy.2 hb⟩ ⟨le_trans ha hab, hb⟩ hy.2
      unfold f
      apply one_div_le_one_div_of_le (by linarith); linarith)
  simpa [mul_comm] using this

lemma G_near_one_gt : 1 < ∫ y in (0 : ℝ)..1, f (101 / 100) y := by
  have hβ : (1 : ℝ) < 101 / 100 := by norm_num
  have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable (f (101/100)) volume a b :=
    fun a b ha hab hb =>
      ((f_contOn hβ).mono (Set.Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (1/32) le_rfl (by norm_num) (by norm_num))
      (hint (1/32) 1 (by norm_num) (by norm_num) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (1/32) (1/8) (by norm_num) (by norm_num) (by norm_num))
      (hint (1/8) 1 (by norm_num) (by norm_num) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (1/8) (1/2) (by norm_num) (by norm_num) (by norm_num))
      (hint (1/2) 1 (by norm_num) (by norm_num) le_rfl)]
  have h0 : 0 ≤ ∫ y in (0 : ℝ)..(1/32), f (101/100) y := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    have := g_nonneg hy.1 (by linarith [hy.2])
    unfold f; apply div_nonneg zero_le_one; linarith
  have p1 := piece (β := 101/100) hβ (a := 1/32) (b := 1/8) (by norm_num) (by norm_num) (by norm_num)
  have p2 := piece (β := 101/100) hβ (a := 1/8) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
  have p3 := piece (β := 101/100) hβ (a := 1/2) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_pos one_lt_two
  have g1 : g 1 = 1 := by simp [g]
  have g2 : g (1/2) = (1/2) * (1 + Real.log 2) := by
    simp only [g, one_div, Real.log_inv]; ring
  have g8 : g (1/8) = (1/8) * (1 + 3 * Real.log 2) := by
    have : (1/8 : ℝ) = (2 ^ 3)⁻¹ := by norm_num
    rw [g, this, Real.log_inv, Real.log_pow]; push_cast; ring
  rw [g1] at p3
  rw [g2] at p2
  rw [g8] at p1
  have e1 : (1 / 8 - 1 / 32) * (1 / (1 / 8 * (1 + 3 * Real.log 2) + (101 / 100 - 1))) ≥
      (3/32) * (1 / ((1/8) * (1 + 3 * 0.6931471808) + 1/100)) := by
    apply mul_le_mul (by norm_num) _ (by positivity) (by norm_num)
    apply one_div_le_one_div_of_le (by positivity); linarith
  have e2 : (1 / 2 - 1 / 8) * (1 / (1 / 2 * (1 + Real.log 2) + (101 / 100 - 1))) ≥
      (3/8) * (1 / ((1/2) * (1 + 0.6931471808) + 1/100)) := by
    apply mul_le_mul (by norm_num) _ (by positivity) (by norm_num)
    apply one_div_le_one_div_of_le (by positivity); linarith
  norm_num at e1 e2 p1 p2 p3
  linarith

end Correa2Beta

open Correa2Beta in
theorem solution :
    ∃! β : ℝ, 1 < β ∧ ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (β - 1)) = 1 := by
  simp only [G_eq]
  -- continuity of `G` on `[101/100, 2]`
  set I := Set.Icc (101 / 100 : ℝ) 2
  have hcont : ContinuousOn (fun β => ∫ y in (0 : ℝ)..1, f β y) I := by
    rw [continuousOn_iff_continuous_restrict]
    let F : I → ℝ → ℝ := fun β y => 1 / (g (Set.projIcc (0 : ℝ) 1 zero_le_one y) + ((β : ℝ) - 1))
    have hF : Continuous (Function.uncurry F) := by
      apply Continuous.div continuous_const
      · exact (g_cont.comp (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))).add
          ((continuous_subtype_val.comp continuous_fst).sub continuous_const)
      · intro p
        have h1 := g_nonneg (Set.projIcc (0 : ℝ) 1 zero_le_one p.2).2.1
          (Set.projIcc (0 : ℝ) 1 zero_le_one p.2).2.2
        have h2 := p.1.2.1
        have : (0:ℝ) < g (Set.projIcc (0:ℝ) 1 zero_le_one p.2) + ((p.1:ℝ) - 1) := by linarith
        exact this.ne'
    have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hF 0 1
    convert hc using 1
    funext β
    simp only [Set.restrict_apply]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    simp only [F, f, Set.projIcc_of_mem zero_le_one hy]
  have hmem : (1 : ℝ) ∈ Set.Icc (∫ y in (0 : ℝ)..1, f 2 y) (∫ y in (0 : ℝ)..1, f (101/100) y) :=
    ⟨G_two_lt.le, G_near_one_gt.le⟩
  obtain ⟨β, hβI, hβ⟩ := intermediate_value_Icc' (by norm_num : (101/100 : ℝ) ≤ 2) hcont hmem
  refine ⟨β, ⟨by linarith [hβI.1], hβ⟩, ?_⟩
  rintro β' ⟨hβ'1, hβ'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := G_strictAnti hβ'1 h
    simp only at hβ
    linarith
  · have := G_strictAnti (by linarith [hβI.1]) h
    simp only at hβ
    linarith
