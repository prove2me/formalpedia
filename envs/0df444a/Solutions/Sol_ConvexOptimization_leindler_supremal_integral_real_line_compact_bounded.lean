-- Prove2me | solution 1 for ConvexOptimization.leindler_supremal_integral_real_line_compact_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T05:47:14.137897+00:00
-- url     : https://prove2.me/submissions/29b1f274-820a-48dd-a9f3-5e81062d666c

import Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line_unit_bounded

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

private theorem scale_rpow_product
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (a b u v : ℝ≥0∞)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hatop : a ≠ ∞) (hbtop : b ≠ ∞) :
    (a ^ (1 - l) * b ^ l) *
        ((a⁻¹ * u) ^ (1 - l) * (b⁻¹ * v) ^ l) =
      u ^ (1 - l) * v ^ l := by
  have hapos : 0 < 1 - l := sub_pos.mpr hl1
  have ha : 0 ≤ 1 - l := hapos.le
  have hb : 0 ≤ l := hl0.le
  simp only [ENNReal.mul_rpow_of_nonneg _ _ ha,
    ENNReal.mul_rpow_of_nonneg _ _ hb, ENNReal.inv_rpow]
  have hacancel : a ^ (1 - l) * (a ^ (1 - l))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel
      ((ENNReal.rpow_eq_zero_iff_of_pos hapos).not.mpr ha0)
      (ENNReal.rpow_ne_top_of_nonneg ha hatop)
  have hbcancel : b ^ l * (b ^ l)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel
      ((ENNReal.rpow_eq_zero_iff_of_pos hl0).not.mpr hb0)
      (ENNReal.rpow_ne_top_of_nonneg hb hbtop)
  calc
    _ = (a ^ (1 - l) * (a ^ (1 - l))⁻¹) *
        (b ^ l * (b ^ l)⁻¹) * (u ^ (1 - l) * v ^ l) := by
      ac_rfl
    _ = _ := by rw [hacancel, hbcancel]; simp

theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (Bf Bg : NNReal)
    (hfB : ∀ x, f x ≤ (Bf : ENNReal))
    (hgB : ∀ x, g x ≤ (Bg : ENNReal)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  by_cases hBf0 : Bf = 0
  · have hfzero : ∀ x, f x = 0 := by
      intro x
      apply bot_unique
      simpa [hBf0] using hfB x
    simp [hfzero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hl1)]
  by_cases hBg0 : Bg = 0
  · have hgzero : ∀ x, g x = 0 := by
      intro x
      apply bot_unique
      simpa [hBg0] using hgB x
    simp [hgzero, ENNReal.zero_rpow_of_pos hl0]

  let bf : ℝ≥0∞ := (Bf : ℝ≥0∞)
  let bg : ℝ≥0∞ := (Bg : ℝ≥0∞)
  let F : ℝ → ℝ≥0∞ := fun x => bf⁻¹ * f x
  let G : ℝ → ℝ≥0∞ := fun x => bg⁻¹ * g x
  let C : ℝ≥0∞ := bf ^ (1 - l) * bg ^ l

  have hbf0 : bf ≠ 0 := by simpa [bf] using hBf0
  have hbg0 : bg ≠ 0 := by simpa [bg] using hBg0
  have hbftop : bf ≠ ∞ := by simp [bf]
  have hbgtop : bg ≠ ∞ := by simp [bg]

  have hF : Measurable F := measurable_const.mul hf
  have hG : Measurable G := measurable_const.mul hg
  have hFc : HasCompactSupport F := by
    exact hfc.mul_left
  have hGc : HasCompactSupport G := by
    exact hgc.mul_left
  have hF1 : ∀ x, F x ≤ 1 := by
    intro x
    calc
      F x = bf⁻¹ * f x := rfl
      _ ≤ bf⁻¹ * bf := mul_le_mul_of_nonneg_left (by simpa [bf] using hfB x) zero_le
      _ = 1 := ENNReal.inv_mul_cancel hbf0 hbftop
  have hG1 : ∀ x, G x ≤ 1 := by
    intro x
    calc
      G x = bg⁻¹ * g x := rfl
      _ ≤ bg⁻¹ * bg := mul_le_mul_of_nonneg_left (by simpa [bg] using hgB x) zero_le
      _ = 1 := ENNReal.inv_mul_cancel hbg0 hbgtop

  have hcore :=
    ConvexOptimization.leindler_supremal_integral_real_line_unit_bounded
      l hl0 hl1 F G hF hG hFc hGc hF1 hG1

  have hFint : (∫⁻ x, F x) = bf⁻¹ * ∫⁻ x, f x := by
    simpa only [F] using lintegral_const_mul bf⁻¹ hf
  have hGint : (∫⁻ x, G x) = bg⁻¹ * ∫⁻ x, g x := by
    simpa only [G] using lintegral_const_mul bg⁻¹ hg

  have hCtop : C ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hl1.le) hbftop
    · exact ENNReal.rpow_ne_top_of_nonneg hl0.le hbgtop

  have hlhs_scale :
      C * ((∫⁻ x, F x) ^ (1 - l) * (∫⁻ x, G x) ^ l) =
        (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l := by
    rw [hFint, hGint]
    exact scale_rpow_product l hl0 hl1 bf bg
      (∫⁻ x, f x) (∫⁻ x, g x) hbf0 hbg0 hbftop hbgtop

  rw [← hlhs_scale]
  calc
    C * ((∫⁻ x, F x) ^ (1 - l) * (∫⁻ x, G x) ^ l)
        ≤ C * (∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
            (1 - l) • x + l • y = z ∧
              q = F x ^ (1 - l) * G y ^ l}) :=
      mul_le_mul_of_nonneg_left hcore zero_le
    _ = ∫⁻ z, C * sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
          (1 - l) • x + l • y = z ∧
            q = F x ^ (1 - l) * G y ^ l} :=
      (lintegral_const_mul' C _ hCtop).symm
    _ ≤ ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
          (1 - l) • x + l • y = z ∧
            q = f x ^ (1 - l) * g y ^ l} := by
      apply lintegral_mono
      intro z
      change C * sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
          (1 - l) • x + l • y = z ∧
            q = F x ^ (1 - l) * G y ^ l} ≤
        sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
          (1 - l) • x + l • y = z ∧
            q = f x ^ (1 - l) * g y ^ l}
      rw [ENNReal.mul_sSup]
      apply iSup_le
      intro q
      apply iSup_le
      intro hq
      rcases hq with ⟨x, y, hxy, rfl⟩
      have hscale :
          C * (F x ^ (1 - l) * G y ^ l) =
            f x ^ (1 - l) * g y ^ l := by
        exact scale_rpow_product l hl0 hl1 bf bg (f x) (g y)
          hbf0 hbg0 hbftop hbgtop
      rw [hscale]
      exact le_sSup ⟨x, y, hxy, rfl⟩
