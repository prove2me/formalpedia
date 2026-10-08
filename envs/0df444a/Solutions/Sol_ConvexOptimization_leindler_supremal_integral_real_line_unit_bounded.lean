-- Prove2me | solution 1 for ConvexOptimization.leindler_supremal_integral_real_line_unit_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T06:10:24.648879+00:00
-- url     : https://prove2.me/submissions/f9a71be5-94bf-474b-92f8-647b972857ce

import Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line_unit_sup_normalized

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

private theorem scale_rpow_product_unit_sup
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (a b u v : ℝ≥0∞)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hatop : a ≠ ⊤) (hbtop : b ≠ ⊤) :
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
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  let a : ℝ≥0∞ := sSup (Set.range f)
  let b : ℝ≥0∞ := sSup (Set.range g)

  have hfa : ∀ x, f x ≤ a := by
    intro x
    exact le_sSup (Set.mem_range_self x)
  have hgb : ∀ x, g x ≤ b := by
    intro x
    exact le_sSup (Set.mem_range_self x)
  have ha1 : a ≤ 1 := by
    change sSup (Set.range f) ≤ 1
    rw [sSup_range]
    exact iSup_le hf1
  have hb1 : b ≤ 1 := by
    change sSup (Set.range g) ≤ 1
    rw [sSup_range]
    exact iSup_le hg1

  by_cases ha0 : a = 0
  · have hfzero : ∀ x, f x = 0 := by
      intro x
      exact bot_unique (by simpa [ha0] using hfa x)
    simp [hfzero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hl1)]
  by_cases hb0 : b = 0
  · have hgzero : ∀ x, g x = 0 := by
      intro x
      exact bot_unique (by simpa [hb0] using hgb x)
    simp [hgzero, ENNReal.zero_rpow_of_pos hl0]

  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb1

  let F : ℝ → ℝ≥0∞ := fun x ↦ a⁻¹ * f x
  let G : ℝ → ℝ≥0∞ := fun x ↦ b⁻¹ * g x
  let C : ℝ≥0∞ := a ^ (1 - l) * b ^ l

  have hF : Measurable F := measurable_const.mul hf
  have hG : Measurable G := measurable_const.mul hg
  have hFc : HasCompactSupport F := by
    exact hfc.mul_left
  have hGc : HasCompactSupport G := by
    exact hgc.mul_left
  have hF1 : ∀ x, F x ≤ 1 := by
    intro x
    calc
      F x = a⁻¹ * f x := rfl
      _ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left (hfa x) zero_le
      _ = 1 := ENNReal.inv_mul_cancel ha0 hatop
  have hG1 : ∀ x, G x ≤ 1 := by
    intro x
    calc
      G x = b⁻¹ * g x := rfl
      _ ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left (hgb x) zero_le
      _ = 1 := ENNReal.inv_mul_cancel hb0 hbtop

  have hFsup : sSup (Set.range F) = 1 := by
    rw [sSup_range]
    change (⨆ x, a⁻¹ * f x) = 1
    rw [← ENNReal.mul_iSup, ← sSup_range]
    change a⁻¹ * a = 1
    exact ENNReal.inv_mul_cancel ha0 hatop
  have hGsup : sSup (Set.range G) = 1 := by
    rw [sSup_range]
    change (⨆ x, b⁻¹ * g x) = 1
    rw [← ENNReal.mul_iSup, ← sSup_range]
    change b⁻¹ * b = 1
    exact ENNReal.inv_mul_cancel hb0 hbtop

  have hcore :=
    ConvexOptimization.leindler_supremal_integral_real_line_unit_sup_normalized
      l hl0 hl1 F G hF hG hFc hGc hF1 hG1 hFsup hGsup

  have hFint : (∫⁻ x, F x) = a⁻¹ * ∫⁻ x, f x := by
    simpa only [F] using lintegral_const_mul a⁻¹ hf
  have hGint : (∫⁻ x, G x) = b⁻¹ * ∫⁻ x, g x := by
    simpa only [G] using lintegral_const_mul b⁻¹ hg

  have hCtop : C ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hl1.le) hatop
    · exact ENNReal.rpow_ne_top_of_nonneg hl0.le hbtop

  have hlhs_scale :
      C * ((∫⁻ x, F x) ^ (1 - l) * (∫⁻ x, G x) ^ l) =
        (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l := by
    rw [hFint, hGint]
    exact scale_rpow_product_unit_sup l hl0 hl1 a b
      (∫⁻ x, f x) (∫⁻ x, g x) ha0 hb0 hatop hbtop

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
        exact scale_rpow_product_unit_sup l hl0 hl1 a b (f x) (g y)
          ha0 hb0 hatop hbtop
      rw [hscale]
      exact le_sSup ⟨x, y, hxy, rfl⟩
