-- Prove2me | solution 1 for BellmanDP.GoldMining.stability
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:51:46.333426+00:00
-- url     : https://prove2.me/submissions/495b4dae-2650-48d4-80b8-0bd76a4c4bf5

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model



namespace BellmanDP.GoldMining

open Filter Topology

lemma gs_geo_le {a b C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (h : ∀ N : ℕ, a ≤ b + C * q ^ N) :
    a ≤ b := by
  have ht : Tendsto (fun N : ℕ => b + C * q ^ N) atTop (𝓝 (b + C * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1))
  simp only [mul_zero, add_zero] at ht
  exact ge_of_tendsto' ht h

theorem stability_core (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (h : ℝ → ℝ → ℝ)
    (f : ℝ → ℝ → ℝ) (hf : IsGoldMiningSolution p₁ p₂ r₁ r₂ f) (hfb : BoundedOnRectangles f)
    (g : ℝ → ℝ → ℝ) (hg : IsPerturbedSolution p₁ p₂ r₁ r₂ h g) (hgb : BoundedOnRectangles g)
    (X Y M : ℝ) (hM : ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y → |h x y| ≤ M) :
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y →
      |f x y - g x y| ≤ M / min (1 - p₁) (1 - p₂) := by
  intro x0 y0 hx0 hxX hy0 hyY
  set q := max p₁ p₂ with hqdef
  have hq0 : 0 ≤ q := le_max_of_le_left hp₁0
  have hq1 : q < 1 := max_lt hp₁1 hp₂1
  have hmin : min (1 - p₁) (1 - p₂) = 1 - q := by
    rcases le_total p₁ p₂ with hle | hle
    · rw [min_eq_right (by linarith), hqdef, max_eq_right hle]
    · rw [min_eq_left (by linarith), hqdef, max_eq_left hle]
  rw [hmin]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x0 y0 hx0 hxX hy0 hyY)
  obtain ⟨Mf, hMf⟩ := hfb X Y
  obtain ⟨Mg, hMg⟩ := hgb X Y
  set B := Mf + Mg
  have hB0 : 0 ≤ B := by
    have := hMf x0 y0 hx0 hxX hy0 hyY; have := hMg x0 y0 hx0 hxX hy0 hyY
    linarith [abs_nonneg (f x0 y0), abs_nonneg (g x0 y0)]
  have hE0 : 0 ≤ M / (1 - q) := div_nonneg hM0 (by linarith)
  have hEq : q * (M / (1 - q)) + M = M / (1 - q) := by
    have : (1 - q) ≠ 0 := by linarith
    field_simp
    ring
  have claim : ∀ N : ℕ, ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y →
      |f x y - g x y| ≤ M / (1 - q) + q ^ N * B := by
    intro N
    induction N with
    | zero =>
      intro x y hx hxX hy hyY
      have h1 := hMf x y hx hxX hy hyY
      have h2 := hMg x y hx hxX hy hyY
      have : |f x y - g x y| ≤ |f x y| + |g x y| := abs_sub _ _
      simp only [pow_zero, one_mul]; linarith
    | succ N ih =>
      intro x y hx hxX hy hyY
      have hx' : 0 ≤ (1 - r₁) * x := mul_nonneg (by linarith) hx
      have hx'' : (1 - r₁) * x ≤ X := by nlinarith
      have hy' : 0 ≤ (1 - r₂) * y := mul_nonneg (by linarith) hy
      have hy'' : (1 - r₂) * y ≤ Y := by nlinarith
      have hA : |goldA p₁ r₁ f x y - goldA p₁ r₁ g x y| ≤ q * (M / (1 - q) + q ^ N * B) := by
        have : goldA p₁ r₁ f x y - goldA p₁ r₁ g x y = p₁ * (f ((1 - r₁) * x) y - g ((1 - r₁) * x) y) := by
          unfold goldA; ring
        rw [this, abs_mul, abs_of_nonneg hp₁0]
        have h1 := ih _ _ hx' hx'' hy hyY
        have h2 : 0 ≤ M / (1 - q) + q ^ N * B := by positivity
        calc p₁ * |f ((1 - r₁) * x) y - g ((1 - r₁) * x) y| ≤ p₁ * (M / (1 - q) + q ^ N * B) :=
              mul_le_mul_of_nonneg_left h1 hp₁0
          _ ≤ q * (M / (1 - q) + q ^ N * B) := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
      have hB' : |goldB p₂ r₂ f x y - goldB p₂ r₂ g x y| ≤ q * (M / (1 - q) + q ^ N * B) := by
        have : goldB p₂ r₂ f x y - goldB p₂ r₂ g x y = p₂ * (f x ((1 - r₂) * y) - g x ((1 - r₂) * y)) := by
          unfold goldB; ring
        rw [this, abs_mul, abs_of_nonneg hp₂0]
        have h1 := ih _ _ hx hxX hy' hy''
        have h2 : 0 ≤ M / (1 - q) + q ^ N * B := by positivity
        calc p₂ * |f x ((1 - r₂) * y) - g x ((1 - r₂) * y)| ≤ p₂ * (M / (1 - q) + q ^ N * B) :=
              mul_le_mul_of_nonneg_left h1 hp₂0
          _ ≤ q * (M / (1 - q) + q ^ N * B) := mul_le_mul_of_nonneg_right (le_max_right _ _) h2
      have hmax := abs_max_sub_max_le_max (goldA p₁ r₁ f x y) (goldB p₂ r₂ f x y)
        (goldA p₁ r₁ g x y) (goldB p₂ r₂ g x y)
      have hmax' : |max (goldA p₁ r₁ f x y) (goldB p₂ r₂ f x y) - max (goldA p₁ r₁ g x y) (goldB p₂ r₂ g x y)|
          ≤ q * (M / (1 - q) + q ^ N * B) := hmax.trans (max_le hA hB')
      rw [hf x y hx hy, hg x y hx hy]
      have hh := hM x y hx hxX hy hyY
      have : |max (goldA p₁ r₁ f x y) (goldB p₂ r₂ f x y) -
          (max (goldA p₁ r₁ g x y) (goldB p₂ r₂ g x y) + h x y)| ≤
          |max (goldA p₁ r₁ f x y) (goldB p₂ r₂ f x y) - max (goldA p₁ r₁ g x y) (goldB p₂ r₂ g x y)|
            + |h x y| := by
        rw [← sub_sub]; exact abs_sub _ _
      rw [pow_succ]
      nlinarith
  exact gs_geo_le hq0 hq1 (C := B) (fun N => by have := claim N x0 y0 hx0 hxX hy0 hyY; linarith)

end BellmanDP.GoldMining

open BellmanDP.GoldMining


theorem solution (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (h : ℝ → ℝ → ℝ) (hh : BoundedOnRectangles h)
    (f : ℝ → ℝ → ℝ) (hf : IsGoldMiningSolution p₁ p₂ r₁ r₂ f) (hfb : BoundedOnRectangles f)
    (g : ℝ → ℝ → ℝ) (hg : IsPerturbedSolution p₁ p₂ r₁ r₂ h g) (hgb : BoundedOnRectangles g)
    (X Y M : ℝ) (hM : ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y → |h x y| ≤ M) :
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y →
      |f x y - g x y| ≤ M / min (1 - p₁) (1 - p₂) := by
  exact stability_core p₁ p₂ r₁ r₂ hp₁0 hp₁1 hp₂0 hp₂1 hr₁0 hr₁1 hr₂0 hr₂1 h f hf hfb g hg hgb X Y M hM
