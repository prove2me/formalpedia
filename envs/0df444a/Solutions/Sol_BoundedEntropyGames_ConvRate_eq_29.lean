-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:38:32.223353+00:00
-- url     : https://prove2.me/submissions/15fe544f-08a2-42f6-b5bc-4f01789ec105

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof
import Theorems.Thm_BoundedEntropyGames_ConvRate_eq_3_4
import Theorems.Thm_BoundedEntropyGames_ConvRate_eq_5_6

open BoundedEntropyGames.ConvRate

theorem solution {𝒜 𝒳 𝒴 : Type*} [Fintype 𝒜] [Fintype 𝒳] [Fintype 𝒴]
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) (r : ℝ) (hr : r ∈ Set.Ioc (0 : ℝ) 1)
    (p₁ p₂ : 𝒜 → ℝ) (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (h19 : r * shannon p₁ + (1 - r) * shannon p₂ ≤ condEntropy pXY)
    (h20 : shannon p₂ < shannon p₁) :
    ∃ γ ≥ (0 : ℝ), ∀ α ∈ Set.Ioc (1 : ℝ) 2, ∀ g ∈ Set.Icc (0 : ℝ) r, ∀ ρ ∈ Set.Icc (0 : ℝ) (r - g),
      (shannon p₁ - shannon p₂) * g - γ * (α - 1)
        ≤ condRenyi α pXY - ρ * renyi (1 / α) p₁ - (1 - ρ) * renyi (1 / α) p₂ := by
  obtain ⟨C₀, hC₀, hX⟩ := eq_5_6 pXY hp
  obtain ⟨C₁, hC₁, h1⟩ := eq_3_4 p₁ hp₁
  obtain ⟨C₂, hC₂, h2⟩ := eq_3_4 p₂ hp₂
  set D₀ := condD1 pXY
  set D₁ := d1 p₁
  set D₂ := d1 p₂
  refine ⟨|D₀| + |D₁| + |D₂| + C₀ + C₁ + C₂, by positivity, ?_⟩
  intro α hα g hg ρ hρ
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨hg0, hgr⟩ := hg
  obtain ⟨hρ0, hρr⟩ := hρ
  obtain ⟨hr0, hr1⟩ := hr
  have hαpos : 0 < α := by linarith
  set e := α - 1 with he
  have he0 : 0 < e := by linarith
  have he1 : e ≤ 1 := by linarith
  set e' := 1 / α - 1 with he'
  -- bounds on e' = 1/α - 1 ∈ [-e, 0)
  have hinv : 1 / α < 1 := by rw [div_lt_one hαpos]; exact hα1
  have hinv2 : 1 / 2 ≤ 1 / α := by
    rw [div_le_div_iff₀ (by norm_num) hαpos]; linarith
  have he'neg : e' < 0 := by linarith
  have he'ge : -e ≤ e' := by
    have : 1 / α ≥ 2 - α := by
      rw [ge_iff_le, le_div_iff₀ hαpos]; nlinarith
    linarith
  have hmem : 1 / α ∈ Set.Icc (1 / 2 : ℝ) 2 := ⟨hinv2, by linarith⟩
  have hne : 1 / α ≠ 1 := ne_of_lt hinv
  have hb1 := h1 (1 / α) hmem hne
  have hb2 := h2 (1 / α) hmem hne
  have hb0 := hX α ⟨by linarith, hα2⟩ (ne_of_gt hα1)
  rw [← he'] at hb1 hb2
  rw [← he] at hb0
  have hR1 : renyi (1 / α) p₁ ≤ shannon p₁ + |D₁| * e + C₁ * e := by
    have a1 := (abs_le.mp hb1).2
    have : -(D₁ * e') ≤ |D₁| * e := by
      have : |D₁ * e'| ≤ |D₁| * e := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith)
          (abs_nonneg _)
      linarith [neg_abs_le (D₁ * e')]
    have : e' ^ 2 ≤ e := by nlinarith
    nlinarith
  have hR2 : renyi (1 / α) p₂ ≤ shannon p₂ + |D₂| * e + C₂ * e := by
    have a1 := (abs_le.mp hb2).2
    have : -(D₂ * e') ≤ |D₂| * e := by
      have : |D₂ * e'| ≤ |D₂| * e := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith)
          (abs_nonneg _)
      linarith [neg_abs_le (D₂ * e')]
    have : e' ^ 2 ≤ e := by nlinarith
    nlinarith
  have hR0 : condEntropy pXY - |D₀| * e - C₀ * e ≤ condRenyi α pXY := by
    have a1 := (abs_le.mp hb0).1
    have : D₀ * e ≤ |D₀| * e := mul_le_mul_of_nonneg_right (le_abs_self _) he0.le
    have : e ^ 2 ≤ e := by nlinarith
    nlinarith
  -- (28)
  have hρ1 : ρ ≤ 1 := by linarith
  have h28 : (shannon p₁ - shannon p₂) * g ≤
      condEntropy pXY - ρ * shannon p₁ - (1 - ρ) * shannon p₂ := by
    have : ρ * (shannon p₁ - shannon p₂) ≤ (r - g) * (shannon p₁ - shannon p₂) :=
      mul_le_mul_of_nonneg_right hρr (by linarith)
    linarith only [this, h19]
  have hD1 : 0 ≤ |D₁| := abs_nonneg _
  have hD2 : 0 ≤ |D₂| := abs_nonneg _
  have k1 : ρ * renyi (1 / α) p₁ ≤ ρ * (shannon p₁ + |D₁| * e + C₁ * e) :=
    mul_le_mul_of_nonneg_left hR1 hρ0
  have k2 : (1 - ρ) * renyi (1 / α) p₂ ≤ (1 - ρ) * (shannon p₂ + |D₂| * e + C₂ * e) :=
    mul_le_mul_of_nonneg_left hR2 (by linarith)
  have k3 : ρ * (|D₁| * e + C₁ * e) ≤ |D₁| * e + C₁ * e := by
    have : 0 ≤ |D₁| * e + C₁ * e := by positivity
    have := mul_le_mul_of_nonneg_right hρ1 this
    linarith only [this]
  have k4 : (1 - ρ) * (|D₂| * e + C₂ * e) ≤ |D₂| * e + C₂ * e := by
    have : 0 ≤ |D₂| * e + C₂ * e := by positivity
    have := mul_le_mul_of_nonneg_right (show 1 - ρ ≤ 1 by linarith) this
    linarith only [this]
  linarith only [k1, k2, k3, k4, hR0, h28]
