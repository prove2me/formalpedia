-- Prove2me | solution 1 for FBMSP.mhr_revenue_tp2
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:09:25.686974+00:00
-- url     : https://prove2.me/submissions/41765fd9-5d92-47af-9fd9-df5995c67fef

import Definitions.Def_FBMSP_Model

open MeasureTheory Set FBMSP

private lemma tp2_survival_antitone (η : Measure ℝ) [IsProbabilityMeasure η] :
    Antitone (survival η) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
    (measure_mono (Ici_subset_Ici.mpr hab))

private lemma tp2_concave_four_point {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) (a b c d : ℝ)
    (ha : a ∈ s) (hd : d ∈ s)
    (hab : a ≤ b) (hbd : b ≤ d) (hac : a ≤ c) (hcd : c ≤ d)
    (hsum : a + d = b + c) :
    f a + f d ≤ f b + f c := by
  by_cases h : a = d
  · have hb : b = a := by linarith
    have hc : c = a := by linarith
    simp [h, hb, hc]
  have had : a < d := lt_of_le_of_ne (hab.trans hbd) h
  have hden : 0 < d - a := sub_pos.mpr had
  let u := (d - b) / (d - a)
  let v := (b - a) / (d - a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hbd) hden.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hab) hden.le
  have huv : u + v = 1 := by
    dsimp [u, v]
    field_simp [ne_of_gt hden]
    <;> ring
  have hb : u * a + v * d = b := by
    dsimp [u, v]
    field_simp [ne_of_gt hden]
    <;> ring
  have hc : v * a + u * d = c := by
    calc
      v * a + u * d = a + d - b := by
        dsimp [u, v]
        field_simp [ne_of_gt hden]
        <;> ring
      _ = c := by linarith
  have hfb := hf.2 ha hd hu hv huv
  have hfc := hf.2 ha hd hv hu (by linarith)
  simp only [smul_eq_mul, hb] at hfb
  simp only [smul_eq_mul, hc] at hfc
  calc
    f a + f d =
        (u * f a + v * f d) + (v * f a + u * f d) := by
      calc
        f a + f d = (u + v) * (f a + f d) := by rw [huv, one_mul]
        _ = _ := by ring
    _ ≤ f b + f c := add_le_add hfb hfc

theorem solution (η : MeasureTheory.Measure ℝ)
    (hnoise : ValidNoise η) (hmhr : HasMHR η)
    (x₁ x₂ p₁ p₂ : ℝ) (hx : x₁ ≤ x₂)
    (hp₁ : 0 ≤ p₁) (hp : p₁ ≤ p₂) :
    postedRevenue η x₁ p₂ * postedRevenue η x₂ p₁ ≤
      postedRevenue η x₁ p₁ * postedRevenue η x₂ p₂ := by
  letI : IsProbabilityMeasure η := hnoise.1
  have hs0 (t : ℝ) : 0 ≤ survival η t := ENNReal.toReal_nonneg
  have hanti := tp2_survival_antitone η
  have hprod :
      survival η (p₁ - x₂) * survival η (p₂ - x₁) ≤
        survival η (p₁ - x₁) * survival η (p₂ - x₂) := by
    by_cases hd : 0 < survival η (p₂ - x₁)
    · have ha : 0 < survival η (p₁ - x₂) :=
        hd.trans_le (hanti (by linarith))
      have hb : 0 < survival η (p₁ - x₁) :=
        hd.trans_le (hanti (by linarith))
      have hc : 0 < survival η (p₂ - x₂) :=
        hd.trans_le (hanti (by linarith))
      have hlog := tp2_concave_four_point hmhr.2
        (p₁ - x₂) (p₁ - x₁) (p₂ - x₂) (p₂ - x₁)
        ha hd (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
      have he := Real.exp_le_exp.mpr hlog
      simpa only [Real.exp_add, Real.exp_log ha, Real.exp_log hb,
        Real.exp_log hc, Real.exp_log hd] using he
    · have hz : survival η (p₂ - x₁) = 0 := le_antisymm (le_of_not_gt hd) (hs0 _)
      rw [hz, mul_zero]
      exact mul_nonneg (hs0 _) (hs0 _)
  have hprices : 0 ≤ p₁ * p₂ := mul_nonneg hp₁ (hp₁.trans hp)
  unfold postedRevenue
  calc
    p₂ * survival η (p₂ - x₁) * (p₁ * survival η (p₁ - x₂)) =
        (p₁ * p₂) * (survival η (p₁ - x₂) * survival η (p₂ - x₁)) := by ring
    _ ≤ (p₁ * p₂) * (survival η (p₁ - x₁) * survival η (p₂ - x₂)) :=
      mul_le_mul_of_nonneg_left hprod hprices
    _ = p₁ * survival η (p₁ - x₁) * (p₂ * survival η (p₂ - x₂)) := by ring
