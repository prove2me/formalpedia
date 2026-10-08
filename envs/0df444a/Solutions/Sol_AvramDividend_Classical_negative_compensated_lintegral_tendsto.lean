-- Prove2me | solution 1 for AvramDividend.Classical.negative_compensated_lintegral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:01:38.90024+00:00
-- url     : https://prove2.me/submissions/395f2150-e7d1-4f85-b252-7cbdddbd4b61

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ)
    (hneg : ∀ᵐ y ∂ν, y < 0) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ y : ℝ,
        ENNReal.ofReal
          ((Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ∂ν)
      Filter.atTop
      (nhds (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂ν)) := by
  have hmonoReal (y θ₁ θ₂ : ℝ) (hy : y < 0)
      (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) :
      (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ≤
      (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ := by
    have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ hθ
    have hn₁ : θ₁ ≠ 0 := ne_of_gt hθ₁
    have hn₂ : θ₂ ≠ 0 := ne_of_gt hθ₂
    have hyne : y ≠ 0 := ne_of_lt hy
    have hxy : θ₂ * y ≤ θ₁ * y :=
      mul_le_mul_of_nonpos_right hθ hy.le
    have hsec : (Real.exp (θ₂ * y) - 1) / (θ₂ * y) ≤
        (Real.exp (θ₁ * y) - 1) / (θ₁ * y) := by
      have h := ConvexOn.secant_mono convexOn_exp
        (a := (0 : ℝ)) (x := θ₂ * y) (y := θ₁ * y)
        (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
        (mul_ne_zero hn₂ hyne) (mul_ne_zero hn₁ hyne) hxy
      simpa only [Real.exp_zero, sub_zero] using h
    have hprod :
        (Real.exp (θ₁ * y) - 1) / (θ₁ * y) * y ≤
          (Real.exp (θ₂ * y) - 1) / (θ₂ * y) * y :=
      mul_le_mul_of_nonpos_right hsec hy.le
    have hformula (θ : ℝ) (hn : θ ≠ 0) :
        (Real.exp (θ * y) - 1) / (θ * y) * y =
          (Real.exp (θ * y) - 1) / θ := by
      field_simp [hn, hyne]
    have hsecOrd :
        (Real.exp (θ₁ * y) - 1) / θ₁ ≤
        (Real.exp (θ₂ * y) - 1) / θ₂ := by
      calc
        _ = (Real.exp (θ₁ * y) - 1) / (θ₁ * y) * y :=
          (hformula θ₁ hn₁).symm
        _ ≤ (Real.exp (θ₂ * y) - 1) / (θ₂ * y) * y := hprod
        _ = _ := hformula θ₂ hn₂
    have heq₁ :
        (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ =
          (Real.exp (θ₁ * y) - 1) / θ₁ - y := by
      field_simp [hn₁]
    have heq₂ :
        (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ =
          (Real.exp (θ₂ * y) - 1) / θ₂ - y := by
      field_simp [hn₂]
    rw [heq₁, heq₂]
    linarith
  have hlimReal (y : ℝ) (hy : y < 0) :
      Tendsto (fun n : ℕ =>
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) / ((n : ℝ) + 1))
        atTop (nhds (-y)) := by
    have hb (n : ℕ) :
        0 ≤ (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1) ∧
        (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1) ≤
          (1 : ℝ) / ((n : ℝ) + 1) := by
      have hθ : 0 < ((n : ℝ) + 1) := by positivity
      have hz : ((n : ℝ) + 1) * y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hθ.le hy.le
      have he : Real.exp (((n : ℝ) + 1) * y) ≤ 1 :=
        Real.exp_le_one_iff.mpr hz
      constructor
      · exact div_nonneg (by linarith) hθ.le
      · exact div_le_div_of_nonneg_right
          (by linarith [Real.exp_pos (((n : ℝ) + 1) * y)]) hθ.le
    have hsq : Tendsto (fun n : ℕ =>
        (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1))
        atTop (nhds (0 : ℝ)) :=
      squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hquot : Tendsto (fun n : ℕ =>
        (Real.exp (((n : ℝ) + 1) * y) - 1) / ((n : ℝ) + 1))
        atTop (nhds (0 : ℝ)) := by
      have heq : (fun n : ℕ =>
          (Real.exp (((n : ℝ) + 1) * y) - 1) / ((n : ℝ) + 1)) =
        (fun n : ℕ =>
          -((1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1))) := by
        funext n
        ring
      rw [heq]
      simpa using hsq.neg
    have hrew : (fun n : ℕ =>
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) =
      (fun n : ℕ =>
        (Real.exp (((n : ℝ) + 1) * y) - 1) / ((n : ℝ) + 1) - y) := by
      funext n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hrew]
    simpa using hquot.sub (tendsto_const_nhds (x := y))
  let f : ℕ → ℝ → ℝ≥0∞ := fun n y =>
    ENNReal.ofReal
      ((Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1))
  have hm : ∀ n, AEMeasurable (f n) ν := by
    intro n
    have h : Measurable (f n) := by
      dsimp [f]
      fun_prop
    exact h.aemeasurable
  have hmon : ∀ᵐ y ∂ν, Monotone (fun n : ℕ => f n y) := by
    filter_upwards [hneg] with y hy
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    have hreal : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact hmonoReal y ((n : ℝ) + 1) ((m : ℝ) + 1) hy
      (by positivity) (by linarith)
  have hl : ∀ᵐ y ∂ν,
      Tendsto (fun n : ℕ => f n y) atTop
        (nhds (ENNReal.ofReal |y|)) := by
    filter_upwards [hneg] with y hy
    simpa only [f, abs_of_neg hy] using
      (ENNReal.tendsto_ofReal (hlimReal y hy))
  have hf := lintegral_tendsto_of_tendsto_of_monotone hm hmon hl
  simpa only [f] using hf
