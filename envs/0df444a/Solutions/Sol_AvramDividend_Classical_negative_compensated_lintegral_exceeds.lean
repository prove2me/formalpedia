-- Prove2me | solution 1 for AvramDividend.Classical.negative_compensated_lintegral_exceeds
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:33:49.070375+00:00
-- url     : https://prove2.me/submissions/33c26bc6-27b3-4b08-b536-2cc99f2994dd

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal
open scoped Topology

private theorem kernel_limit (y : ℝ) (hy : y < 0) :
    Tendsto (fun n : ℕ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 - ((n : ℝ) + 1) * y) /
        ((n : ℝ) + 1)) atTop (nhds |y|) := by
  have hzero : Tendsto (fun n : ℕ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1) / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun n : ℕ => 1 / ((n : ℝ) + 1))
    · exact Eventually.of_forall (fun n => norm_nonneg _)
    · exact Eventually.of_forall (fun n => by
        have ht : 0 < (n : ℝ) + 1 := by positivity
        rw [Real.norm_eq_abs, abs_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg
            (sub_nonpos.mpr (Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonneg_of_nonpos ht.le hy.le))) ht.le)]
        rw [← neg_div, div_le_div_iff_of_pos_right ht]
        linarith [Real.exp_pos (((n : ℝ) + 1) * y)])
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hs := hzero.sub (tendsto_const_nhds (x := y))
  convert hs using 1
  · ext n
    have ht : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    <;> ring
  · rw [abs_of_neg hy]
    ring

theorem AvramDividend.Classical.negative_compensated_lintegral_exceeds
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂ν) = ⊤)
    (B : ℝ≥0∞) (hB : B < ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      B < (∫⁻ y : ℝ,
        ENNReal.ofReal
          ((Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ∂ν) := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun n y => ENNReal.ofReal
    ((Real.exp (((n : ℝ) + 1) * y) - 1 - ((n : ℝ) + 1) * y) / ((n : ℝ) + 1))
  have hm : ∀ n, Measurable (F n) := by
    intro n
    dsimp [F]
    fun_prop
  have he : (fun y => liminf (fun n => F n y) atTop) =ᵐ[ν]
      (fun y => ENNReal.ofReal |y|) := by
    filter_upwards [hneg] with y hy
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (kernel_limit y hy)).liminf_eq
  have hf := lintegral_liminf_le (μ := ν) (u := atTop) hm
  rw [lintegral_congr_ae he, hA] at hf
  have hlim : liminf (fun n => ∫⁻ y, F n y ∂ν) atTop = ⊤ := top_unique hf
  have hev : ∀ᶠ n : ℕ in atTop, B < ∫⁻ y, F n y ∂ν := by
    exact eventually_lt_of_lt_liminf (by rw [hlim]; exact hB)
      ⟨0, Eventually.of_forall (fun n => bot_le)⟩
  exact eventually_atTop.1 hev

theorem solution
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂ν) = ⊤)
    (B : ℝ≥0∞) (hB : B < ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      B < (∫⁻ y : ℝ,
        ENNReal.ofReal
          ((Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ∂ν) := AvramDividend.Classical.negative_compensated_lintegral_exceeds ν hneg hA B hB

#print axioms solution
