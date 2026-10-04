-- Prove2me | solution 1 for AvramDividend.Classical.discounted_renewal_kernel_mass_small
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:48:46.632005+00:00
-- url     : https://prove2.me/submissions/871c201f-281b-4939-b0f2-c5ba4268cd9d

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace P35bb663a

lemma kernel_le (n : ℕ) (z : ℝ≥0) :
    ENNReal.ofReal ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) / ((n : ℝ) + 1))
      ≤ ENNReal.ofReal (min (z : ℝ) 1) := by
  apply ENNReal.ofReal_le_ofReal
  have hθ : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hθp : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hz : (0 : ℝ) ≤ (z : ℝ) := z.2
  have he : 0 < Real.exp (-((n : ℝ) + 1) * (z : ℝ)) := Real.exp_pos _
  have h1 : 1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ)) ≤ ((n : ℝ) + 1) * (z : ℝ) := by
    have := Real.add_one_le_exp (-((n : ℝ) + 1) * (z : ℝ))
    linarith
  rw [le_min_iff]
  constructor
  · rw [div_le_iff₀ hθp]; linarith
  · rw [div_le_iff₀ hθp]; nlinarith

lemma kernel_tendsto (z : ℝ≥0) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) / ((n : ℝ) + 1))) atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  apply ENNReal.tendsto_ofReal
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero (fun n => ?_) (fun n => ?_) hlim
  · have hθp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : Real.exp (-((n : ℝ) + 1) * (z : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hz : (0 : ℝ) ≤ (z : ℝ) := z.2
      nlinarith
    exact div_nonneg (by linarith) hθp.le
  · have hθp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have := Real.exp_pos (-((n : ℝ) + 1) * (z : ℝ))
    exact div_le_div_of_nonneg_right (by linarith) hθp.le

end P35bb663a

open MeasureTheory Filter Set Topology NNReal ENNReal in
theorem solution (μ : Measure ℝ≥0)
    (hμ : (∫⁻ z : ℝ≥0, ENNReal.ofReal (min (z : ℝ) 1) ∂μ) ≠ ⊤)
    (q δ : ℝ) (hq : 0 < q) (hδ : 0 < δ) :
    ∃ n : ℕ,
      ENNReal.ofReal (q / ((n : ℝ) + 1)) +
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
              ((n : ℝ) + 1)) ∂μ) <
        ENNReal.ofReal δ := by
  have hI : Tendsto (fun n : ℕ => ∫⁻ z : ℝ≥0, ENNReal.ofReal
      ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence
      (μ := μ) (f := fun _ => (0 : ℝ≥0∞))
      (F := fun (n : ℕ) (z : ℝ≥0) => ENNReal.ofReal
        ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) / ((n : ℝ) + 1)))
      (fun z => ENNReal.ofReal (min (z : ℝ) 1))
      (fun n => by
        apply Measurable.ennreal_ofReal
        apply Continuous.measurable
        fun_prop)
      (fun n => Eventually.of_forall (fun z => P35bb663a.kernel_le n z))
      hμ
      (Eventually.of_forall (fun z => P35bb663a.kernel_tendsto z))
    simpa using h
  have hQ : Tendsto (fun n : ℕ => ENNReal.ofReal (q / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul q
    simpa [mul_one_div, div_eq_mul_inv] using this
  have hS := hQ.add hI
  rw [add_zero] at hS
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  exact (hS.eventually (gt_mem_nhds hpos)).exists
