-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b25_original_real_stopped_AK_paired_DCT
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:30:04.133575+00:00
-- url     : https://prove2.me/submissions/0e5b9cd8-25b1-4edf-bf19-b2957c18cb4f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bva20_masked_discounted_mark_rate_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_weak_ruin_discounted_mark_bound
import Theorems.Thm_AvramDividend_Classical_avram_bva20_paired_dominated_integral_difference_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (C τ : ℝ≥0∞) (q T : ℝ) (hq : 0 ≤ q)
    (U : ℝ≥0 → ℝ) (ψ : ℝ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hψ : ∀ b : ℝ, 0 ≤ b →
      ENNReal.ofReal b ≤ C → |ψ b| ≤ B)
    (u : ℕ → ℕ → ℝ≥0) (c : ℕ → ℕ → ℝ)
    (hcoeff : ∀ n i,
      c n i =
        if (u n i : ℝ≥0∞) < τ ∧
           0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
        then Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i))
        else 0)
    (f : ℝ → ℝ) :
    let F : ℕ → ℝ → ℝ := fun n t =>
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c n ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0
    let G : ℕ → ℝ → ℝ := fun n t =>
      let s : ℝ≥0 := Real.toNNReal t
      if 0 < s ∧ (s : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (s : ℝ≥0∞) ≤ τ ∧ 0 ≤ U s ∧ ENNReal.ofReal (U s) ≤ C
      then Real.exp (-(q * (s : ℝ))) * ψ (U s)
      else 0
    (∀ n, Measurable (F n)) →
    (∀ n, Measurable (G n)) →
    (∀ᵐ t ∂μ, Tendsto (fun n => F n t) atTop (𝓝 (f t)) ∧
      Tendsto (fun n => G n t) atTop (𝓝 (f t))) →
    Tendsto (fun n => (∫ t, G n t ∂μ) - (∫ t, F n t ∂μ))
      atTop (𝓝 (0 : ℝ)) := by
  let F : ℕ → ℝ → ℝ := fun n t =>
    if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
    then c n ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0
  let G : ℕ → ℝ → ℝ := fun n t =>
    let s : ℝ≥0 := Real.toNNReal t
    if 0 < s ∧ (s : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (s : ℝ≥0∞) ≤ τ ∧ 0 ≤ U s ∧ ENNReal.ofReal (U s) ≤ C
    then Real.exp (-(q * (s : ℝ))) * ψ (U s) else 0
  change (∀ n, Measurable (F n)) →
    (∀ n, Measurable (G n)) →
    (∀ᵐ t ∂μ, Tendsto (fun n => F n t) atTop (𝓝 (f t)) ∧
      Tendsto (fun n => G n t) atTop (𝓝 (f t))) →
    Tendsto (fun n => (∫ t, G n t ∂μ) - (∫ t, F n t ∂μ))
      atTop (𝓝 (0 : ℝ))
  intro hFmeas hGmeas hLim
  have hFb (n : ℕ) (t : ℝ) : ‖F n t‖ ≤ B := by
    rw [Real.norm_eq_abs]
    change |if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c n ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0| ≤ B
    split_ifs with ht
    · rw [hcoeff n ⌊(t / T) * ((n : ℝ) + 2)⌋₊]
      exact avram_bva20_masked_discounted_mark_rate_uniform_bound
        C τ U ψ B q hB hq hψ (u n ⌊(t / T) * ((n : ℝ) + 2)⌋₊)
    · simpa using hB
  have hGb (n : ℕ) (t : ℝ) : ‖G n t‖ ≤ B := by
    change ‖(if 0 < Real.toNNReal t ∧
      ((Real.toNNReal t : ℝ≥0) : ℝ) < T - T / ((n : ℝ) + 2) ∧
      ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) ≤ τ ∧
      0 ≤ U (Real.toNNReal t) ∧ ENNReal.ofReal (U (Real.toNNReal t)) ≤ C
      then Real.exp (-(q * ((Real.toNNReal t : ℝ≥0) : ℝ))) *
        ψ (U (Real.toNNReal t)) else 0)‖ ≤ B
    split_ifs with ht
    · rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.exp_pos _).le]
      have hq0 : 0 ≤ q * (Real.toNNReal t : ℝ) :=
        mul_nonneg hq (NNReal.coe_nonneg _)
      have he : Real.exp (-(q * (Real.toNNReal t : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq0)
      have hψb : |ψ (U (Real.toNNReal t))| ≤ B :=
        hψ (U (Real.toNNReal t)) ht.2.2.2.1 ht.2.2.2.2
      exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans
        (by simpa only [one_mul] using hψb)
    · simpa using hB
  exact avram_bva20_paired_dominated_integral_difference_zero
    μ B G F f
    (fun n => (hGmeas n).aestronglyMeasurable)
    (fun n => (hFmeas n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (hGb n))
    (fun n => Filter.Eventually.of_forall (hFb n))
    (by filter_upwards [hLim] with t ht; exact ht.2)
    (by filter_upwards [hLim] with t ht; exact ht.1)
