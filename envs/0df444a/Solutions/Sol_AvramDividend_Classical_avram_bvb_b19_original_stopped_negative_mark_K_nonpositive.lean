-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b19_original_stopped_negative_mark_K_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:40:22.337222+00:00
-- url     : https://prove2.me/submissions/940201e3-3f7a-491b-88eb-5e40e36eb505

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys93_negative_mark_closed_cap_compensator_double_integral_nonpos
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! Exact original-kernel sign, specialising the proved closed-cap marked integral theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ : ℕ → ℝ) (U : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    (∫ t, ∫ z,
      (if 0 < t ∧ (t : ℝ) < T - δ n ∧
          (t : ℝ≥0∞) ≤ σ ω ∧ 0 ≤ U t ω ∧
          ENNReal.ofReal (U t ω) ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) *
          (w (U t ω + z) - w (U t ω))
      else 0) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) ≤ 0 := by
  let μ : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let A : Set ℝ≥0 := {t | 0 < t ∧ (t : ℝ) < T - δ n ∧
    (t : ℝ≥0∞) ≤ σ ω ∧ 0 ≤ U t ω ∧
    ENNReal.ofReal (U t ω) ≤ C}
  let e : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  have he : ∀ t, 0 ≤ e t := by
    intro t
    exact le_of_lt (Real.exp_pos _)
  have hUA : ∀ t ∈ A, 0 ≤ U t ω ∧
      ENNReal.ofReal (U t ω) ≤ C := by
    intro t ht
    rcases ht with ⟨_, _, _, h0, hcap⟩
    exact ⟨h0, hcap⟩
  have hsign :=
    avram_bvb_phys93_negative_mark_closed_cap_compensator_double_integral_nonpos
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      μ ν (fun t => U t ω) e A he hUA
  simpa only [μ, ν, A, e, Set.mem_setOf_eq, and_assoc] using hsign
