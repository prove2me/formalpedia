-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_signed_grid_second_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:37:58.493604+00:00
-- url     : https://prove2.me/submissions/25d6c805-f471-478c-9747-452c69ae8413

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_negative_test_grid_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_finite_sum_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Genuine uniform signed grid L² estimate without a pathwise convergence assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ n : ℕ, (n : ℝ) * h ≤ T →
          (∫⁻ ω, ‖(∑ i ∈ Finset.range n,
            g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
               X.X ((i : ℝ≥0) * Real.toNNReal h) ω))‖ₑ ^ (2 : ℕ) ∂P)
          ≤ M ^ 2 * (ENNReal.ofReal (C * T) +
                         (ENNReal.ofReal (C * T)) ^ 2) := by
  obtain ⟨C, hC, hgrid⟩ :=
    avram_p2_original_bounded_negative_test_grid_l2_bound
      X ε hε T hT f M hM hf
  refine ⟨C, hC, ?_⟩
  filter_upwards [hgrid] with h hsmall
  intro n htime
  have hdom : ∀ ω, ‖(∑ i ∈ Finset.range n,
      g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
         X.X ((i : ℝ≥0) * Real.toNNReal h) ω))‖ₑ ≤
      (∑ i ∈ Finset.range n,
        f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal h) ω)) := by
    intro ω
    exact avram_p2_j_ui_signed_finite_sum_envelope
      (Finset.range n)
      (fun i => g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal h) ω))
      (fun i => f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal h) ω))
      (fun i hi => hg _)
  calc
    (∫⁻ ω, ‖(∑ i ∈ Finset.range n,
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal h) ω))‖ₑ ^ (2 : ℕ) ∂P) ≤
      (∫⁻ ω, (∑ i ∈ Finset.range n,
        f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal h) ω)) ^ (2 : ℕ) ∂P) := by
          apply lintegral_mono
          intro ω
          exact ENNReal.pow_le_pow_left (hdom ω)
    _ ≤ M ^ 2 * (ENNReal.ofReal (C * T) +
                    (ENNReal.ofReal (C * T)) ^ 2) :=
      hsmall n htime
