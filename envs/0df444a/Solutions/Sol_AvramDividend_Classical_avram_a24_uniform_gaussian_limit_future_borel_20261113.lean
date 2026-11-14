-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_uniform_gaussian_limit_future_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:40:58.81639+00:00
-- url     : https://prove2.me/submissions/1d6bd0c4-efe6-4451-86ce-1500e7997876

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_every_gaussian_cutoff_future_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_measurable_real_sequence_limit_default_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One globally Borel future-path functional represents all original Gaussian limit increments of a given duration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (T : ℝ≥0) :
    ∃ Wlim : (ℝ≥0 → ℝ) → ℝ, Measurable Wlim ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ≥0,
        Wlim (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) =
          R (s + T) ω - R s ω) := by
  have hCut (n : ℕ) :
      ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
        ∀ s : ℝ≥0, ∀ ω : Ω,
          avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
            avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
              W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) :=
    avram_a24_uniform_every_gaussian_cutoff_future_borel_20261113
      X hX hFinite n T
  let W : ℕ → (ℝ≥0 → ℝ) → ℝ :=
    fun n => Classical.choose (hCut n)
  have hW (n : ℕ) : Measurable (W n) :=
    (Classical.choose_spec (hCut n)).1
  have hSource (n : ℕ) (s : ℝ≥0) (ω : Ω) :
      avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
          W n (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) :=
    (Classical.choose_spec (hCut n)).2 s ω
  obtain ⟨Wlim, hMeas, hLim⟩ :=
    avram_a23_measurable_real_sequence_limit_default_20261113 W hW
  refine ⟨Wlim, hMeas, ?_⟩
  filter_upwards [hR] with ω hω
  intro s
  let Shift : ℝ≥0 → ℝ := fun u => X.X (s + u) ω - X.X s ω
  have hSeq : (fun n : ℕ => W n Shift) =
      (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω) := by
    funext n
    exact (hSource n s ω).symm
  have hTend : Tendsto (fun n : ℕ => W n Shift)
      atTop (𝓝 (R (s + T) ω - R s ω)) := by
    rw [hSeq]
    exact (hω (s + T)).sub (hω s)
  exact hLim Shift (R (s + T) ω - R s ω) hTend
