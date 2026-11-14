-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_gaussian_limit_increment_canonical_future_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:18:13.243234+00:00
-- url     : https://prove2.me/submissions/ed814b6d-014f-4902-90aa-c0d0eef92fca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a23_every_cutoff_increment_shift_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_measurable_real_sequence_limit_default_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physical Gaussian limit increment has a canonical measurable future-path representative. -/
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
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ Wlim : (ℝ≥0 → ℝ) → ℝ,
      Measurable Wlim ∧
      (∀ᵐ ω ∂P,
        Wlim (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) =
          R t ω - R s ω) := by
  let Shift : Ω → (ℝ≥0 → ℝ) := fun ω u =>
    X.X (s + u) ω - X.X s ω
  have hCut (n : ℕ) :
      ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
        ∀ ω : Ω,
          avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
            avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
              W (Shift ω) :=
    avram_a23_every_cutoff_increment_shift_borel_20261113
      X hX hFinite n s t hst
  let W : ℕ → (ℝ≥0 → ℝ) → ℝ :=
    fun n => Classical.choose (hCut n)
  have hW (n : ℕ) : Measurable (W n) :=
    (Classical.choose_spec (hCut n)).1
  have hSource (n : ℕ) (ω : Ω) :
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
          W n (Shift ω) :=
    (Classical.choose_spec (hCut n)).2 ω
  obtain ⟨Wlim, hMeas, hLim⟩ :=
    avram_a23_measurable_real_sequence_limit_default_20261113 W hW
  refine ⟨Wlim, hMeas, ?_⟩
  filter_upwards [hR] with ω hω
  have hSeq :
      (fun n : ℕ => W n (Shift ω)) =
      (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω) := by
    funext n
    exact (hSource n ω).symm
  have hTend : Tendsto (fun n : ℕ => W n (Shift ω))
      atTop (𝓝 (R t ω - R s ω)) := by
    rw [hSeq]
    exact (hω t).sub (hω s)
  exact hLim (Shift ω) (R t ω - R s ω) hTend
