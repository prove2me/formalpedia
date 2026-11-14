-- Prove2me | solution 1 for AvramDividend.Classical.avram_b159_original_true_unmarked_cell_ae_gaussian_source_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:47:33.217302+00:00
-- url     : https://prove2.me/submissions/81a32b18-6a5e-4022-b874-d5c67bd8afe4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original unmarked physical random source cells obey the intrinsic Gaussian signed-drift decomposition almost everywhere by collapsing marked cells to zero duration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (Marked : Ω → Prop)
    (hOriginalUnmarked : ∀ ω, ¬ Marked ω → ∀ u : ℝ≥0,
      s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ᵐ ω ∂P, ¬ Marked ω →
      X.X (t ω) ω - X.X (s ω) ω =
        ((t ω : ℝ) - (s ω : ℝ)) *
          (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
        (R (t ω) ω - R (s ω) ω) := by
  classical
  let α : Ω → ℝ≥0 := fun ω => if Marked ω then t ω else s ω
  have hαorder (ω : Ω) : α ω ≤ t ω := by
    by_cases hm : Marked ω
    · simp [α, hm]
    · simpa [α, hm] using hOrder ω
  have hNoJumpAll (ω : Ω) (u : ℝ≥0) (hsu : α ω < u) (hut : u ≤ t ω) :
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
    by_cases hm : Marked ω
    · have htlt : t ω < u := by simpa [α, hm] using hsu
      exact False.elim ((not_lt_of_ge hut) htlt)
    · exact hOriginalUnmarked ω hm u (by simpa [α, hm] using hsu) hut
  have hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, α ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 :=
    Filter.Eventually.of_forall hNoJumpAll
  obtain ⟨M, hM, hAe⟩ :=
    avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
      X hFinite R Jsmall hRsrc hJsrc α t hαorder hNoJump
  filter_upwards [hAe] with ω hω
  intro hNot
  simpa [α, hNot] using hω
