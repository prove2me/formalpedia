-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_capped_grid_discounted_scale_mesh_tendsto_of_continuity
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T11:22:41.158836+00:00
-- url     : https://prove2.me/submissions/0f767fe6-b9fb-43bf-8ce2-31286c982f12

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_capped_grid_discounted_scale_of_continuous_reserve

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (discount : ℝ≥0 → ℝ)
    (hdiscount : Continuous discount)
    (hContinuity : ContinuousAt W (x + X.X (min τ T) ω))
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω))) :
    Tendsto (fun n =>
      discount (min ((first n : ℝ≥0) * mesh n) T) *
        W (x + X.X (min ((first n : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (discount (min τ T) * W (x + X.X (min τ T) ω))) := by
  rw [tendsto_nhds]
  intro U hU hmem
  obtain ⟨δ, hδ, hk⟩ := AvramDividend.Classical.avram_ws01b_capped_grid_discounted_scale_of_continuous_reserve
    X q W hW ω lower upper x τ T hτ discount hdiscount U hU hmem hContinuity
  have hsmall : ∀ᶠ n in atTop, mesh n < δ := hmesh.eventually (Iio_mem_nhds hδ)
  filter_upwards [hfirst, hsmall] with n hn hlt
  obtain ⟨k, hk1, hk2, hk3⟩ := hk (mesh n) (hpos n) hlt
  have hkeq : k = first n := by
    rcases lt_trichotomy k (first n) with h | h | h
    · exact absurd hk1 (hn.2 k h)
    · exact h
    · exact absurd hn.1 (hk2 _ h)
  rw [hkeq] at hk3
  exact hk3
