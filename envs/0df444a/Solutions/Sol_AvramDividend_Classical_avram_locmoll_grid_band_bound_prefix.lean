-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_grid_band_bound_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:19:33.790697+00:00
-- url     : https://prove2.me/submissions/43a143dc-3af2-4d23-bf37-8382a75325d0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f17_dense_range_right_neighbourhood_sample
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_right_continuous_grid_detection
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (H : ℝ≥0) (δ R : ℕ → ℝ)
    (hδ : Antitone δ) (hR : Monotone R)
    (r : ℕ → ℝ≥0) (hr : DenseRange r) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
    let E : ℕ → Ω → ℕ → ℝ≥0 := fun k ω j =>
      if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H
    let θ : ℕ → Ω → ℝ≥0 := fun k ω => ⨅ j, E k ω j
    (∀ k ω, θ k ω ≤ H) ∧
    (∀ k ω t, t < θ k ω → Y t ω ∈ Icc (δ k) (R k)) := by 
  dsimp only
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
  let E : ℕ → Ω → ℕ → ℝ≥0 := fun k ω j =>
    if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H
  let θ : ℕ → Ω → ℝ≥0 := fun k ω => ⨅ j, E k ω j
  have hθ (k : ℕ) (ω : Ω) (j : ℕ) : θ k ω ≤ E k ω j :=
    ciInf_le (OrderBot.bddBelow _) j
  have hgrid := avram_f17_dense_range_right_neighbourhood_sample r hr
  constructor
  · intro k ω
    exact (hθ k ω 0).trans (by dsimp [E]; split <;> simp)
  · intro k ω t ht
    by_contra hc
    have he : Y t ω < δ k ∨ R k < Y t ω := by
      change ¬ (δ k ≤ Y t ω ∧ Y t ω ≤ R k) at hc
      push_neg at hc
      by_cases hh : Y t ω < δ k
      · exact Or.inl hh
      · exact Or.inr (hc (le_of_not_gt hh))
    obtain ⟨j, hj, hej⟩ :=
      avram_wave7_18_original_right_continuous_grid_detection
        X x D hD r (δ k) (R k) hgrid ω t (θ k ω) ht he
    have h := hθ k ω j
    change θ k ω ≤ (if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H) at h
    rw [if_pos (show Y (r j) ω < δ k ∨ R k < Y (r j) ω from hej)] at h
    exact (not_lt_of_ge (h.trans (min_le_left _ _))) hj

