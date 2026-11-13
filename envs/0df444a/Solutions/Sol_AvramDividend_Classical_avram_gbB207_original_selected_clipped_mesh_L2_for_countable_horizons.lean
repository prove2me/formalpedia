-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB207_original_selected_clipped_mesh_L2_for_countable_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:38:44.316042+00:00
-- url     : https://prove2.me/submissions/66019468-7d32-4b33-8595-ed18f3441b58

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB205_original_choose_good_levels_for_countable_mesh_limits
import Theorems.Thm_AvramDividend_Classical_avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Selected original cutoffs yield countably simultaneous integrated L2 convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (ρ : ℕ → Ω → ℝ≥0) (q : ℝ) (w : ℝ → ℝ)
    (alo ahi blo bhi : ℝ) (ha : alo < ahi)
    (hSep : ahi < blo) (hb : blo < bhi)
    (hDeriv : ∀ y ∈ Ioo alo bhi, ContinuousAt (deriv w) y) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    let K : ℝ → ℝ → ℕ → ℕ → ℝ → Ω → ℝ := fun a b k m t ω =>
      let Δ : ℝ≥0 := ((n k : ℕ) : ℝ≥0) /
        ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ) then
          if (s : ℝ) < (ρ k ω : ℝ) then
            Real.exp (-(q * (s : ℝ))) *
              (if Y (Real.toNNReal (s : ℝ)) ω ∈ Icc a b
                then deriv w (Y (Real.toNNReal (s : ℝ)) ω)
                else 1)
          else 0
        else 0)
    let H : ℝ → ℝ → ℕ → ℝ → Ω → ℝ := fun a b k t ω =>
      if t < (ρ k ω : ℝ) then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b
            then deriv w (Y (Real.toNNReal t) ω)
            else 1)
      else 0
    (∀ a ∈ Ioo alo ahi, ∀ b ∈ Ioo blo bhi,
      ∀ k m, Measurable (fun z : ℝ × Ω =>
        K a b k m z.1 z.2)) →
    (∀ a ∈ Ioo alo ahi, ∀ b ∈ Ioo blo bhi,
      ∀ k, Measurable (fun z : ℝ × Ω =>
        H a b k z.1 z.2)) →
    (∀ a ∈ Ioo alo ahi, ∀ b ∈ Ioo blo bhi,
      ∀ k, ∃ BK BH : ℝ, 0 ≤ BK ∧ 0 ≤ BH ∧
        (∀ m t ω, t ∈ Ioo (0 : ℝ) ((n k : ℕ) : ℝ) →
          |K a b k m t ω| ≤ BK) ∧
        (∀ t ω, t ∈ Ioo (0 : ℝ) ((n k : ℕ) : ℝ) →
          |H a b k t ω| ≤ BH)) →
    ∃ a ∈ Ioo alo ahi, ∃ b ∈ Ioo blo bhi,
      ∀ k : ℕ,
        Tendsto (fun m : ℕ =>
          ∫ t in Ioo (0 : ℝ) ((n k : ℕ) : ℝ),
            (∫ ω, (K a b k m t ω - H a b k t ω)^2 ∂P)
            ∂volume) atTop (𝓝 (0 : ℝ)) := by
  intro Y K H hKm hHm hBound
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨a, haGood, b, hbGood, hAE⟩ :=
    avram_gbB205_original_choose_good_levels_for_countable_mesh_limits
      X hν x D hD n hn ρ q w alo ahi blo bhi ha hSep hb hDeriv
  refine ⟨a, haGood, b, hbGood, ?_⟩
  intro k
  obtain ⟨BK, BH, hBK, hBH, hKb, hHb⟩ :=
    hBound a haGood b hbGood k
  have hAEk := hAE k
  exact
    avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
      P (n k) (hn k) (K a b k) (H a b k)
      (hKm a haGood b hbGood k)
      (hHm a haGood b hbGood k)
      BK BH hBK hBH hKb hHb
      (by simpa only [K, H] using hAEk)

