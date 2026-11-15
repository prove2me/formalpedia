-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB64_original_gaussian_compact_band_all_fullcell_spatial_value_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:55:52.023613+00:00
-- url     : https://prove2.me/submissions/f41e33a1-76d8-474d-af94-9bb687198912

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (V : ℝ → ℝ)
    (lo hi L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u ∈ Icc lo hi, ∀ v ∈ Icc lo hi,
      |V v - V u| ≤ L * |v - u|)
    (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          x + X.X s ω - rightLimit D s ω ∈ Icc lo hi →
          x + X.X (s + Δ) ω - rightLimit D s ω ∈ Icc lo hi →
          |V (x + X.X (s + Δ) ω - rightLimit D s ω) -
            V (x + X.X s ω - rightLimit D s ω)| < ε := by
  have hRaw :=
    avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
      X hν n
  filter_upwards [hRaw] with ω hω
  intro ε hε
  have hLp : 0 < L + 1 := by linarith
  have hη : 0 < ε / (L + 1) := div_pos hε hLp
  obtain ⟨k,hk⟩ := hω (ε / (L + 1)) hη
  refine ⟨k, ?_⟩
  intro m hm i him
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  change
    x + X.X s ω - rightLimit D s ω ∈ Icc lo hi →
    x + X.X (s + Δ) ω - rightLimit D s ω ∈ Icc lo hi →
    |V (x + X.X (s + Δ) ω - rightLimit D s ω) -
      V (x + X.X s ω - rightLimit D s ω)| < ε
  intro hy hz
  have hSource : |X.X (s + Δ) ω - X.X s ω| <
      ε / (L + 1) := hk m hm i him
  have hEq :
      |(x + X.X (s + Δ) ω - rightLimit D s ω) -
        (x + X.X s ω - rightLimit D s ω)| =
      |X.X (s + Δ) ω - X.X s ω| := by
    congr 1
    ring
  have hBound := hLip
    (x + X.X s ω - rightLimit D s ω) hy
    (x + X.X (s + Δ) ω - rightLimit D s ω) hz
  have hDenom : (ε / (L + 1)) * (L + 1) = ε :=
    div_mul_cancel₀ ε (ne_of_gt hLp)
  have hSmall : L * (ε / (L + 1)) < ε := by
    nlinarith
  calc
    |V (x + X.X (s + Δ) ω - rightLimit D s ω) -
      V (x + X.X s ω - rightLimit D s ω)| ≤
        L * |(x + X.X (s + Δ) ω - rightLimit D s ω) -
          (x + X.X s ω - rightLimit D s ω)| := hBound
    _ = L * |X.X (s + Δ) ω - X.X s ω| := by rw [hEq]
    _ ≤ L * (ε / (L + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hSource) hL
    _ < ε := hSmall
