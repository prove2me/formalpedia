-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger22_original_source_fourth_dominates_large_square_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:27:09.61479+00:00
-- url     : https://prove2.me/submissions/cf735a89-ed34-4cf6-8001-e0e0f4922bf2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original Gaussian fourth energy dominates the large-increment quadratic tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (η : ℝ) (hη : 0 < η) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∫⁻ ω, ∑ i ∈ S,
      ENNReal.ofReal ((if η ≤ |Z i ω| then (Z i ω)^2 else 0) * η^2) ∂P)
      ≤ (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω)^4) ∂P) := by
  classical
  let Z : ℕ → Ω → ℝ := fun i ω =>
    X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  have hcell : ∀ z : ℝ,
      (if η ≤ |z| then z^2 else 0) * η^2 ≤ z^4 := by
    intro z
    split_ifs with hz
    · have hzsq : 0 ≤ z^2 := sq_nonneg z
      have habssq : η^2 ≤ (|z|)^2 := by
        have hsum : 0 ≤ |z| + η := by
          have := abs_nonneg z
          linarith
        have hmul : 0 ≤ (|z| - η) * (|z| + η) :=
          mul_nonneg (sub_nonneg.mpr hz) hsum
        nlinarith
      have hηsq : η^2 ≤ z^2 := by
        simpa only [sq_abs] using habssq
      nlinarith [mul_nonneg hzsq (sub_nonneg.mpr hηsq)]
    · nlinarith [sq_nonneg (z ^ 2)]
  apply lintegral_mono
  intro ω
  apply Finset.sum_le_sum
  intro i hi
  exact ENNReal.ofReal_le_ofReal (hcell (Z i ω))
