-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB197_original_one_mesh_gaussian_L2_isometry_from_bounded_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:07:47.293297+00:00
-- url     : https://prove2.me/submissions/e80a845a-a0ee-4efd-a851-9264448959bb

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB77_original_zerojump_uniform_bilinear_grid_isometry
import Theorems.Thm_AvramDividend_Classical_avram_gbB196_original_uniform_step_square_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Original bounded predictable one-grid Gaussian L2 identity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (n m : ℕ) (hn : 0 < n) (G : ℕ → ℕ → Ω → ℝ)
    (hAdapt : ∀ (k i : ℕ), Measurable[𝓕.rightCont
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))] (G k i))
    (hStrong : ∀ k i, StronglyMeasurable (G k i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ k i ω, |G k i ω| ≤ B) :
    let L : ℕ → Ω → ℝ := fun k ω =>
      let δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
      (Finset.range (k + 1)).sum (fun i =>
        G k i ω * (X.X (s i + δ) ω -
          X.X (s i) ω - (δ : ℝ) * X.c))
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    (∫ ω, (L m ω) ^ 2 ∂P) =
      X.σ ^ 2 * (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K m t ω) ^ 2 ∂P) ∂volume) := by
  intro L K
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B, hB, hGb⟩ := hBound
  have hFixed : ∃ B : ℝ, 0 ≤ B ∧
      ∀ i ω, |G m i ω| ≤ B :=
    ⟨B, hB, fun i ω => hGb m i ω⟩
  have hOne (i : ℕ) :
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))]
        (G m i) := hAdapt m i
  have h77 := avram_gbB77_original_zerojump_uniform_bilinear_grid_isometry
    X hν n (m + 1) hn (Nat.succ_pos m)
      (G m) (G m) hOne hOne hFixed hFixed
  have h196 := avram_gbB196_original_uniform_step_square_energy
    P n m hn G hStrong ⟨B, hB, hGb⟩
  have hD :
      (((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) : ℝ) =
        (n : ℝ) / ((m : ℝ) + 1) := by
    norm_num
  calc
    (∫ ω, (L m ω) ^ 2 ∂P) =
        ((((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) : ℝ) *
          X.σ ^ 2) *
          (Finset.range (m + 1)).sum (fun i =>
            ∫ ω, (G m i ω) ^ 2 ∂P) := by
      convert h77 using 1 <;> simp [L, pow_two]
    _ = X.σ ^ 2 * (∫ t in Ioo (0 : ℝ) (n : ℝ),
          (∫ ω, (K m t ω) ^ 2 ∂P) ∂volume) := by
      rw [hD]
      simpa only [K] using (by
        rw [h196]
        ring)

