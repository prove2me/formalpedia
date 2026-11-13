-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB83_original_two_mesh_common_refinement_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:23:23.778393+00:00
-- url     : https://prove2.me/submissions/a7970d1a-25ae-4395-9157-a4823c0de13e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB198_single_uniform_grid_weighted_refinement
import Theorems.Thm_AvramDividend_Classical_avram_gbB71_common_refinement_coarse_start_le_fine_start
import Theorems.Thm_AvramDividend_Classical_avram_gbB77_original_zerojump_uniform_bilinear_grid_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (n : ℕ) (hn : 0 < n) (G : ℕ → ℕ → Ω → ℝ)
    (hAdapt : ∀ (m i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))] (G m i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ m i ω, |G m i ω| ≤ B) :
    let L : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i => G m i ω * (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c))
    ∀ m l, (∫ ω, L m ω * L l ω ∂P) = (X.σ ^ 2) * ((n : ℝ) / (((m + 1) * (l + 1) : ℕ) : ℝ)) * (Finset.range ((m + 1) * (l + 1))).sum (fun r => ∫ ω, G m (r / (l + 1)) ω * G l (r / (m + 1)) ω ∂P) := by
  intro L m l
  letI : IsProbabilityMeasure P := X.isProbability
  let N : ℕ := (m + 1) * (l + 1)
  let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun r => (r : ℝ≥0) * Δ
  let Z : ℕ → Ω → ℝ := fun r ω => X.X (s r + Δ) ω - X.X (s r) ω - (Δ : ℝ) * X.c
  let H : ℕ → Ω → ℝ := fun r ω => G m (r / (l + 1)) ω
  let J : ℕ → Ω → ℝ := fun r ω => G l (r / (m + 1)) ω
  have hRefM (ω : Ω) : L m ω = (Finset.range N).sum (fun r => H r ω * Z r ω) := by
    simpa only [L, H, N, Δ, Z, s] using
      (avram_gbB198_single_uniform_grid_weighted_refinement
        X.X X.c n m (l + 1) (Nat.succ_pos l) (G m) ω)
  have hRefL (ω : Ω) : L l ω = (Finset.range N).sum (fun r => J r ω * Z r ω) := by
    simpa only [L, J, N, Δ, Z, s, Nat.mul_comm] using
      (avram_gbB198_single_uniform_grid_weighted_refinement
        X.X X.c n l (m + 1) (Nat.succ_pos m) (G l) ω)
  have hHAdapt (r : ℕ) : Measurable[𝓕.rightCont (s r)] (H r) := by
    have hle :=
      avram_gbB71_common_refinement_coarse_start_le_fine_start
        r m l (n : ℝ≥0)
    exact (hAdapt m (r / (l + 1))).mono
      (𝓕.rightCont.mono hle) le_rfl
  have hJAdapt (r : ℕ) : Measurable[𝓕.rightCont (s r)] (J r) := by
    have hle0 :=
      avram_gbB71_common_refinement_coarse_start_le_fine_start
        r l m (n : ℝ≥0)
    have hle :
        (((r / (m + 1) : ℕ) : ℝ≥0) *
          ((n : ℝ≥0) / ((l + 1 : ℕ) : ℝ≥0))) ≤ s r := by
      simpa only [s, Δ, N, Nat.mul_comm (l + 1) (m + 1)] using hle0
    exact (hAdapt l (r / (m + 1))).mono
      (𝓕.rightCont.mono hle) le_rfl
  obtain ⟨B, hB, hGB⟩ := hBound
  have hHB : ∃ B : ℝ, 0 ≤ B ∧ ∀ r ω, |H r ω| ≤ B := ⟨B, hB, fun r ω => hGB m (r / (l + 1)) ω⟩
  have hJB : ∃ B : ℝ, 0 ≤ B ∧ ∀ r ω, |J r ω| ≤ B := ⟨B, hB, fun r ω => hGB l (r / (m + 1)) ω⟩
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos l)
  have h77 := avram_gbB77_original_zerojump_uniform_bilinear_grid_isometry
      X hν n N hn hN H J hHAdapt hJAdapt hHB hJB
  have hWidth : (Δ : ℝ) = (n : ℝ) / (N : ℝ) := by
    simp [Δ]
  calc
    (∫ ω, L m ω * L l ω ∂P) = (∫ ω, ((Finset.range N).sum (fun r => H r ω * Z r ω)) * ((Finset.range N).sum (fun r => J r ω * Z r ω)) ∂P) := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [hRefM ω, hRefL ω]
    _ = ((Δ : ℝ) * X.σ ^ 2) * (Finset.range N).sum (fun r => ∫ ω, H r ω * J r ω ∂P) := by
          simpa only [s, Z, Δ] using h77
    _ = (X.σ ^ 2) * ((n : ℝ) / (N : ℝ)) * (Finset.range N).sum (fun r => ∫ ω, G m (r / (l + 1)) ω * G l (r / (m + 1)) ω ∂P) := by
          rw [hWidth]
          ring
