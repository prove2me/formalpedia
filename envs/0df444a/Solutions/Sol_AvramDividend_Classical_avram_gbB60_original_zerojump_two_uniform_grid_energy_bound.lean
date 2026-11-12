-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB60_original_zerojump_two_uniform_grid_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:53:04.447988+00:00
-- url     : https://prove2.me/submissions/91f191d1-5fc9-440c-a54b-1e5ae6e8b4cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB69_two_uniform_grid_common_refinement_telescoping
import Theorems.Thm_AvramDividend_Classical_avram_gbB70_original_zerojump_single_uniform_mesh_predictable_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_gbB71_common_refinement_coarse_start_le_fine_start
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hAdapt : ∀ (m i : ℕ),
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))]
        (G m i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ m i ω, |G m i ω| ≤ B) :
    let L : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        G m i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
          (Δ : ℝ) * X.c))
    let E : ℕ × ℕ → ℝ := fun nm =>
      let m : ℕ := nm.1
      let p : ℕ := nm.2
      let N : ℕ := (m + 1) * (p + 1)
      let Δ : ℝ := (n : ℝ) / (N : ℝ)
      Δ * (Finset.range N).sum (fun i =>
        ∫ ω, (G m (i / (p + 1)) ω -
          G p (i / (m + 1)) ω) ^ 2 ∂P)
    ∀ (m p : ℕ),
      0 ≤ (∫ ω, (L m ω - L p ω) ^ 2 ∂P) ∧
      (∫ ω, (L m ω - L p ω) ^ 2 ∂P) ≤
        X.σ ^ 2 * E (m, p) := by
  intro L E m p
  let N : ℕ := (m + 1) * (p + 1)
  let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let H : ℕ → Ω → ℝ := fun i ω =>
    G m (i / (p + 1)) ω - G p (i / (m + 1)) ω
  let V : Ω → ℝ := fun ω =>
    (Finset.range N).sum (fun i =>
      H i ω * (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c))
  have hN : 0 < N := by dsimp [N]; positivity
  have hAdaptH : ∀ i : ℕ, Measurable[𝓕.rightCont
      ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i) := by
    intro i
    have hm := avram_gbB71_common_refinement_coarse_start_le_fine_start i m p
      (n : ℝ≥0)
    have hp := avram_gbB71_common_refinement_coarse_start_le_fine_start i p m
      (n : ℝ≥0)
    rw [Nat.mul_comm (p + 1) (m + 1)] at hp
    have hm0 := hAdapt m (i / (p + 1))
    have hp0 := hAdapt p (i / (m + 1))
    have hm1 := hm0.mono (𝓕.rightCont.mono hm) le_rfl
    have hp1 := hp0.mono (𝓕.rightCont.mono hp) le_rfl
    exact hm1.sub hp1
  obtain ⟨B, hB, hGB⟩ := hBound
  have hBoundH : ∃ B' : ℝ, 0 ≤ B' ∧ ∀ i ω, |H i ω| ≤ B' := by
    refine ⟨2 * B, by positivity, ?_⟩
    intro i ω
    dsimp [H]
    calc
      |G m (i / (p + 1)) ω - G p (i / (m + 1)) ω|
          ≤ |G m (i / (p + 1)) ω| +
              |G p (i / (m + 1)) ω| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le (G m (i / (p + 1)) ω)
                (-(G p (i / (m + 1)) ω)))
      _ ≤ B + B := add_le_add (hGB m (i / (p + 1)) ω)
        (hGB p (i / (m + 1)) ω)
      _ = 2 * B := by ring
  have hSingle := avram_gbB70_original_zerojump_single_uniform_mesh_predictable_L2_energy
    X hν n N hn hN H hAdaptH hBoundH
  have hPath : ∀ ω, L m ω - L p ω = V ω := by
    intro ω
    simpa only [L, V, H, N, Δ, s] using
      (avram_gbB69_two_uniform_grid_common_refinement_telescoping
        X.X X.c n m p G ω)
  have hV : 0 ≤ (∫ ω, (V ω) ^ 2 ∂P) ∧
      (∫ ω, (V ω) ^ 2 ∂P) ≤
        X.σ ^ 2 * ((n : ℝ) / (N : ℝ)) *
          (Finset.range N).sum (fun i => ∫ ω, (H i ω) ^ 2 ∂P) := by
    simpa only [V, N, Δ, s] using hSingle
  simp_rw [hPath]
  simpa only [E, N, H, mul_assoc] using hV
