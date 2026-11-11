-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_rightcont_upper_grid_stops
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:51:42.241395+00:00
-- url     : https://prove2.me/submissions/6ca05083-8db3-4fa0-bd62-23e6bb9b3efd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_stopping_from_variable_mesh
import Theorems.Thm_AvramDividend_Classical_avram_ja18_nnreal_dyadic_mesh_data
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Compose a deterministic shrinking dyadic mesh with original stopped
clock discretisation, retaining the original filtration and horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (n : ℕ) (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ k ω : WithTop ℝ≥0))) ∧
      (∀ k, ∃ S : Finset ℝ≥0, ∀ ω, ρ k ω ∈ S) ∧
      (∀ k ω, τ ω ≤ ρ k ω) ∧
      (∀ k ω, ρ k ω ≤ (n : ℝ≥0)) ∧
      (∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) := by
  obtain ⟨e, N, δ, he, h0, hStep, hTop, hδ⟩ :=
    avram_ja18_nnreal_dyadic_mesh_data n
  exact avram_ja18_original_stopping_from_variable_mesh
    τ hτ n hBound e N δ he h0 hStep hTop hδ
