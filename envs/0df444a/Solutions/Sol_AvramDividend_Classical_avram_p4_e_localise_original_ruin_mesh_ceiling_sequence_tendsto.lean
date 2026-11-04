-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_mesh_ceiling_sequence_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:46:54.517036+00:00
-- url     : https://prove2.me/submissions/096c8112-b8f5-4f32-8280-cf84d2ff7619

import Mathlib
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_first_ceiling_clock_mesh_error
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact source ruin-clipped clock has finite first-ceiling grids converging from above. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (N : ℕ → ℕ) (hN : ∀ k, (n : ℝ≥0) ≤ e k (N k))
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (h0 : ∀ k, e k 0 = 0)
    (hStep : ∀ k i, e k (i + 1) ≤ e k i + δ k) :
    ∃ K : ℕ → Ω → ℕ,
      ∀ ω, Tendsto (fun k => e k (K k ω)) atTop (𝓝 (τ ω)) := by
  classical
  have hτN : ∀ k ω, τ ω ≤ e k (N k) := by
    intro k ω
    rw [hτeq ω]
    have hn := (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
    exact hn.trans (hN k)
  let cover : ∀ k ω, ∃ j : ℕ, τ ω ≤ e k j :=
    fun k ω => ⟨N k, hτN k ω⟩
  let K : ℕ → Ω → ℕ := fun k ω =>
    @Nat.find (fun j : ℕ => τ ω ≤ e k j)
      (Classical.decPred (fun j : ℕ => τ ω ≤ e k j)) (cover k ω)
  have hBounds : ∀ k ω, τ ω ≤ e k (K k ω) ∧
      e k (K k ω) ≤ τ ω + δ k := by
    intro k ω
    exact avram_p4_e_localise_original_first_ceiling_clock_mesh_error
      X x D n τ hτeq (e k) (he k) (N k) (hτN k)
      (δ k) (h0 k) (hStep k) ω
  refine ⟨K, ?_⟩
  have hLower : ∀ k ω, τ ω ≤ e k (K k ω) :=
    fun k ω => (hBounds k ω).1
  have hUpper : ∀ k ω, e k (K k ω) ≤ τ ω + δ k :=
    fun k ω => (hBounds k ω).2
  exact avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
    X x D n τ hτeq e K δ hδ hLower hUpper
