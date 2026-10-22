-- Prove2me | solution 1 for AvramDividend.Classical.chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:44:18.486119+00:00
-- url     : https://prove2.me/submissions/f703d5cf-3c2c-435f-94c7-271fc24634ed

import Theorems.Thm_AvramDividend_Classical_chat03_tendsto_first_passage_of_mesh_brackets
import Theorems.Thm_AvramDividend_Classical_chat03_finite_grid_clock_tendsto_ennreal
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
For an extended-real sampled clock that may be infinite on coarse meshes,
eventual finite epsilon brackets suffice for convergence to a finite clock.
-/
theorem solution
    (τ : ℝ≥0) (mesh : ℕ → ℝ≥0) (σ : ℕ → ℝ≥0∞)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hbracket : ∀ ε : ℝ≥0, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ n : ℕ, mesh n < δ →
          (τ : ℝ≥0∞) ≤ σ n ∧
          σ n < ((τ + ε : ℝ≥0) : ℝ≥0∞)) :
    Tendsto σ atTop (𝓝 (τ : ℝ≥0∞)) := by
  have hfinite : ∀ᶠ n : ℕ in atTop, σ n ≠ ∞ := by
    obtain ⟨δ, hδ, hbound⟩ := hbracket 1 (by norm_num)
    have hsmall : ∀ᶠ n : ℕ in atTop, mesh n < δ :=
      hzero.eventually (Iio_mem_nhds hδ)
    filter_upwards [hsmall] with n hn
    exact ne_of_lt (lt_of_lt_of_le (hbound n hn).2 le_top)
  have hNN : Tendsto (fun n => (σ n).toNNReal) atTop (𝓝 τ) := by
    apply chat03_tendsto_first_passage_of_mesh_brackets τ mesh _ hzero
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hbracket ε hε
    refine ⟨δ, hδ, ?_⟩
    intro n hn
    obtain ⟨hlo, hhi⟩ := hbound n hn
    have hfin : σ n ≠ ∞ :=
      ne_of_lt (lt_of_lt_of_le hhi le_top)
    have hcoe : ((σ n).toNNReal : ℝ≥0∞) = σ n :=
      ENNReal.coe_toNNReal hfin
    constructor
    · apply ENNReal.coe_le_coe.mp
      rw [hcoe]
      exact hlo
    · apply ENNReal.coe_lt_coe.mp
      rw [hcoe]
      exact hhi
  have hEN : Tendsto (fun n => ((σ n).toNNReal : ℝ≥0∞))
      atTop (𝓝 (τ : ℝ≥0∞)) :=
    chat03_finite_grid_clock_tendsto_ennreal
      (τ : ℝ≥0∞) (by simp) (fun n => (σ n).toNNReal)
      (by simpa using hNN)
  apply hEN.congr'
  filter_upwards [hfinite] with n hn
  exact ENNReal.coe_toNNReal hn
