-- Prove2me | solution 1 for AvramDividend.Classical.bounded_stop_explicit_grid_increment_limit_with_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:56:51.672131+00:00
-- url     : https://prove2.me/submissions/aa5baa39-bc23-4e72-82ff-3d3ba54c77d9

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Constructions
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_mem_finite_nnreal_grid
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_fibre_measurable
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_finite_grid_le_bound
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
/-- Explicit upper dyadic finite grids with bounded support and pointwise
future-increment convergence for a bounded Lévy stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) (u : ℝ≥0) :
    let τn : ℕ → Ω → ℝ≥0 := fun n ω =>
      (Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
        (2 : ℝ≥0) ^ n
    let grid : ℕ → Finset ℝ≥0 := fun n =>
      (Finset.range (Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) + 1)).image
        (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n)
    (∀ n ω, τn n ω ∈ grid n) ∧
    (∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
    (∀ n s, s ∈ grid n → s ≤ H + 1) ∧
    (∀ ω n, τ ω ≤ τn n ω) ∧
    (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) ∧
    (∀ ω, Tendsto
      (fun n => X.X (τn n ω + u) ω - X.X (τn n ω) ω)
      atTop (𝓝 (X.X (τ ω + u) ω - X.X (τ ω) ω))) := by
  classical
  dsimp
  let τn : ℕ → Ω → ℝ≥0 := fun n ω =>
    (Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
      (2 : ℝ≥0) ^ n
  let grid : ℕ → Finset ℝ≥0 := fun n =>
    (Finset.range (Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) + 1)).image
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n)
  have habove : ∀ ω n, τ ω ≤ τn n ω := by
    intro ω n
    exact dyadic_ceiling_time_ge_nnreal (τ ω) n
  have hconv : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)) := by
    intro ω
    exact dyadic_ceiling_nnreal_tendsto (τ ω)
  refine ⟨?_, ?_, ?_, habove, hconv, ?_⟩
  · intro n ω
    exact dyadic_ceiling_time_mem_finite_nnreal_grid
      (τ ω) H (hbound ω) n
  · intro n s hs
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hs
    have hinj : ∀ a b : ℕ,
        (a : ℝ≥0) / (2 : ℝ≥0) ^ n =
        (b : ℝ≥0) / (2 : ℝ≥0) ^ n → a = b := by
      intro a b h
      have h2 : (2 : ℝ≥0) ^ n ≠ 0 := by positivity
      rw [div_left_inj' h2] at h
      exact_mod_cast h
    have heq : {ω : Ω | τn n ω =
        (k : ℝ≥0) / (2 : ℝ≥0) ^ n} =
        {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => hinj _ _ h, fun h => by simp only [τn, h]⟩
    rw [heq]
    exact dyadic_ceiling_index_fibre_measurable 𝓕 τ hstop n k
  · intro n s hs
    exact dyadic_ceiling_finite_grid_le_bound H n s hs
  · intro ω
    exact chat08_stopped_levy_increment_tendsto_of_right_approximation
      X τn τ u hconv habove ω
