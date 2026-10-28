-- Prove2me | solution 2 for AvramDividend.Classical.esscher_finite_grid_stop_future_increment_cylinder_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:40:14.457986+00:00
-- url     : https://prove2.me/submissions/dd02494e-9ee6-4296-a582-2db2217fc1b7

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s + u ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  set μ := P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))) with hμ
  have hXm : ∀ r, Measurable (X.X r) := fun r =>
    (X.adapted r).mono (𝓕.le r) le_rfl
  have hfib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s} := fun s hs => 𝓕.le s _ (hstop s hs)
  have hinc : ∀ s, MeasurableSet ((fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) := fun s =>
    hB.preimage ((hXm _).sub (hXm _))
  -- decompose the event along the grid
  have hset : A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} =
      ⋃ s ∈ grid, (A ∩ {ω : Ω | τ ω = s}) ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_preimage, exists_prop]
    constructor
    · rintro ⟨hA, hB⟩; exact ⟨τ ω, hgrid ω, ⟨hA, rfl⟩, hB⟩
    · rintro ⟨s, -, ⟨hA, rfl⟩, hB⟩; exact ⟨hA, hB⟩
  rw [hset, measure_biUnion_finset]
  · rw [finiteGrid_stoppedEvent_measure_partition μ τ A grid hgrid hA hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hμ, esscher_terminal_increment_cylinder_factorization X θ hθ s u T (hT s hs) _
      (hHistory s hs) B hB]
    congr 1
    have h := chat04_esscher_finite_horizon_laws_consistent_on_past_events X θ hθ s T
      (le_trans le_self_add (hT s hs)) _ (hHistory s hs)
    exact h
  · intro s _ s' _ hss'
    refine Set.disjoint_left.2 fun ω h1 h2 => hss' ?_
    exact h1.1.2.symm.trans h2.1.2
  · intro s hs
    exact (hA.inter (hfib s hs)).inter (hinc s)
