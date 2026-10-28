-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_stop_future_increment_cylinder_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:38:49.531366+00:00
-- url     : https://prove2.me/submissions/f0043e3d-4fce-4371-988d-0cb23793a183

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators
/-- Finite-grid stopping preserves the genuine Esscher future-increment cylinder law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid) (hT : ∀ s ∈ grid, s + u ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid, MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  classical
  let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  let R : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
  let C : ℝ≥0 → Set Ω := fun s =>
    (A ∩ {ω : Ω | τ ω = s}) ∩
      (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B
  have hFib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s} := by
    intro s hs; exact (𝓕.le s) _ (hstop s hs)
  have hC : ∀ s ∈ grid, MeasurableSet (C s) := by
    intro s hs
    have hY : Measurable (fun ω : Ω => X.X (s + u) ω - X.X s ω) :=
      ((X.adapted (s + u)).mono (𝓕.le (s + u)) le_rfl).sub
        ((X.adapted s).mono (𝓕.le s) le_rfl)
    exact ((𝓕.le s) _ (hHistory s hs)).inter (hY hB)
  have hDisj : (↑grid : Set ℝ≥0).PairwiseDisjoint C := by
    intro s hs t ht hne
    apply Set.disjoint_left.mpr
    intro ω hωs hωt
    exact hne (hωs.1.2.symm.trans hωt.1.2)
  have hCover :
      A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} =
        ⋃ s ∈ grid, C s := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨ha, hb⟩; exact ⟨τ ω, hgrid ω, ⟨⟨ha, rfl⟩, hb⟩⟩
    · rintro ⟨s, hs, ⟨⟨ha, hτs⟩, hb⟩⟩
      subst s; exact ⟨ha, hb⟩
  have hPartition : Q A = ∑ s ∈ grid, Q (A ∩ {ω : Ω | τ ω = s}) :=
    finiteGrid_stoppedEvent_measure_partition Q τ A grid hgrid hA hFib
  change Q (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    Q A * R ((X.X u) ⁻¹' B)
  calc
    Q (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
        ∑ s ∈ grid, Q (C s) := by rw [hCover]; exact measure_biUnion_finset hDisj hC
    _ = ∑ s ∈ grid,
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
          (A ∩ {ω : Ω | τ ω = s}) * R ((X.X u) ⁻¹' B) := by
          apply Finset.sum_congr rfl; intro s hs
          exact esscher_terminal_increment_cylinder_factorization X θ hθ s u T
            (hT s hs) (A ∩ {ω : Ω | τ ω = s}) (hHistory s hs) B hB
    _ = ∑ s ∈ grid, Q (A ∩ {ω : Ω | τ ω = s}) * R ((X.X u) ⁻¹' B) := by
          apply Finset.sum_congr rfl; intro s hs
          have hsT : s ≤ T := le_trans (le_add_of_nonneg_right (show 0 ≤ u from zero_le)) (hT s hs)
          exact congrArg (fun z : ℝ≥0∞ => z * R ((X.X u) ⁻¹' B))
            (chat04_esscher_finite_horizon_laws_consistent_on_past_events
              X θ hθ s T hsT _ (hHistory s hs))
    _ = (∑ s ∈ grid, Q (A ∩ {ω : Ω | τ ω = s})) *
        R ((X.X u) ⁻¹' B) := by rw [Finset.sum_mul]
    _ = Q A * R ((X.X u) ⁻¹' B) := by rw [← hPartition]
