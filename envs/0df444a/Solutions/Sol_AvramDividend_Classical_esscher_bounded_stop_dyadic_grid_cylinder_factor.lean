-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_dyadic_grid_cylinder_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T22:10:22.939333+00:00
-- url     : https://prove2.me/submissions/6c83cff8-cbe2-4945-9528-98a41085a817

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_future_increment_cylinder_factor
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    ∀ (n : ℕ) (B : Set ℝ), MeasurableSet B →
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω |
        X.X ((Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
          (2 : ℝ≥0) ^ n + u) ω -
        X.X ((Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
          (2 : ℝ≥0) ^ n) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  classical
  let τn : ℕ → Ω → ℝ≥0 := fun n ω =>
    (Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
      (2 : ℝ≥0) ^ n
  let grid : ℕ → Finset ℝ≥0 := fun n =>
    (Finset.range (Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) + 1)).image
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n)
  obtain ⟨hmem, hfib, hgridBound, habove, _, _⟩ :=
    bounded_stop_explicit_grid_increment_limit_with_horizon
      X τ hstop H hbound u
  have hall : ∀ n s, MeasurableSet[𝓕 s]
      {ω : Ω | τn n ω = s} := by
    intro n s
    by_cases hs : s ∈ grid n
    · exact hfib n s hs
    · have he : {ω : Ω | τn n ω = s} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hs (h ▸ hmem n ω)
      simpa [he] using
        (MeasurableSet.empty : MeasurableSet[𝓕 s] (∅ : Set Ω))
  have hMeasA : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hA
  intro n B hB
  change
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω | X.X (τn n ω + u) ω -
        X.X (τn n ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B)
  apply esscher_finite_grid_stop_future_increment_cylinder_factor
    X θ hθ T u (τn n) (grid n) (hmem n)
  · intro s hs
    exact le_trans (add_le_add_left (hgridBound n s hs) u) hT
  · intro s hs
    exact hfib n s hs
  · exact hMeasA
  · intro s hs
    exact stoppedEvent_upperGridFibre_measurable τ A hA τn
      habove hall n s
  · exact hB
