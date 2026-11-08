-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_integrable_original_grid_localisation_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:02:57.021102+00:00
-- url     : https://prove2.me/submissions/e9b7a551-77f2-47a0-a05c-5ce6b88c152f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Original finite-grid clipping has vanishing absolute expected tail for
any integrable original source, with no Brownian-process substitution. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f P) :
    Tendsto (fun k : ℕ =>
      ∫ ω : Ω, if ω ∈ {z : Ω | ∀ i ∈ Finset.range (n + 1),
          abs (a z i) ≤ (k : ℝ)} then (0 : ℝ) else abs (f ω) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let A : ℕ → Set Ω := fun k =>
    {ω | ∀ i ∈ Finset.range (n + 1), abs (a ω i) ≤ (k : ℝ)}
  have hA (k : ℕ) : MeasurableSet (A k) := by
    exact avram_bv_residual10_finite_coordinate_event_measurable n a ha (k : ℝ)
  have hmeas (k : ℕ) :
      AEStronglyMeasurable
        (fun ω : Ω => if ω ∈ A k then (0 : ℝ) else abs (f ω)) P := by
    exact (Measurable.ite (hA k) measurable_const hfm.abs).aestronglyMeasurable
  have hdom (k : ℕ) : ∀ᵐ ω ∂P,
      ‖if ω ∈ A k then (0 : ℝ) else abs (f ω)‖ ≤ abs (f ω) := by
    filter_upwards [] with ω
    by_cases hk : ω ∈ A k
    · simp [hk]
    · simp [hk]
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => if ω ∈ A k then (0 : ℝ) else abs (f ω))
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with ω
    obtain ⟨N, hN⟩ := avram_bv_residual10_finite_coordinate_event_exhaustion n a ω
    have hevent : ∀ᶠ k : ℕ in atTop, ω ∈ A k :=
      (eventually_ge_atTop N).mono (fun k hk => hN k hk)
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [hevent] with k hk
    simp [hk]
  have hdct := tendsto_integral_of_dominated_convergence
    (F := fun k ω => if ω ∈ A k then (0 : ℝ) else abs (f ω))
    (f := fun _ => (0 : ℝ)) (fun ω => abs (f ω))
    hmeas hf.abs hdom hlim
  simpa [A] using hdct
