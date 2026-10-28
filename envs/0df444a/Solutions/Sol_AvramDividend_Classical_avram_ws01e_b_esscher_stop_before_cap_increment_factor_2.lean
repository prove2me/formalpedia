-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_b_esscher_stop_before_cap_increment_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:16:10.008709+00:00
-- url     : https://prove2.me/submissions/7e66c1e0-e00e-4056-aa41-1c9d01f50779

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot
import Theorems.Thm_AvramDividend_Classical_esscher_locally_bounded_stop_increment_cylinder_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Genuine finite-horizon Esscher regeneration on a first-passage-before-cap event.
The stopping age itself need not be bounded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      ({ω : Ω | τ ω ≤ H} ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
        {ω : Ω | τ ω ≤ H} *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  let A : Set Ω := {ω : Ω | τ ω ≤ H}
  have hτle : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s} := by
    intro s
    simpa only [WithTop.coe_le_coe] using (hStop.measurableSet_le s)
  have hHistory : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    rcases le_total s H with hs | hs
    · have he : A ∩ {ω : Ω | τ ω ≤ s} =
          {ω : Ω | τ ω ≤ s} := by
        apply Set.inter_eq_right.mpr
        intro ω hw
        exact le_trans hw hs
      rw [he]
      exact hτle s
    · have he : A ∩ {ω : Ω | τ ω ≤ s} = A := by
        apply Set.inter_eq_left.mpr
        intro ω hw
        exact le_trans hw hs
      rw [he]
      exact 𝓕.mono hs _ (hτle H)
  exact esscher_locally_bounded_stop_increment_cylinder_factor
    X θ hθ τ hStop H u T hT A hHistory (Set.Subset.rfl) B hB
