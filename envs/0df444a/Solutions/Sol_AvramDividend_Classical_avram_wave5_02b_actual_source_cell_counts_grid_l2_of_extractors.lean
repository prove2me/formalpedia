-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_actual_source_cell_counts_grid_l2_of_extractors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:40:06.565069+00:00
-- url     : https://prove2.me/submissions/a144b8a8-bb95-4dd2-91b9-0b21ff9968ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_poisson_l2_isometry_natural

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (grid : ℕ → ℝ≥0) (C : ℕ → Set ℝ)
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) = K i ω)
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hH : ∀ i, Measurable[𝓕 (grid i)] (H i))
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable
      (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (hPrefixPast : ∀ i, Measurable[𝓕 (grid i)] (fun ω =>
      ∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))))
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω *
        ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
          (r i : ℝ))) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
        (r i : ℝ))) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, (r i : ℝ) * ∫ ω, (H i ω) ^ 2 ∂P := by
  have hJoint : ∀ i, IndepFun (fun ω =>
      ((∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))),
        H i ω)) (K i) P := by
    intro i
    have hi := actual_levy_past_indep_measurable_future_jump_family_ws01b
      X (grid i) _ ((hPrefixPast i).prodMk (hH i)) (Fpath i) (hFpath i)
    have hrep : (fun ω => Fpath i (fun t : ℝ≥0 =>
        X.X (grid i + t) ω - X.X (grid i) ω)) = K i := funext (hRep i)
    simpa only [hrep] using hi
  have hcount : ∀ i ω,
      (NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal =
        (K i ω : ℝ) := by
    intro i ω
    rw [← hKsource i ω]
    simp
  have hi := avram_wave4_p1_finite_grid_poisson_l2_isometry_natural
    P H K r hHm hHSq hKm hKlaw hKInt hJoint n
  simpa only [hcount] using hi
