-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_adapted_finite_grid_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:11:43.844884+00:00
-- url     : https://prove2.me/submissions/0a7d07b0-ba34-4a6b-8a50-7966973523ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_prefix_predictable_of_adapted_finite_cells
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_source_levy_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Original finite-band grid isometry from adapted source cell counts. -/
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
    (grid : ℕ → ℝ≥0) (hGrid : Monotone grid)
    (C : ℕ → Set ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hBand : ∀ i, C i ⊆ Set.Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (C i) < ⊤)
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) = K i ω)
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hRate : ∀ i, (r i : ℝ) =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (C i)).toReal)
    (hH : ∀ i, Measurable[𝓕 (grid i)] (H i))
    (hKpast : ∀ i, Measurable[𝓕 (grid (i + 1))]
      (fun ω => (K i ω : ℝ)))
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable
      (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω *
        ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
          (r i : ℝ))) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
        (r i : ℝ))) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n,
        ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) * ∫ ω, (H i ω) ^ 2 ∂P := by
  have hFilt : ∀ {i j : ℕ}, i ≤ j →
      𝓕 (grid i) ≤ 𝓕 (grid j) := by
    intro i j hij
    exact 𝓕.mono (hGrid hij)
  have hPrefix : ∀ i, Measurable[𝓕 (grid i)] (fun ω =>
      ∑ j ∈ Finset.range i, H j ω *
        ((K j ω : ℝ) - (r j : ℝ))) := by
    intro i
    exact avram_p4_g_isometry_prefix_predictable_of_adapted_finite_cells
      grid H K r hFilt hH hKpast i
  exact avram_p4_g_isometry_original_finite_grid_source_levy_rate
    X NX hNX grid C ε hε hBand hν H K r Fpath hFpath hRep
    hKsource hRate hH hHm hHSq hKm hKlaw hKInt hPrefix n
