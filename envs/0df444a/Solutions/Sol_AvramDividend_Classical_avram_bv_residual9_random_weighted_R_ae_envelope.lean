-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_random_weighted_R_ae_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:07:06.584912+00:00
-- url     : https://prove2.me/submissions/a6184529-2511-4f11-98ab-d68606efa648

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_monotone_R_mesh_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Random sample-dependent coefficients obey the original monotone raw-R mesh envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (a : Ω → ℕ → ℝ) (K : ℝ)
    (hK : ∀ ω i, i ∈ Finset.range (n + 1) → |a ω i| ≤ K) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      |∑ i ∈ Finset.range (n + 1),
        a ω i * (R (u n i) - R (u n (i + 1)))| ≤
          K * (R (u n (n + 1)) - R (u n 0)) := by
  have hRmono :=
    AvramDividend.Classical.avram_bv_residual10_original_raw_R_ae_monotone X hBV
  filter_upwards [hRmono] with ω hmono
  exact AvramDividend.Classical.avram_bv_residual10_original_monotone_R_mesh_bound
    X ω u n hu hmono (a ω) K (hK ω)
