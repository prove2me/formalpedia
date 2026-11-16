-- Prove2me | solution 1 for AvramDividend.Classical.avram_b28_original_intrinsic_gaussian_unique_physical_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:44:50.12198+00:00
-- url     : https://prove2.me/submissions/980799cd-a70f-423e-a589-9cd06feb902e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R B : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hBsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (B t ω)))
    (σ : Ω → ℝ≥0) (S : Finset ℕ)
    (a b : ℕ → ℝ≥0) (WG : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) =
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
        (B (b i) ω - B (a i) ω)) := by
  filter_upwards [hRsource, hBsource] with ω hR hB
  have hEq : ∀ t : ℝ≥0, R t ω = B t ω := by
    intro t
    exact tendsto_nhds_unique (hR t) (hB t)
  apply Finset.sum_congr rfl
  intro i hi
  rw [hEq (b i), hEq (a i)]
