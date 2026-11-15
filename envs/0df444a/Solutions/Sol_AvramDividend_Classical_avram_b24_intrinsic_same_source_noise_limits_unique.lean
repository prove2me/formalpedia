-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_intrinsic_same_source_noise_limits_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:53:41.12321+00:00
-- url     : https://prove2.me/submissions/a0c2dcfa-e51a-42e5-a5d8-538259e08511

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R R' J J' : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hR' : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R' u ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (J u ω)))
    (hJ' : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (J' u ω))) :
    (∀ᵐ ω ∂P, ∀ u, R u ω = R' u ω ∧ J u ω = J' u ω) ∧
    (∀ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
       (WG WJ : ℕ → Ω → ℝ) (σ : Ω → ℝ≥0),
      ∀ᵐ ω ∂P,
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)) =
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R' (b i) ω - R' (a i) ω)) ∧
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (J (b i) ω - J (a i) ω)) =
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (J' (b i) ω - J' (a i) ω))) := by
  have hpaths : ∀ᵐ ω ∂P, ∀ u, R u ω = R' u ω ∧ J u ω = J' u ω := by
    filter_upwards [hR, hR', hJ, hJ'] with ω hr hr' hj hj' u
    exact ⟨tendsto_nhds_unique (hr u) (hr' u),
      tendsto_nhds_unique (hj u) (hj' u)⟩
  refine ⟨hpaths, ?_⟩
  intro S a b WG WJ σ
  filter_upwards [hpaths] with ω hω
  constructor
  · apply Finset.sum_congr rfl
    intro i hi
    rw [(hω (b i)).1, (hω (a i)).1]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [(hω (b i)).2, (hω (a i)).2]
