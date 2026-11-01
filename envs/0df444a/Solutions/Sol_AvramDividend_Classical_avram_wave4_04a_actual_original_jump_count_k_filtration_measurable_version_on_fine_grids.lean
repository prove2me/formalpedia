-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_original_jump_count_k_filtration_measurable_version_on_fine_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:40:47.406312+00:00
-- url     : https://prove2.me/submissions/158ef884-6c1d-4e19-80e7-e10443dc4ed5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_grid_drift_count_horizon_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T)
    (k : ℕ) :
    ∃ E : Set Ω, MeasurableSet[𝓕 T] E ∧
      (∀ᵐ ω ∂P,
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) = (k : ENNReal) ↔
          ω ∈ E) := by
  classical
  let E : ℕ → Set Ω := fun n =>
    {ω : Ω |
      ((Finset.range n).filter (fun i =>
        X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
          X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k}
  have hE (n : ℕ) : MeasurableSet[𝓕 T] (E n) := by
    exact (avram_wave4_04a_actual_original_grid_drift_count_horizon_adapted
      X T n (grid n) (hBound n)) (measurableSet_singleton k)
  have hlim : MeasurableSet[𝓕 T] (Filter.liminf E atTop) := by
    letI : MeasurableSpace Ω := 𝓕 T
    exact MeasurableSet.measurableSet_liminf hE
  refine ⟨Filter.liminf E atTop, hlim, ?_⟩
  simpa only [E] using
    (avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
      X hBV hFinite T hT grid hGrid hMesh k).2
