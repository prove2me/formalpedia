-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_original_finite_unit_mean_exact_real_horizon_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:36:12.226895+00:00
-- url     : https://prove2.me/submissions/df7d05ce-b6ce-44c7-a958-8eda9523d167

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_finite_unit_mean_all_real_horizons_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_nnreal_rational_grid_enclosure
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_rational_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_ennreal_finite_mesh_squeeze

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact original source marked mean is linear at every nonnegative real
horizon when the unit-time marked source mean is finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (hunit : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) < ⊤) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) =
      (t : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
  let M : ℝ≥0 → ℝ≥0∞ := fun q => (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 q ×ˢ B) ∂P)
  change M t = (t : ℝ≥0∞) * M 1
  have hunit' : M 1 < ⊤ := hunit
  have htfinite : M t < ⊤ :=
    avram_p2_d_future_finite_unit_mean_all_real_horizons_finite X B hB t hunit
  apply avram_p2_d_future_ennreal_finite_mesh_squeeze (M 1) (M t)
    t hunit'.ne htfinite.ne
  intro d hd
  obtain ⟨n, hlo, hhi⟩ :=
    avram_p2_d_future_nnreal_rational_grid_enclosure t d hd
  have hd0 : (d : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hrelLo : (d : ℝ≥0) * ((n : ℝ≥0) / (d : ℝ≥0)) =
      (n : ℝ≥0) := by
    field_simp [hd0]
  have hrelHi : (d : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) =
      ((n + 1 : ℕ) : ℝ≥0) := by
    field_simp [hd0]
  have hMean :=
    avram_p2_d_future_zero_origin_expected_count_rational_sandwich
      X B hB ((n : ℝ≥0) / (d : ℝ≥0)) t
      (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0))
      n (n + 1) d hd hrelLo hrelHi hlo hhi
  exact ⟨n, hlo, hhi, hMean.1, hMean.2⟩
