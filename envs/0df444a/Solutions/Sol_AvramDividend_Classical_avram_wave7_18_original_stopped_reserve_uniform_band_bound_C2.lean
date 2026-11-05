-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_stopped_reserve_uniform_band_bound_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:54:14.975015+00:00
-- url     : https://prove2.me/submissions/24a27fed-83f0-4cf2-beb5-b42ee2c87062

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_clock_preexit_C2_interior
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_right_continuous_grid_detection
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω => (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨ upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤)) ∧
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨ upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) →
      ∀ s : ℝ≥0, s < T →
        (lower ≤ x + X.X s ω - rightLimit D s ω ∧
          x + X.X s ω - rightLimit D s ω ≤ upper) ∧
        (0 < x + X.X s ω - rightLimit D s ω ∧
          ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) < C) ∧
        ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
          (x + X.X s ω - rightLimit D s ω) := by
  have hbase :=
    avram_wave7_18_original_countable_clock_preexit_C2_interior
      X x D hD C w hw r lower upper hlower hcap hgrid
  have hdetect :=
    avram_wave7_18_original_right_continuous_grid_detection
      X x D hD r lower upper hgrid
  refine ⟨hbase.1, ?_⟩
  intro ω T hclock s hs
  have hband :=
    ((avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
      X x D hD r lower upper hdetect ω T).mpr hclock) s hs
  exact ⟨hband, hbase.2 ω T hclock s hs⟩
