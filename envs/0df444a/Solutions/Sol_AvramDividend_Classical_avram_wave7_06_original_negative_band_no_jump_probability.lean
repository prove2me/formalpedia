-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_no_jump_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:22:27.129223+00:00
-- url     : https://prove2.me/submissions/8114173c-3c7b-43e3-96e6-fe5a20b4644e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_threshold_iff_leftLim
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_endpoint_void_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_iff_intrinsic_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_zero_count_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-faithful reduction to the intrinsic marked Poisson zero-count law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) :
    P {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < T ∧
      ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + (1 / ((n : ℝ) + 1)) ≤ l} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by
  classical
  let E : Set Ω := {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < T ∧
    ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
      (nhdsWithin t (Iio t)) (nhds l) ∧
      X.X t ω + (1 / ((n : ℝ) + 1)) ≤ l}
  let F : Set Ω := {ω : Ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
  have hAE : E =ᵐ[P] F := by
    filter_upwards
      [avram_wave7_06_original_negative_band_endpoint_void_ae X T n]
      with ω hEnd
    apply propext
    change (¬ ∃ t : ℝ≥0, 0 < t ∧ t < T ∧
      ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + (1 / ((n : ℝ) + 1)) ≤ l) ↔
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0
    have hOpen :
        (¬ ∃ t : ℝ≥0, 0 < t ∧ t < T ∧
          ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧
            X.X t ω + 1 / ((n : ℝ) + 1) ≤ l) ↔
        (∀ u : ℝ≥0, 0 < u → u < T →
          ¬ (X.X u ω + 1 / ((n : ℝ) + 1) ≤
            Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)) := by
      constructor
      · intro h u hu0 huT hmark
        apply h
        exact ⟨u, hu0, huT,
          (avram_wave7_06_original_jump_threshold_iff_leftLim
            X ω u hu0 n).2 hmark⟩
      · intro h ⟨u, hu0, huT, hlim⟩
        exact (h u hu0 huT)
          ((avram_wave7_06_original_jump_threshold_iff_leftLim
            X ω u hu0 n).1 hlim)
    exact hOpen.trans
      (hEnd.trans
        (avram_wave7_06_original_negative_band_void_iff_intrinsic_zero
          X ω T n))
  change P E = _
  calc
    P E = P F := measure_congr hAE
    _ = ENNReal.ofReal (Real.exp
        (-((T : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) :=
      avram_wave7_06_original_intrinsic_negative_band_zero_count_law X T n
