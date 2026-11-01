-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_all_borel_band_count_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:00:07.773693+00:00
-- url     : https://prove2.me/submissions/20d1de02-5324-4e3b-b3a1-46d0378709a4

import Mathlib.Data.Set.Card
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual original-X intrinsic jump measure is finite on every Borel
mark rectangle under BV and finite negative Lévy intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) < ⊤ := by
  filter_upwards
    [avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
      X hBV hFinite T hT] with ω hfinite
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    X ω 0 T B hB]
  let A : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  have hsub :
      A ⊆ {u : ℝ≥0 | u ≤ T ∧ 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by
    intro u hu
    rcases hu with ⟨huPos, _, huT, huMark, _⟩
    exact ⟨huT, huPos, huMark⟩
  have hAfin : A.Finite := hfinite.subset hsub
  change ((A.encard : ℝ≥0∞) < ⊤)
  obtain ⟨n, hn⟩ := hAfin.exists_encard_eq_coe
  rw [hn]
  simp
