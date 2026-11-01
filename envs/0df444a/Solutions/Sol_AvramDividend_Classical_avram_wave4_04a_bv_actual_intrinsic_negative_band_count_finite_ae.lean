-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_band_count_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:41:52.769544+00:00
-- url     : https://prove2.me/submissions/91573a28-5d61-4caa-87b9-886a4bab38da

import Mathlib.Data.Set.Card
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_truncated_negative_jump_times_finite_ae
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) < ⊤ := by
  filter_upwards
    [avram_wave4_04a_bv_actual_truncated_negative_jump_times_finite_ae
      X hBV T ε hε] with ω hfinite
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    X ω 0 T (Iic (-ε)) measurableSet_Iic]
  let A : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Iic (-ε)}
  have hsub :
      A ⊆ {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        ε ≤ Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω} := by
    intro u hu
    rcases hu with ⟨huPos, _, huT, _, huBand⟩
    change X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -ε at huBand
    exact ⟨huPos, huT, by linarith⟩
  have hAfin : A.Finite := hfinite.subset hsub
  change ((A.encard : ℝ≥0∞) < ⊤)
  obtain ⟨n, hn⟩ := hAfin.exists_encard_eq_coe
  rw [hn]
  simp
