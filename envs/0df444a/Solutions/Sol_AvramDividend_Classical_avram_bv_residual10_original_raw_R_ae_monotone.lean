-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_raw_R_ae_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:30:48.963883+00:00
-- url     : https://prove2.me/submissions/9bc700df-0350-4607-bd93-56752e1e3ee0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_drift_deficit_stieltjes_intrinsic_negative_mark_plus_residual_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original real-valued negative-jump remainder is almost surely monotone.
This transfers the proved Stieltjes remainder through the exact real-tsum
identity, without changing the Lévy process or replacing it in law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) := by
  filter_upwards
    [avram_wave5_04a_actual_BV_drift_deficit_stieltjes_intrinsic_negative_mark_plus_residual_split
      X hBV,
      avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hsplit hreal
  obtain ⟨F, R, _, hR, hRmono, _, _⟩ := hsplit
  have hJ (t : ℝ≥0) :
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0).toReal =
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) :=
    (hreal 0 t (show (0 : ℝ≥0) ≤ t from zero_le)).2
  have hEq (t : ℝ≥0) :
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = R t := by
    rw [hR t, hJ t]
  intro s t hst
  calc
    ((s : ℝ) * X.drift - X.X s ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = R s := hEq s
    _ ≤ R t := hRmono hst
    _ = ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) := (hEq t).symm
