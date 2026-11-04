-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_preterminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:36:23.518001+00:00
-- url     : https://prove2.me/submissions/823e25c0-c21b-4490-b2c2-adbd0d6ac6d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_preruin_preterminal_drift_strip
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_preterminal_integrable_of_strip
import Theorems.Thm_AvramDividend_Classical_riskProcess_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hfinite : IsFiniteMeasure P)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (S : ℝ≥0) :
    Integrable (fun ω => if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) P := by
  classical
  letI : IsFiniteMeasure P := hfinite
  let A : Set Ω := {ω | (S : ℝ≥0∞) < ruinTime X x D ω}
  let B : ℝ := max 0 (x + (S : ℝ) * X.drift)
  have hB : 0 ≤ B := le_max_left _ _
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (ruinTime_measurable X x D hD)
  have hZ : Measurable (fun ω => riskProcess X x D S ω) :=
    riskProcess_measurable X x D hD S
  have hwMeas : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hstrip : ∀ᵐ ω ∂P, ω ∈ A →
      0 ≤ riskProcess X x D S ω ∧ riskProcess X x D S ω ≤ B := by
    filter_upwards [avram_p3_bv_preruin_preterminal_drift_strip
      X hBV hXzero x D hD S] with ω hω
    intro hsurvive
    exact ⟨(hω hsurvive).1, (hω hsurvive).2.trans (le_max_right _ _)⟩
  simpa only [A, Set.mem_setOf_eq] using
    (avram_p3_bv_preterminal_integrable_of_strip
      P w hw_cont hwMeas (fun ω => riskProcess X x D S ω) hZ
      A hA B hB hstrip q (S : ℝ))
