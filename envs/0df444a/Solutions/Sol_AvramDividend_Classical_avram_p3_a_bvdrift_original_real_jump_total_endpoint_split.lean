-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_real_jump_total_endpoint_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:36:02.368015+00:00
-- url     : https://prove2.me/submissions/4b798f54-cc2a-4424-8cc4-c5ecab955bfa

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_endpoint_left_jump_tsum_split
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The real BV source negative-jump total up to t equals the actual
real left jump at t plus the total over the strict past (0,t). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), 0 < t →
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal =
      (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) +
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u < t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top X hBV]
    with ω hω
  intro t ht
  let J (u : ℝ≥0) : ℝ≥0∞ :=
    ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
  let Mle : ℝ≥0∞ := ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then J u else 0
  let Mlt : ℝ≥0∞ := ∑' u : ℝ≥0, if 0 < u ∧ u < t then J u else 0
  have hfin : Mle ≠ ⊤ := by
    exact ne_of_lt (hω 0 t (show (0 : ℝ≥0) ≤ t from zero_le))
  have hsub : Mlt ≤ Mle := by
    apply ENNReal.tsum_le_tsum
    intro u
    by_cases hu : 0 < u ∧ u < t
    · have hule : 0 < u ∧ u ≤ t := ⟨hu.1, le_of_lt hu.2⟩
      simp [hu, hule]
    · simp [hu]
  have hlt : Mlt ≠ ⊤ := ne_top_of_le_ne_top hfin hsub
  have hpoint : J t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : Mle = J t + Mlt := by
    exact avram_p3_a_bvdrift_original_endpoint_left_jump_tsum_split
      X ω t ht
  have hraw : (J t).toReal =
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω := by
    exact (avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
      X ω t ht).2
  change Mle.toReal =
    (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) + Mlt.toReal
  calc
    Mle.toReal = (J t + Mlt).toReal := congrArg ENNReal.toReal hsplit
    _ = (J t).toReal + Mlt.toReal := ENNReal.toReal_add hpoint hlt
    _ = _ := by rw [hraw]
