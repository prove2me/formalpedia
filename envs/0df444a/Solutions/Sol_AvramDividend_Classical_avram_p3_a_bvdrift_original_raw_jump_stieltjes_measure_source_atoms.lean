-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_measure_source_atoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:46:44.003204+00:00
-- url     : https://prove2.me/submissions/f3f38c5b-8d4a-4c95-a594-38b32e9b7de1

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_stieltjes_function
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original jump Stieltjes measure has precisely the true source atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      ∀ t : ℝ≥0, 0 < t →
        μ {t} = ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_jump_stieltjes_function X hBV,
      avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict X hBV,
      avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split X hBV]
    with ω hFexists hleft hsplit
  obtain ⟨F, hFeq⟩ := hFexists
  refine ⟨F.measure, ?_⟩
  intro t ht
  have hF_eq : (F : ℝ≥0 → ℝ) = (fun s : ℝ≥0 =>
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) :=
    funext hFeq
  have hleftF : Function.leftLim (F : ℝ≥0 → ℝ) t =
      (∑' u : ℝ≥0, if 0 < u ∧ u < t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
    rw [hF_eq]
    exact hleft t ht
  rw [F.measure_singleton, hFeq t, hleftF, hsplit t ht]
  congr 1
  ring
