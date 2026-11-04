-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_cutoff_sup_eq_total_of_coverage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:45:29.408922+00:00
-- url     : https://prove2.me/submissions/158f8cdb-5672-46ff-bb50-31afe32f8ee9

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Actual original negative-jump cutoff totals increase to their full source
jump mass if thresholds decrease and eventually include each positive jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (ε : ℕ → ℝ≥0∞) (hε : Antitone ε)
    (hCover : ∀ v : ℝ≥0, 0 < v → v ≤ T →
      0 < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) →
      ∃ n : ℕ, ε n < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)) :
    let M : ℝ≥0 → ℝ≥0∞ := fun v : ℝ≥0 => if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0
    (⨆ n : ℕ, ∑' v : ℝ≥0, if ε n < M v then M v else 0) =
      ∑' v : ℝ≥0, M v := by
  refine avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core
    (fun v : ℝ≥0 => if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) ε hε ?_
  intro v hv
  by_cases ht : 0 < v ∧ v ≤ T
  · have hmag : 0 < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) := by
      simpa [ht] using hv
    obtain ⟨n, hn⟩ := hCover v ht.1 ht.2 hmag
    exact ⟨n, by simpa [ht] using hn⟩
  · simp [ht] at hv