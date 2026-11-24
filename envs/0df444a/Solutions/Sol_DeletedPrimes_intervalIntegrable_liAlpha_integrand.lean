-- Prove2me | solution 1 for DeletedPrimes.intervalIntegrable_liAlpha_integrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:12:25.771953+00:00
-- url     : https://prove2.me/submissions/5f88c077-f431-4c70-ab09-ce804110bb45

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (α : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ (α - 1) / Real.log u) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hpos : ∀ u ∈ Set.uIcc a b, 2 ≤ u := by
    intro u hu
    rcases Set.mem_uIcc.mp hu with h | h <;> linarith [h.1]
  apply ContinuousOn.div
  · exact continuousOn_id.rpow_const (fun u hu => Or.inl (by simp only [id]; linarith [hpos u hu]))
  · exact continuousOn_id.log (fun u hu => by simp only [id]; linarith [hpos u hu])
  · intro u hu; exact (Real.log_pos (by linarith [hpos u hu])).ne'
end DeletedPrimes
