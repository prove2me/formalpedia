-- Prove2me | solution 1 for ConnesGreen.canonical_actual_zero_support_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:40:59.862988+00:00
-- url     : https://prove2.me/submissions/d087a23a-2613-4024-b7b7-73a0ea30c3fe

import Theorems.Thm_ConnesGreen_canonicalPicardMarker_window_antitone
import Theorems.Thm_WeilDefect_MarkerStability_exists_compact_antitone_right_limit
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace ConnesGreen
private theorem positiveWindowPicardMarker_antitone (S : Finset CriticalZeros) :
    AntitoneOn (fun t => positiveWindowPicardMarker t S) (Ioi (0 : ℝ)) := by
  intro t ht T hT htT
  change positiveWindowPicardMarker T S ≤ positiveWindowPicardMarker t S
  rw [positiveWindowPicardMarker_eq t ht S, positiveWindowPicardMarker_eq T hT S]
  exact canonicalPicardMarker_window_antitone t T ht hT htT S


end ConnesGreen
theorem solution (c : ℝ) (hc : 0 ≤ c)
    (S : Finset CriticalZeros) :
    ∃ Gplus : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ),
      0 ≤ Gplus ∧ Gplus ≤ 1 ∧
      IsLUB ((fun t => positiveWindowPicardMarker t S) '' Ioi c) Gplus ∧
      Tendsto (fun t => positiveWindowPicardMarker t S)
        (nhdsWithin c (Ioi c)) (nhds Gplus) := by
  letI := canonical_selected_coefficient_finiteDimensional S
  letI : ProperSpace (ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) := FiniteDimensional.proper ℂ _
  have hnorm : ∀ t : ℝ, c < t → ‖positiveWindowPicardMarker t S‖ ≤ 1 := by
    intro t hct
    have ht : 0 < t := lt_of_le_of_lt hc hct
    rw [positiveWindowPicardMarker_eq t ht S]
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (by norm_num : (0 : ℝ) ≤ 1)
      (canonicalPicardMarker_spec t ht S).1).mpr
    simpa using (canonicalPicardMarker_spec t ht S).2.1
  obtain ⟨Gplus, _, hlub, hlim⟩ := exists_compact_antitone_right_limit
    (fun t => positiveWindowPicardMarker t S) c (Metric.closedBall 0 1)
    (isCompact_closedBall _ _) (fun t ht => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm t ht)
    ((positiveWindowPicardMarker_antitone S).mono (Ioi_subset_Ioi hc))
  have hb : ∀ᶠ t in nhdsWithin c (Ioi c),
      0 ≤ positiveWindowPicardMarker t S ∧ positiveWindowPicardMarker t S ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with t hct
    have ht : 0 < t := lt_of_le_of_lt hc hct
    rw [positiveWindowPicardMarker_eq t ht S]
    exact ⟨(canonicalPicardMarker_spec t ht S).1, (canonicalPicardMarker_spec t ht S).2.1⟩
  exact ⟨Gplus, isClosed_Ici.mem_of_tendsto hlim (hb.mono fun _ h => h.1),
    isClosed_Iic.mem_of_tendsto hlim (hb.mono fun _ h => h.2), hlub, hlim⟩
