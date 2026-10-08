-- Prove2me | solution 1 for ConnesGreen.RG0Integration.original_picard_outer_no_strict_half_margin
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:46:21.147085+00:00
-- url     : https://prove2.me/submissions/6eea9a85-46dd-4d1d-a473-9d1689e3456b

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Theorems.Thm_WeilDefect_MarkerStability_no_strict_scalar_lower_bound_of_eventual_failure
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.MarkerStability ContinuousLinearMap Filter Set
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem solution
    (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros)
    (R : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
    (hlim : Tendsto (fun T => positiveWindowPicardMarker T S)
      (nhdsWithin c (Ioi c)) (nhds R))
    (hbad : ∀ T : ℝ, ∀ hT : 0 < T, c < T →
      ¬ (1/2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S)
    (a : ℝ) (ha : (1/2 : ℝ) < a) :
    ¬ a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ R := by
  have hpos : 0 ≤ R := isClosed_Ici.mem_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with T hTc
    have hT : 0 < T := hc.trans hTc
    rw [positiveWindowPicardMarker_eq T hT]
    exact (canonicalPicardMarker_spec T hT S).1)
  apply no_strict_scalar_lower_bound_of_eventual_failure
    (fun T => positiveWindowPicardMarker T S) R (1/2) a hlim
    ((ContinuousLinearMap.nonneg_iff_isPositive R).mp hpos).isSelfAdjoint
  · filter_upwards [self_mem_nhdsWithin] with T hTc
    have hT : 0 < T := hc.trans hTc
    rw [positiveWindowPicardMarker_eq T hT]
    exact canonicalPicardMarker_selfAdjoint T hT S
  · filter_upwards [self_mem_nhdsWithin] with T hTc
    have hT : 0 < T := hc.trans hTc
    rw [positiveWindowPicardMarker_eq T hT]
    exact hbad T hT hTc
  · exact ha
