-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail13_single_step_left_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:27:00.078209+00:00
-- url     : https://prove2.me/submissions/670b5d42-a022-4550-b1a9-caa99876f28e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology NNReal ENNReal
noncomputable section

/-- A step with the dividend paid strictly after its clock is left-continuous
at every time in the exact original IsDividendStrategy sense. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (K : Ω → ℝ)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω) :
    ∀ ω t, ContinuousWithinAt (fun u => D u ω) (Iic t) t := by
  intro ω t
  by_cases ht : t ≤ s
  · have hnear : (fun u : ℝ≥0 => D u ω) =ᶠ[𝓝[Iic t] t]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      rw [hD]
      simp [le_trans hu ht]
    have hpoint : D t ω = 0 := by
      rw [hD]
      simp [ht]
    exact continuousWithinAt_const.congr_of_eventuallyEq hnear hpoint
  · have hst : s < t := lt_of_not_ge ht
    have hnear_set : Ioi s ∈ 𝓝[Iic t] t :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hst)
    have hnear : (fun u : ℝ≥0 => D u ω) =ᶠ[𝓝[Iic t] t]
        (fun _ => K ω) := by
      filter_upwards [hnear_set] with u hu
      change s < u at hu
      rw [hD]
      simp [not_le.mpr hu]
    have hpoint : D t ω = K ω := by
      rw [hD]
      simp [not_le.mpr hst]
    exact continuousWithinAt_const.congr_of_eventuallyEq hnear hpoint
