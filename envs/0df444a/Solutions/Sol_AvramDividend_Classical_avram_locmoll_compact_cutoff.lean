-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_compact_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:42:28.691091+00:00
-- url     : https://prove2.me/submissions/6e51e790-5835-44fd-8d9f-8f242ecea961

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false
theorem solution
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 2 w s) (c r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hR : Metric.closedBall c R ⊆ s) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      EqOn F w (Metric.ball c r) := by 
  let b : ContDiffBump c := ⟨r, R, hr, hrR⟩
  let F : ℝ → ℝ := (b : ℝ → ℝ) * w
  refine ⟨F, ?_, b.hasCompactSupport.mul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ s
    · exact b.contDiff.contDiffAt.mul (hw.contDiffAt (hs.mem_nhds hx))
    · have hxb : x ∉ tsupport (b : ℝ → ℝ) := by
        rw [b.tsupport_eq]
        exact fun h => hx (hR h)
      have he : (b : ℝ → ℝ) =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hxb
      have hF : F =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [he] with z hz
        change b z * w z = 0
        simp [show b z = 0 from hz]
      exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (0 : ℝ))).contDiffAt.congr_of_eventuallyEq hF
  · intro z hz
    change b z * w z = w z
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_mul]
