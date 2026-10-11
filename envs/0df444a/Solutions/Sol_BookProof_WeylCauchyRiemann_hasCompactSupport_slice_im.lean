-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.hasCompactSupport_slice_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:53.774403+00:00
-- url     : https://prove2.me/submissions/4f16ba71-9893-4b7c-abc1-cba3eb64ed85

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.hasCompactSupport_slice_im
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (x : ℝ) :
    HasCompactSupport (fun t : ℝ => ψ ((x : ℂ) + t * Complex.I)) := by

  obtain ⟨M, hM⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -M) (b := M)) ?_
  intro t ht
  have hmem : (x : ℂ) + t * Complex.I ∈ tsupport ψ := subset_tsupport ψ ht
  have := hM hmem
  simp only [mem_closedBall, dist_zero_right] at this
  have himle : |t| ≤ ‖(x : ℂ) + t * Complex.I‖ := by
    have : ((x : ℂ) + t * Complex.I).im = t := by simp
    calc |t| = |((x : ℂ) + t * Complex.I).im| := by rw [this]
      _ ≤ ‖(x : ℂ) + t * Complex.I‖ := Complex.abs_im_le_norm _
  rw [mem_Icc]
  constructor <;> [linarith [abs_le.1 (le_trans himle this) |>.1];
    linarith [abs_le.1 (le_trans himle this) |>.2]]
