-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.hasCompactSupport_slice_re
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:54.702356+00:00
-- url     : https://prove2.me/submissions/9293d7a8-7be4-438f-9932-8b071684d072

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.hasCompactSupport_slice_re
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (y : ℝ) :
    HasCompactSupport (fun t : ℝ => ψ ((t : ℂ) + y * Complex.I)) := by

  obtain ⟨M, hM⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -M) (b := M)) ?_
  intro t ht
  have hmem : (t : ℂ) + y * Complex.I ∈ tsupport ψ := subset_tsupport ψ ht
  have := hM hmem
  simp only [mem_closedBall, dist_zero_right] at this
  have hrele : |t| ≤ ‖(t : ℂ) + y * Complex.I‖ := by
    have hre : ((t : ℂ) + y * Complex.I).re = t := by simp
    calc |t| = |((t : ℂ) + y * Complex.I).re| := by rw [hre]
      _ ≤ ‖(t : ℂ) + y * Complex.I‖ := Complex.abs_re_le_norm _
  rw [mem_Icc]
  constructor <;> [linarith [abs_le.1 (le_trans hrele this) |>.1];
    linarith [abs_le.1 (le_trans hrele this) |>.2]]
