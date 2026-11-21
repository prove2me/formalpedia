-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_finitecap_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:41:28.532504+00:00
-- url     : https://prove2.me/submissions/6287f132-074a-469b-ab34-45f251e68eab

import Mathlib
open Set

theorem solution
    (w : ℝ → ℝ) (b ε : ℝ) (hb : 0 ≤ b) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y z : ℝ,
      0 ≤ y → y ≤ b → 0 ≤ z → z ≤ b →
      |y - z| < δ → |w y - w z| < ε  := by
  have hcont : ContinuousOn w (Icc 0 b) :=
    hw_cont.mono (fun z hz => hz.1)
  have huc : UniformContinuousOn w (Icc 0 b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp huc) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y z hy0 hyb hz0 hzb hdist
  have hY : y ∈ Icc 0 b := ⟨hy0, hyb⟩
  have hZ : z ∈ Icc 0 b := ⟨hz0, hzb⟩
  simpa only [Real.dist_eq] using
    hmod y hY z hZ (by simpa only [Real.dist_eq] using hdist)
