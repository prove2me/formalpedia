-- Prove2me | solution 1 for BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:48:07.637216+00:00
-- url     : https://prove2.me/submissions/664efba1-aa3f-40ee-9a19-15f6899339af

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_QuantumGravityHalfDensity_halfDensityUnitary_apply
open BookProof.ScalaronDensitized




open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (x : physConfCore M alpha) :
    halfDensityUnitary (x : Lp ℂ 2 physMeasure) ∈ densConfCore M alpha := by

  obtain ⟨n, hn⟩ := x.2
  refine ⟨n, ?_⟩
  have hpull := measurePreserving_qgSquare.quasiMeasurePreserving.ae hn
  filter_upwards [halfDensityUnitary_apply ((x : Lp ℂ 2 physMeasure)), hpull] with y hy hpx hbig
  rw [hy]
  simp only [qgSquare] at hpx
  exact hpx hbig
