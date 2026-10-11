-- Prove2me | solution 1 for BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:05:52.534316+00:00
-- url     : https://prove2.me/submissions/433ab356-a05c-4d83-a072-8b6f30646196

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_ScalaronDensitized_densConfV_apply
import Theorems.Thm_BookProof_QuantumGravityHalfDensity_halfDensityUnitary_symm_apply
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterStarobinskyPotential
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
theorem solution (h : densConfCore M alpha) :
    ∃ x : physConfCore M alpha,
      halfDensityUnitary (x : Lp ℂ 2 physMeasure) = (h : Lp ℂ 2 qgSrcMeasure) := by

  obtain ⟨n, hn⟩ := h.2
  have hmem : (halfDensityUnitary.symm (h : Lp ℂ 2 qgSrcMeasure)) ∈ physConfCore M alpha := by
    refine ⟨n, ?_⟩
    have hpull := measurePreserving_qgSqrt.quasiMeasurePreserving.ae hn
    filter_upwards [halfDensityUnitary_symm_apply ((h : Lp ℂ 2 qgSrcMeasure)), hpull,
      ae_restrict_mem measurableSet_Ioi] with e he hpe hepos hbig
    rw [he]
    refine hpe ?_
    rwa [densConfV_apply, Real.sq_sqrt (le_of_lt hepos)]
  exact ⟨⟨_, hmem⟩, halfDensityUnitary.apply_symm_apply _⟩
