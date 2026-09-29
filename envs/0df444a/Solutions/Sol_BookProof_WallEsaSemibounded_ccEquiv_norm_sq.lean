-- Prove2me | solution 1 for BookProof.WallEsaSemibounded.ccEquiv_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:12:18.401884+00:00
-- url     : https://prove2.me/submissions/e334062e-6009-4af3-9d49-c666307721f5

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStrichartzWave
-- Generated from ChapterWallEsaSemibounded.lean — solution of BookProof.WallEsaSemibounded.ccEquiv_norm_sq
import Mathlib
import Definitions.Def_ChapterWallEsaSemibounded
import Theorems.Thm_BookProof_WallEsaSemibounded_inner_toLp_self
import Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe
open BookProof.WallEsaSemibounded











open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (f : ccSchwartz ℝ) :
    ‖((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2
      = ∫ x, ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by

  have h := inner_toLp_self (f : 𝓢(ℝ, ℂ))
  rw [← ccEquiv_coe] at h
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)
    ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ)), h]
  simp
