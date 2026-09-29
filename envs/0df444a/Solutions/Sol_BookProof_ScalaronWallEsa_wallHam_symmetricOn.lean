-- Prove2me | solution 1 for BookProof.ScalaronWallEsa.wallHam_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:54.35827+00:00
-- url     : https://prove2.me/submissions/c0569f35-a8c9-441d-be53-def12048eca2

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWeakSecondDerivative
-- Generated from ChapterScalaronWallEsa.lean — solution of BookProof.ScalaronWallEsa.wallHam_symmetricOn
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
import Theorems.Thm_BookProof_ScalaronWallEsa_kinCcR_symmetricOn
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_symmetric
open BookProof.ScalaronWallEsa













open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    SymmetricOn (ccDomain ℝ) (wallHam V hV) := by

  intro x y
  have h1 := kinCcR_symmetricOn x y
  have h2 := smoothPotential_symmetric V hV x y
  simp only [wallHam, LinearMap.add_apply, inner_add_left, inner_add_right]
  linear_combination h1 + h2
