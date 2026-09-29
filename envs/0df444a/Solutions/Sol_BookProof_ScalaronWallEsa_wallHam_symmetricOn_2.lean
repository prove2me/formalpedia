-- Prove2me | solution 2 for BookProof.ScalaronWallEsa.wallHam_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-20T11:03:07.461496+00:00
-- url     : https://prove2.me/submissions/d95f3016-01af-4eee-b130-cade9aa5f345

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
