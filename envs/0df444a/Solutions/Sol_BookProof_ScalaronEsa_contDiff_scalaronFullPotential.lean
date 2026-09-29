-- Prove2me | solution 1 for BookProof.ScalaronEsa.contDiff_scalaronFullPotential
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:45:23.548548+00:00
-- url     : https://prove2.me/submissions/b7862da5-7602-44dd-9206-acc326c37ebc

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.contDiff_scalaronFullPotential
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronAlong
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem solution (M alpha : ℝ) (eRc ephi : E) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scalaronFullPotential M alpha eRc ephi) := by

  unfold scalaronFullPotential confV
  refine ContDiff.add ?_ (contDiff_scalaronAlong M alpha ephi)
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => (inner ℝ x eRc : ℝ)) :=
    ((innerSL ℝ).flip eRc).contDiff
  exact (contDiff_const.mul h).add (contDiff_const.mul (h.pow 2))
