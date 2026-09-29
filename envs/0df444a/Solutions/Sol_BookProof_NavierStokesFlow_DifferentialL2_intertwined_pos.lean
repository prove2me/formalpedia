-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.intertwined_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:40:36.462499+00:00
-- url     : https://prove2.me/submissions/cb330727-8d46-4c1f-a398-529aaf44bb9d

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.intertwined_pos
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_add
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_smul
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_ann
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_cre
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_posOp_eq_ladder
open BookProof.NavierStokesFlow.DifferentialL2




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
-- The transport arguments unfold operators on a submodule of `L²(ℝ³)` through several
-- linear equivalences, so the default heartbeat budget is not enough.
theorem solution (i : Fin 3) :
    Intertwined (pos i) (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp i) := by

  rw [posOp_eq_ladder, add_comm (annOp i) (creOp i)]
  exact ((intertwined_cre i).add (intertwined_ann i)).smul _
