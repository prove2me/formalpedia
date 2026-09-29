-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.intertwined_mom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:40:35.565497+00:00
-- url     : https://prove2.me/submissions/6cfbbf60-ccca-4ca8-a8e1-919fb486dd58

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.intertwined_mom
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_sub
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_smul
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_ann
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_cre
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_momOp_eq_ladder
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_sqrtTwo_ne_zero
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_sqrtTwo_mul_self
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
    Intertwined (mom i) (((Real.sqrt 2 : ℝ) : ℂ) • momOp i) := by

  have hs : ((Real.sqrt 2 : ℝ) : ℂ) • momOp i
      = (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)) • (creOp i - annOp i) := by
    rw [momOp_eq_ladder, smul_smul]
    congr 1
    have hne := sqrtTwo_ne_zero
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq]; exact sqrtTwo_mul_self
    push_cast
    field_simp
    linear_combination hsq
  rw [hs]
  exact ((intertwined_cre i).sub (intertwined_ann i)).smul _
