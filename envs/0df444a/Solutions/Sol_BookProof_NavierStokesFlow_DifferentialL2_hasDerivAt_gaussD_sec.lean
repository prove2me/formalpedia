-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_gaussD_sec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:41:51.368654+00:00
-- url     : https://prove2.me/submissions/ab40a0a6-afe6-4a78-84e6-21b67c665f97

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_gaussD_sec
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_norm_sq_sec
open BookProof.NavierStokesFlow.DifferentialL2




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (sec i x s)) (-(t / 2) * gaussD (sec i x t)) t := by

  classical
  set S := ∑ j ∈ Finset.univ.erase i, (x j) ^ 2 with hS
  have hfun : (fun s : ℝ => gaussD (sec i x s)) = fun s : ℝ => Real.exp (-(S + s ^ 2) / 4) := by
    funext s
    rw [gaussD, norm_sq_sec]
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => -(S + s ^ 2) / 4) (-(2 * t) / 4) t := by
    have h : HasDerivAt (fun s : ℝ => -(S + s ^ 2) / 4) (-(0 + 2 * t) / 4) t := by
      have h0 : HasDerivAt (fun s : ℝ => S + s ^ 2) (0 + 2 * t) t := by
        simpa using ((hasDerivAt_pow 2 t).const_add S)
      exact h0.neg.div_const 4
    simpa using h
  have h2 := (Real.hasDerivAt_exp (-(S + t ^ 2) / 4)).comp t h1
  refine HasDerivAt.congr_deriv h2 ?_
  rw [gaussD, norm_sq_sec, hS]
  ring
