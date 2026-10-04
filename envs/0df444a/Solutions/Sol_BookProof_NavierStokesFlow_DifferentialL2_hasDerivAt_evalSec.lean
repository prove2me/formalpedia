-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_evalSec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:25:47.755766+00:00
-- url     : https://prove2.me/submissions/82a30b32-9679-4743-ae1c-1b01e150e077

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_evalSec
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_sec_apply
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_hasDerivAt_eval_update
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
theorem solution (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (pderiv i p)) (x i) := by

  classical
  have hupd : ∀ t : ℝ, (fun j => (((sec i x t) j : ℝ) : ℂ))
      = Function.update (fun j => ((x j : ℝ) : ℂ)) i ((t : ℝ) : ℂ) := by
    intro t
    funext j
    rw [sec_apply, Function.update_apply]
    by_cases hj : j = i <;> simp [hj]
  have hbase := hasDerivAt_eval_update i p (fun j => ((x j : ℝ) : ℂ)) (((x i : ℝ)) : ℂ)
  have h := hbase.comp_ofReal (z := x i)
  have heq : (fun y : ℝ => MvPolynomial.eval
        (Function.update (fun j => ((x j : ℝ) : ℂ)) i ((y : ℝ) : ℂ)) p)
      = fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p := by
    funext t; rw [hupd t]
  rw [heq] at h
  have hfun : Function.update (fun j => ((x j : ℝ) : ℂ)) i (((x i : ℝ)) : ℂ)
      = fun j => ((x j : ℝ) : ℂ) := by
    funext j
    rw [Function.update_apply]
    by_cases hj : j = i <;> simp [hj]
  rwa [hfun] at h
