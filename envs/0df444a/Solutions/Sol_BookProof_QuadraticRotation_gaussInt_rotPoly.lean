-- Prove2me | solution 1 for BookProof.QuadraticRotation.gaussInt_rotPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:13:39.717753+00:00
-- url     : https://prove2.me/submissions/d6249679-14ba-4c45-8bd6-c147d164053a

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.gaussInt_rotPoly
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_integral_comp_rotIso
import Theorems.Thm_BookProof_QuadraticRotation_eval_rotPoly
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (r : MvPolynomial (Fin d) ℂ) : gaussInt (rotPoly O r) = gaussInt r := by

  rw [gaussInt, gaussInt]
  have hpt : ∀ x : Vd d,
      MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (rotPoly O r) * (gaussWD x : ℂ)
        = (fun y : Vd d => MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) r * (gaussWD y : ℂ))
            (rotIso hO x) := by
    intro x
    rw [eval_rotPoly hO]
    congr 2
    rw [gaussWD, gaussWD, (rotIso hO).norm_map x]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_comp_rotIso hO
    (fun y : Vd d => MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) r * (gaussWD y : ℂ))
