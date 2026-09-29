-- Prove2me | solution 1 for BookProof.HyperbolicQuadratic.minkowski_apply_eq_differential
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:16:15.430928+00:00
-- url     : https://prove2.me/submissions/0a740326-eabd-4311-a355-801eb7012a3c

-- Generated from ChapterHyperbolicQuadraticEsa.lean — solution of BookProof.HyperbolicQuadratic.minkowski_apply_eq_differential
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_apply_eq_differential
open BookProof.HyperbolicQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (p : MvPolynomial (Fin (1 + n)) ℂ)
    (x : Vd (1 + n)) :
    pgFun (quadPoly (minkowskiCoeff n) p) x
      = (-(deriv (fun t : ℝ => deriv (fun s : ℝ => pgFun p (sec 0 x s)) t) (x 0))
          + (((x 0 : ℝ) : ℂ) ^ 2 / 4) * pgFun p x)
        - ∑ k ∈ Finset.univ.erase (0 : Fin (1 + n)),
            (-(deriv (fun t : ℝ => deriv (fun s : ℝ => pgFun p (sec k x s)) t) (x k))
              + (((x k : ℝ) : ℂ) ^ 2 / 4) * pgFun p x) := by

  classical
  have h0 : ((minkowskiCoeff n 0 : ℝ) : ℂ) = 1 := by simp [minkowskiCoeff]
  have hk : ∀ k ∈ Finset.univ.erase (0 : Fin (1 + n)), ((minkowskiCoeff n k : ℝ) : ℂ) = -1 := by
    intro k hk
    simp [minkowskiCoeff, Finset.ne_of_mem_erase hk]
  rw [quadPoly_apply_eq_differential,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (1 + n))), h0, one_mul,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hkm => ?_
  rw [hk k hkm]
  ring
