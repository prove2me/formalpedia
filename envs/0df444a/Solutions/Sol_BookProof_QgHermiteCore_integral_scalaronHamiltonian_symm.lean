-- Prove2me | solution 1 for BookProof.QgHermiteCore.integral_scalaronHamiltonian_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:37:54.897583+00:00
-- url     : https://prove2.me/submissions/9d7b7d39-4910-4d5d-9bd7-8e5c8991f8ba

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.integral_scalaronHamiltonian_symm
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_continuous_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_integral_hamiltonian_symm
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x
        * (-deriv (deriv (gaussPoly q)) x + starobinskyV M alpha x * gaussPoly q x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x + starobinskyV M alpha x * gaussPoly p x)
        * gaussPoly q x :=
  integral_hamiltonian_symm (continuous_starobinskyV M alpha)
      (expBounded_starobinskyV M alpha hM) p q
