-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TopDegreePolynomials.evR_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:32.236519+00:00
-- url     : https://prove2.me/submissions/d478e0b2-5130-407e-87fa-7bd81f09c583

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TopDegreePolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.TopDegreePolynomials
theorem _root_.solution (P : R[X]) (a : ℕ) (ha : P.natDegree ≤ a) (Y : ℝ) (X : M) :
    evR P Y • X = ∑ i ∈ range (a + 1), ((Y : ℂ) ^ i) • (P.coeff i • X) := by
  unfold evR
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le ha), Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow, ← Algebra.commutes, mul_smul, algebraMap_smul]
end Formalism.FourierDecayAlt.P.TopDegreePolynomials
