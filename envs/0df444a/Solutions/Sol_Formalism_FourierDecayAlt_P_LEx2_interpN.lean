-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.interpN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:14.250359+00:00
-- url     : https://prove2.me/submissions/1a99ccf1-cbfd-43ab-8844-b94f605e9d0e

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_interp1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open MvPolynomial
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (N n : ℕ) (grid : Fin N → Finset ℝ) (hg : ∀ a, (grid a).card = n + 1)
    (Q : MvPolynomial (Fin N) ℝ) (hQ : ∀ a, Q.degreeOf a ≤ n) (Y : Fin N → ℝ) :
    eval Y Q = ∑ g ∈ Fintype.piFinset grid,
      (∏ a, (Lagrange.basis (grid a) id (g a)).eval (Y a)) * eval g Q := by
  simp_rw [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : ∀ a, m a ≤ n := fun a => (MvPolynomial.degreeOf_le_iff.1 (hQ a)) m hm
  have h1 : ∏ a, Y a ^ m a = ∑ g ∈ Fintype.piFinset grid,
      ∏ a, ((Lagrange.basis (grid a) id (g a)).eval (Y a) * g a ^ m a) := by
    rw [← Finset.prod_univ_sum (t := grid)
      (f := fun a x => (Lagrange.basis (grid a) id x).eval (Y a) * x ^ m a)]
    apply Finset.prod_congr rfl
    intro a _
    exact interp1 (grid a) n (m a) (hg a) (hmn a) (Y a)
  rw [h1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.prod_mul_distrib]; ring
end Formalism.FourierDecayAlt.P.LEx2
