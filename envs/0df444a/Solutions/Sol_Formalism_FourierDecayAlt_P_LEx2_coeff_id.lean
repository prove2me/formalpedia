-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.coeff_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:48.657387+00:00
-- url     : https://prove2.me/submissions/b60fbdeb-2424-4d06-b846-ba71b823427d

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul

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
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (s : Finset ℝ) (d k j : ℕ) (hs : s.card = d + 1) (hk : k ≤ d) :
    ∑ x ∈ s, (Lagrange.basis s id x).coeff j * x ^ k = if j = k then 1 else 0 := by
  have h := Lagrange.eq_interpolate (s := s) (v := id) (f := (Polynomial.X : Polynomial ℝ) ^ k)
    (Function.injective_id.injOn) (by
      rw [Polynomial.degree_X_pow, hs]; exact_mod_cast Nat.lt_succ_of_le hk)
  have h2 := congrArg (fun p => Polynomial.coeff p j) h
  simp only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.eval_pow,
    Polynomial.eval_X, id, Polynomial.coeff_X_pow] at h2
  rw [h2]; apply Finset.sum_congr rfl; intros; ring
end Formalism.FourierDecayAlt.P.LEx2
