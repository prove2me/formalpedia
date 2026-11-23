-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.interp1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:52.228438+00:00
-- url     : https://prove2.me/submissions/3680303f-b74d-4227-a99d-7d2277d084b2

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
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (s : Finset ℝ) (n k : ℕ) (hs : s.card = n + 1) (hk : k ≤ n) (y : ℝ) :
    y ^ k = ∑ x ∈ s, (Lagrange.basis s id x).eval y * x ^ k := by
  have h := Lagrange.eq_interpolate (s := s) (v := id) (f := (Polynomial.X : Polynomial ℝ) ^ k)
    (Function.injective_id.injOn) (by
      rw [Polynomial.degree_X_pow, hs]; exact_mod_cast Nat.lt_succ_of_le hk)
  have h2 := congrArg (Polynomial.eval y) h
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, id] at h2
  rw [h2]; apply Finset.sum_congr rfl; intros; ring
end Formalism.FourierDecayAlt.P.LEx2
