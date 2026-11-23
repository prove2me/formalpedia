-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.second_polynomial_first_clause
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:37.228813+00:00
-- url     : https://prove2.me/submissions/150ba1a1-36cf-4fc2-955b-f444cb6ce4e9

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_cs_of_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution : PairingGramBound := by
  intro V _ _ R x wt bw hR hbw hwt t t'
  have hcs := cs_of_psd R hR (x t) (x t')
  have hk : 0 ≤ wt t * wt t' / bw := div_nonneg (mul_nonneg (hwt t) (hwt t')) hbw.le
  have e1 : ‖Npair R x wt bw t t'‖ = wt t * wt t' / bw * ‖R (x t) (x t')‖ := by
    rw [Npair, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]
  have e2 : (Npair R x wt bw t t).re * (Npair R x wt bw t' t').re =
      (wt t * wt t' / bw) ^ 2 * ((R (x t) (x t)).re * (R (x t') (x t')).re) := by
    simp only [Npair, Complex.re_ofReal_mul]; ring
  rw [e1, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]
  exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (Real.abs_le_sqrt hcs)) hk
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses
