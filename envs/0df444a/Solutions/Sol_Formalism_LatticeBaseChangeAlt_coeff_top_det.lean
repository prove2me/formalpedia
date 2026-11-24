-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.coeff_top_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:22.944846+00:00
-- url     : https://prove2.me/submissions/22aa3b92-bf97-4c63-99f0-ffa3b9db0cb6

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_DetMulEqSumPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset Matrix Polynomial
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution {K : Type*} [CommRing K] {i : ℕ} (M : Matrix (Fin i) (Fin i) K) :
    (det (1 + (X : K[X]) • M.map C)).coeff i = M.det := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  · have e : (1 + (X : K[X]) • M.map C) = 1 - (X : K[X]) • (-M).map C := by
      have hm : (-M).map C = -(M.map C) := by
        ext a b
        simp
      rw [hm, smul_neg, sub_neg_eq_add]
    rw [e]
    change (Matrix.charpolyRev (-M)).coeff i = M.det
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, Polynomial.revAt_le (le_refl i), Nat.sub_self]
    have h := Matrix.det_eq_sign_charpoly_coeff (-M)
    rw [Fintype.card_fin, Matrix.det_neg, Fintype.card_fin] at h
    have hu : IsUnit ((-1 : K) ^ i) := (isUnit_one.neg).pow i
    exact (hu.mul_left_cancel h).symm
end Formalism.LatticeBaseChangeAlt
