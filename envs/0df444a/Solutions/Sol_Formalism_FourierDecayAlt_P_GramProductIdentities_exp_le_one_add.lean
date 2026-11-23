-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.exp_le_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:06.641889+00:00
-- url     : https://prove2.me/submissions/1c922855-914d-4f1b-af99-a4b7916ff9da

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.exp (-2 * |x|) ≤ 1 + x := by
  rcases le_or_gt 0 x with h0 | h0
  · have : Real.exp (-2 * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])
    linarith
  · have hu : |x| = -x := abs_of_neg h0
    set u := -x with hu'
    have hu0 : 0 ≤ u := by linarith
    have hu1 : u ≤ 1 / 2 := by rw [← hu]; exact hx
    have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
    have h2 : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (-2 * u) * (1 + 2 * u) ≤ 1 := by
      calc Real.exp (-2 * u) * (1 + 2 * u) ≤ Real.exp (-2 * u) * Real.exp (2 * u) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
    rw [hu]
    have he := Real.exp_pos (-2 * u)
    nlinarith [mul_nonneg hu0 (by linarith : (0:ℝ) ≤ 1 - 2 * u)]
end Formalism.FourierDecayAlt.P.GramProductIdentities
