-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.sign_alternates_add_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:50:20.679714+00:00
-- url     : https://prove2.me/submissions/d7d391f7-6a73-4584-b329-4e1cefbada30

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarInverseSimplification

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (s : ℕ) : sgnW (s + 2) = - sgnW s := by
  unfold sgnW
  have e : (s + 2) * (s + 2 - 1) / 2 = s * (s - 1) / 2 + (2 * s + 1) := by
    have e2 : (s + 2) * (s + 2 - 1) = s * (s - 1) + 2 * (2 * s + 1) := by
      rw [show s + 2 - 1 = s + 1 by omega]
      cases s with
      | zero => rfl
      | succ k =>
        rw [show k + 1 - 1 = k by omega]
        ring
    rw [e2, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  rw [e, pow_add, pow_succ, pow_mul]
  norm_num
end Formalism.FourierDecayAlt.P.SignAntidiagonal
