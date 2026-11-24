-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.sgnW_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:10:59.686329+00:00
-- url     : https://prove2.me/submissions/645b1c5e-a944-4ef6-941f-2128245bece8

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignPermutationIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sign_permutation_identity

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
open Formalism.FourierDecayAlt.C3
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (m : ℕ) : sgnW (m + 1) = (-1) ^ m * sgnW m := by
  have h := (sign_permutation_identity m).1
  have hsq : sgnW m * sgnW m = 1 := by
    unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp
  calc sgnW (m + 1) = (sgnW m * sgnW m) * sgnW (m + 1) := by rw [hsq, one_mul]
    _ = sgnW m * (sgnW m * sgnW (m + 1)) := by ring
    _ = (-1) ^ m * sgnW m := by rw [h]; ring
end Formalism.FourierDecayAlt.P.SignAntidiagonal
