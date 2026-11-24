-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CommonEigenvectors.hval_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:56:39.661649+00:00
-- url     : https://prove2.me/submissions/11117b67-bbf6-41bc-9b3d-6aa77d4f4093

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CommonEigenvectors
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CommonEigenvectors
theorem _root_.solution {n : ℕ} (θ : Fin n → ℂ) :
    (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c).re = hval θ := by
  unfold hval
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [Complex.mul_re]
end Formalism.FourierDecayAlt.P.CommonEigenvectors
