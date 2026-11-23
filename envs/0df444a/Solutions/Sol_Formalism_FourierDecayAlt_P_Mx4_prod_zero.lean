-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.prod_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:52.403151+00:00
-- url     : https://prove2.me/submissions/73176e99-14b3-4dce-9125-160523f3afc8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sR_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution {P : Par} {l j : ℕ} {π π2 : Ty P} (h : ¬ ∃ π1, Up P l π π1 ∧ Up P j π1 π2) :
    (sR P j * sR P l) π2 π = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases h1 : Up P l π b
  · rw [sR_neg (l := j) (π := b) (π' := π2) (fun h2 => h ⟨b, h1, h2⟩), zero_mul]
  · rw [sR_neg h1, mul_zero]
end Formalism.FourierDecayAlt.P.Mx4
