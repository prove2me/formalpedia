-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.la_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:41:34.743299+00:00
-- url     : https://prove2.me/submissions/67e7592d-f3c6-4c35-b910-c9b2dee809b8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_la_ideal

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
theorem _root_.solution {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] {k r : ℕ}
    {z' : Fin (2 * r + k + 1) → ℂ} {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {La : A →ₗ[ℂ] M}
    (hR : RightRuleFn k r z' E La) {x y : A} (hx : x - y ∈ Ideal.span (rgen k r z' E)) : La x = La y := by
  have := la_ideal hR hx
  rwa [map_sub, sub_eq_zero] at this
end Formalism.FourierDecayAlt.P.SignAntidiagonal
