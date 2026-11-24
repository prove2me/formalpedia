-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.AAv_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:13.955002+00:00
-- url     : https://prove2.me/submissions/a5d63628-8ea5-4b42-ab65-0501398f7951

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr

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
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (ell : ℂ) :
    AAv k r E y m1 h1 ell = AAv k r E y m2 h2 ell := by subst h; rfl
end Formalism.FourierDecayAlt.P.SignAntidiagonal
