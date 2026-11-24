-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.AAx_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:15.355382+00:00
-- url     : https://prove2.me/submissions/f78a3daa-0e69-497a-b075-3e8648490f89

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
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (u : ℂ) :
    AAx k r E xi m1 h1 u = AAx k r E xi m2 h2 u := by subst h; rfl
end Formalism.FourierDecayAlt.P.SignAntidiagonal
