-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.zb_col_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:27:20.702821+00:00
-- url     : https://prove2.me/submissions/453022e0-a304-4a79-9090-32e1d7c9cc6d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity

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
theorem _root_.solution (i0 s' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (a : ℕ) (ha : a < i0 + s') :
    Zb i0 (s' + 1) h t a i0 = 0 := by
  unfold Zb
  split_ifs <;> first | rfl | (exfalso; omega)
end Formalism.FourierDecayAlt.P.SignAntidiagonal
