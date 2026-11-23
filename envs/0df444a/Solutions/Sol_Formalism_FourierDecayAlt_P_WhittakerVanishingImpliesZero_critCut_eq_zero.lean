-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.critCut_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:29.486988+00:00
-- url     : https://prove2.me/submissions/8c97f444-7a5e-4bdc-b77e-1904aca48df4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_lt_of_critCut_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution {n : ℕ} {δ : ℝ} {z : ℂ} {x : Fin n → ℂ} (hδ : 0 < δ)
    (h : 2 * δ ≤ ‖x - fun _ => z‖) : critCut δ z x = 0 := by
  by_contra hne
  have h2 : ‖x - fun _ => z‖ < 2 * δ :=
    (pi_norm_lt_iff (by positivity)).mpr fun k => lt_of_critCut_ne_zero hδ hne k
  exact absurd h (not_le.mpr h2)
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
