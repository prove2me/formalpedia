-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.critCut_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:53.756889+00:00
-- url     : https://prove2.me/submissions/2ad6351e-4b2a-4dbc-83ba-b9e001607413

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_extendedCharacter_one

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
    (h : ‖x - fun _ => z‖ ≤ δ) : critCut δ z x = 1 := by
  refine Finset.prod_eq_one fun k _ => extendedCharacter_one ?_
  have h1 : ‖x k - z‖ ≤ δ := (norm_le_pi_norm (x - fun _ => z) k).trans h
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
