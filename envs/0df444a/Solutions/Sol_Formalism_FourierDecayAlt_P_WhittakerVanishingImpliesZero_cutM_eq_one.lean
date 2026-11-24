-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cutM_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:57.209915+00:00
-- url     : https://prove2.me/submissions/ebe3a73a-1ae7-47dd-a10d-48164e686e48

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
theorem _root_.solution {s : ℕ} {τ : ℝ} {Z : Mat s} (hτ : 0 < τ) (h : ‖Z‖ ≤ τ) : cutM τ Z = 1 := by
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => extendedCharacter_one ?_
  have h1 : ‖Z i j‖ ≤ τ := ((norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i)).trans h
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
