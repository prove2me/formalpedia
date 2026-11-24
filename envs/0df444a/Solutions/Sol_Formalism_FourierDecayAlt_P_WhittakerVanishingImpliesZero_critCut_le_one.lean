-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.critCut_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:54.131198+00:00
-- url     : https://prove2.me/submissions/d0c0f8f4-f089-4b3e-bc28-04d03509f8f0

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_chi0_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_smooth_cutoff_le_one

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
theorem _root_.solution {n : ℕ} (δ : ℝ) (z : ℂ) (x : Fin n → ℂ) : critCut δ z x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => chi0_nonneg _) fun _ _ => smooth_cutoff_le_one _
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
