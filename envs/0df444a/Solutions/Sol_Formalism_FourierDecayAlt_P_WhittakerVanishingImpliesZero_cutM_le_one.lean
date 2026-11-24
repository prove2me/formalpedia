-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cutM_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:38.846516+00:00
-- url     : https://prove2.me/submissions/436e8981-2119-4b5f-abe3-cf18574667d0

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
theorem _root_.solution {s : ℕ} (τ : ℝ) (Z : Mat s) : cutM τ Z ≤ 1 :=
  Finset.prod_le_one (fun _ _ => Finset.prod_nonneg fun _ _ => chi0_nonneg _)
    fun _ _ => Finset.prod_le_one (fun _ _ => chi0_nonneg _) fun _ _ => smooth_cutoff_le_one _
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
