-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.matrix_cutoff_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:59.974995+00:00
-- url     : https://prove2.me/submissions/f68c62a6-9e4c-461e-9c41-46330a4688eb

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_deriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6 Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.CutMSpec := by
  intro s
  refine ⟨fun τ Z hτ => ⟨cutM_nonneg τ Z, cutM_le_one τ Z, cutM_eq_one hτ, cutM_eq_zero hτ⟩, fun k => ?_⟩
  obtain ⟨C, _, hC⟩ := cutM_deriv s k
  exact ⟨C, fun τ hτ => ⟨cutM_contDiff τ (n := k), hC τ hτ⟩⟩
end Formalism.FourierDecayAlt.P
