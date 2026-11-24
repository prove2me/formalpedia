-- Prove2me | solution 1 for Formalism.SL.P.eichler_composition_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:38.039627+00:00
-- url     : https://prove2.me/submissions/94dfad4c-5697-4f6f-aaef-d39fb24d9f42

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementEI
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_EichlerEquivalenceHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.SL Formalism.SL.P
open Formalism.SL.IwahoriBlocks
namespace Formalism.SL.P
theorem _root_.solution : Formalism.SL.IwahoriBlocks.EichComp := by
  intro E _ _ V _ _ h x a b s t hH hxx hax hbx v
  have hxa : h x a = 0 := by rw [hH, hax, star_zero]
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hxx, hax, hbx, hxa, mul_zero, zero_mul, add_zero, sub_zero, zero_smul, smul_zero]
  module
end Formalism.SL.P
