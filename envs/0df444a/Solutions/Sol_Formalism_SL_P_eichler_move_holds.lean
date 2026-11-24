-- Prove2me | solution 1 for Formalism.SL.P.eichler_move_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:41.11875+00:00
-- url     : https://prove2.me/submissions/fd84fbdd-fd9a-40db-a952-bbe7f9b1faeb

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
theorem _root_.solution : Formalism.SL.IwahoriBlocks.EichMove := by
  intro E _ _ V _ _ h x x' u s hH hux hux' v hv
  have hx'u : h x' u = 0 := by rw [hH, hux', star_zero]
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hv, hx'u, mul_zero, add_zero, sub_zero, zero_smul, zero_mul, smul_zero]
  module
end Formalism.SL.P
