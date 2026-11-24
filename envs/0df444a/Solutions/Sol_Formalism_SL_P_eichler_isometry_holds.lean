-- Prove2me | solution 1 for Formalism.SL.P.eichler_isometry_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:40.234874+00:00
-- url     : https://prove2.me/submissions/c11b8d35-5c15-4d27-b638-8ef8ad40dc3f

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
theorem _root_.solution : Formalism.SL.IwahoriBlocks.EichIsom := by
  intro E _ _ V _ _ h x u s hH hxx hux hs v w
  have hxu : h x u = 0 := by rw [hH, hux, star_zero]
  have hxw : h x w = star (h w x) := hH w x
  have huw : h u w = star (h w u) := hH w u
  have hxv : h x v = star (h v x) := hH v x
  have huv : h u v = star (h v u) := hH v u
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hxx, hux, hxu, hxw, huw, starRingEnd_apply, star_add, star_sub, star_mul', star_star, mul_zero, add_zero, sub_zero]
  rw [← hs]
  ring
end Formalism.SL.P
