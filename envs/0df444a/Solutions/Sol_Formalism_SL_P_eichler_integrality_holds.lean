-- Prove2me | solution 1 for Formalism.SL.P.eichler_integrality_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:39.197166+00:00
-- url     : https://prove2.me/submissions/d9cb5f15-fb8b-494c-9a23-ed7a519bf6fd

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
theorem _root_.solution : Formalism.SL.IwahoriBlocks.EichInt := by
  intro E _ _ V _ _ h O abelian₂ x x' u s hH hO hint hu hb hsx hx'x hux hux' v hv hvx'
  have hx'u : h x' u = 0 := by rw [hH, hux', star_zero]
  have hvx : h v x = h v (x + x') := by simp [hvx']
  have key : eich h x u s (eich h x' u s v) = v + h v u • (x + x') - (h v x + h v u * h x' x) • (u + s • x) := by
    simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
      LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hvx', hx'u, mul_zero, add_zero, sub_zero, zero_smul, zero_mul, smul_zero]
    module
  rw [key]
  have hvu := hint v hv u hu
  have hk : h v x + h v u * h x' x ∈ O := O.add_mem (hvx ▸ hint v hv _ hb) (O.mul_mem hvu hx'x)
  exact abelian₂.sub_mem (abelian₂.add_mem hv (hO _ hvu _ hb)) (hO _ hk _ (abelian₂.add_mem hu hsx))
end Formalism.SL.P
