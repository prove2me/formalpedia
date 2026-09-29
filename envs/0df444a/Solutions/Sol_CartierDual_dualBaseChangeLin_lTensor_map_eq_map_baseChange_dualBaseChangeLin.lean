-- Prove2me | solution 1 for CartierDual.dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/73256a79-c83b-563e-9d11-360d58f50183

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (O : Type) [CommRing O] (F : Type) [CommRing F] [Algebra O F]
    (A : Type) [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Free O A]
    (f : A →ₐc[O] A) (w : F ⊗[O] CartierDual O A) :
    CartierDual.dualBaseChangeLin O F A
        (LinearMap.lTensor F ((CartierDual.map f : CartierDual O A →ₐc[O] CartierDual O A) :
          CartierDual O A →ₗ[O] CartierDual O A) w) =
      CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id F F) f)
        (CartierDual.dualBaseChangeLin O F A w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c φ =>
      rw [LinearMap.lTensor_tmul]
      refine CartierDual.ext fun x => ?_
      rw [CartierDual.map_apply]
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | tmul c' a =>
          rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply,
            CartierDual.dualBaseChangeLin_tmul_tmul, CartierDual.dualBaseChangeLin_tmul_tmul]
          rfl
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy, ← map_add, ← map_add]

end S_CartierDual_dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin
end P2MW
export P2MW.S_CartierDual_dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin (solution)
