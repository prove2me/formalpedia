-- Prove2me | solution 1 for Deformation.DieudonneModule.map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/48107299-ad50-5ba5-a57a-73f3163f1d39

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul

set_option autoImplicit false

open Deformation

set_option maxHeartbeats 6400000 in
open scoped TensorProduct in
theorem solution
    (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime]
    {A : Type} [CommRing A] [Bialgebra R A] {B : Type} [CommRing B] [Bialgebra R B]
    (f g h : A →ₐc[R] B)
    (hh : (h : A →ₐ[R] B).toLinearMap =
      LinearMap.mul' R B ∘ₗ TensorProduct.map (f : A →ₐ[R] B).toLinearMap (g : A →ₐ[R] B).toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := A))
    (x : Deformation.DieudonneModule R p A) :
    Deformation.DieudonneModule.map R p h x =
      Deformation.DieudonneModule.map R p f x + Deformation.DieudonneModule.map R p g x := by

  have hconv : (WithConv.toConv (f : A →ₐ[R] B) * WithConv.toConv (g : A →ₐ[R] B)).ofConv = (h : A →ₐ[R] B) := by
    apply AlgHom.toLinearMap_injective
    rw [hh]
    have h1 := AlgHom.toLinearMap_convMul (WithConv.toConv (f : A →ₐ[R] B)) (WithConv.toConv (g : A →ₐ[R] B))
    have h2 := congrArg WithConv.ofConv h1
    rw [WithConv.ofConv_toConv] at h2
    rw [h2, LinearMap.convMul_def]
  induction x using DieudonneModule.induction_on with
  | ih n y =>
    rw [DieudonneModule.map_of, DieudonneModule.map_of, DieudonneModule.map_of, ← map_add]
    congr 1
    apply Subtype.ext
    rw [AddSubgroup.coe_add, coe_wittHomMap, coe_wittHomMap, coe_wittHomMap]
    have key := map_convMul_of_mem_wittHom (T := B) y.2
      (WithConv.toConv (f : A →ₐ[R] B)) (WithConv.toConv (g : A →ₐ[R] B))
    rw [hconv, WithConv.ofConv_toConv, WithConv.ofConv_toConv] at key
    exact key

end S_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul
end P2MW
export P2MW.S_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul (solution)
