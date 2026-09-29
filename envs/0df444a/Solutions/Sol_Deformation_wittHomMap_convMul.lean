-- Prove2me | solution 1 for Deformation.wittHomMap_convMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/739656fb-7180-5b18-a940-ed116809307b

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_wittHomMap_convMul

set_option autoImplicit false

open Function Deformation Deformation.TruncWitt

universe u v w

theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] [Coalgebra.IsCocomm R B]
    (φ ψ : WithConv (B →ₐc[R] A)) (x : Deformation.wittHom R p n B) :
    Deformation.wittHomMap p n (φ * ψ).ofConv x =
      Deformation.wittHomMap p n φ.ofConv x + Deformation.wittHomMap p n ψ.ofConv x := by
  refine Subtype.ext ?_
  rw [AddSubgroup.coe_add, coe_wittHomMap, coe_wittHomMap, coe_wittHomMap]
  have h := map_convMul_of_mem_wittHom (T := A) x.2
    (WithConv.toConv (φ.ofConv : B →ₐ[R] A)) (WithConv.toConv (ψ.ofConv : B →ₐ[R] A))
  have hmul : ((φ * ψ).ofConv : B →ₐ[R] A) =
      (WithConv.toConv (φ.ofConv : B →ₐ[R] A) * WithConv.toConv (ψ.ofConv : B →ₐ[R] A)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul φ ψ)
  rw [hmul]
  exact h

end S_Deformation_wittHomMap_convMul
end P2MW
export P2MW.S_Deformation_wittHomMap_convMul (solution)
