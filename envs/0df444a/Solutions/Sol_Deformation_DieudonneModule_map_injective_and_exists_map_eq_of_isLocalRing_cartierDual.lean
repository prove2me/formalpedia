-- Prove2me | solution 1 for Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e308b699-8797-5252-86c5-5390c68a6a77

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

universe u v

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A]
    (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B]
    (hA : IsLocalRing (CartierDual (ZMod p) A)) (hB : IsLocalRing (CartierDual (ZMod p) B)) :
    (∀ g g' : B →ₐc[ZMod p] A,
        Deformation.DieudonneModule.map (ZMod p) p g = Deformation.DieudonneModule.map (ZMod p) p g' →
        g = g') ∧
    (∀ φ : Deformation.DieudonneModule (ZMod p) p B →+ Deformation.DieudonneModule (ZMod p) p A,
        (∀ z, φ (Deformation.DieudonneModule.frobenius (ZMod p) p B z) =
          Deformation.DieudonneModule.frobenius (ZMod p) p A (φ z)) →
        (∀ z, φ (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) =
          Deformation.DieudonneModule.verschiebung (ZMod p) p A (φ z)) →
        ∃ g : B →ₐc[ZMod p] A, Deformation.DieudonneModule.map (ZMod p) p g = φ) :=
  ⟨fun g g' h =>
    Deformation.DieudonneModule.eq_of_map_eq_of_isLocalRing_cartierDual (ZMod p) p A B hB g g' h,
   fun φ hF hV =>
    Deformation.DieudonneModule.exists_map_eq_of_isLocalRing_cartierDual p A B hB φ hF hV⟩

end S_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual (solution)
