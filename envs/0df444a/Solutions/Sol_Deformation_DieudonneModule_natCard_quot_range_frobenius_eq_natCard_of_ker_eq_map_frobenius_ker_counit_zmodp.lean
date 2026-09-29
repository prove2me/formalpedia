-- Prove2me | solution 1 for Deformation.DieudonneModule.natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/58cc97fe-6586-52b1-9702-ab7172ea43fd

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_Deformation_DieudonneModule_map_surjective_and_exact_map_of_ker_eq_map_ker_counit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

universe v x

namespace COKERF
open Function Deformation

theorem frobenius_eq_map (p : ℕ) [Fact p.Prime] (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A]
    (Fk : A →ₐc[ZMod p] A) (hFk : ∀ x : A, Fk x = x ^ p) (z : DieudonneModule (ZMod p) p A) :
    DieudonneModule.frobenius (ZMod p) p A z = DieudonneModule.map (ZMod p) p Fk z := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [DieudonneModule.frobenius_of, DieudonneModule.map_of]
    congr 1
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    rw [coeff_wittHomFrobenius, coeff_wittHomMap, hFk]

end COKERF

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A]
    (hA : IsLocalRing (CartierDual (ZMod p) A))
    (Fk : A →ₐc[ZMod p] A) (hFk : ∀ x : A, Fk x = x ^ p)
    (B : Type x) [CommRing B] [Bialgebra (ZMod p) B]
    (q : A →ₐc[ZMod p] B) (hq : Function.Surjective q)
    (hker : RingHom.ker (q : A →ₐ[ZMod p] B) =
      Ideal.map (Fk : A →ₐ[ZMod p] A) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A))) :
    Nat.card (Deformation.DieudonneModule (ZMod p) p A ⧸
        (Deformation.DieudonneModule.frobenius (ZMod p) p A).range) =
      Nat.card (Deformation.DieudonneModule (ZMod p) p B) := by

  obtain ⟨hsurj, hexact⟩ :=
    Deformation.DieudonneModule.map_surjective_and_exact_map_of_ker_eq_map_ker_counit (ZMod p) p A A hA hA B Fk q hq hker

  have hF : Deformation.DieudonneModule.frobenius (ZMod p) p A = Deformation.DieudonneModule.map (ZMod p) p Fk :=
    AddMonoidHom.ext (COKERF.frobenius_eq_map p A Fk hFk)
  have hrange : (Deformation.DieudonneModule.frobenius (ZMod p) p A).range = (Deformation.DieudonneModule.map (ZMod p) p q).ker := by
    rw [hF]
    exact (AddMonoidHom.exact_iff.1 hexact).symm ▸ rfl
  rw [hrange]
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv

end S_Deformation_DieudonneModule_natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp
end P2MW
export P2MW.S_Deformation_DieudonneModule_natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp (solution)
