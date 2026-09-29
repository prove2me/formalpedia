-- Prove2me | solution 1 for Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/087a9f4c-dd95-579f-8148-2539193f1025

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Deformation_SplitCoordinates
import Theorems.Thm_Deformation_HondaSystem_exists_splitCoordinates_lawful_normalForm
import Theorems.Thm_Deformation_HondaSystem_existsUnique_coords_of_mem_fontaineFunctor_of_splitCoordinates
import Theorems.Thm_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates
import Theorems.Thm_Deformation_HondaSystem_exists_mvFormalGroup_cocycle_of_splitCoordinates
import Theorems.Thm_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X"
p2m_attr_erase "simp" "Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

open scoped TensorProduct
open MvPowerSeries

universe u v

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x) :
    ∃ (L : ℕ → Type u) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra 𝓞 (L v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (L v)) (_ : ∀ v, Module.Free 𝓞 (L v))
      (_ : ∀ v, Module.Finite 𝓞 (L v)) (t : ∀ v, L (v + 1) →ₐc[𝓞] L v),
      (∀ v, Function.Surjective (t v)) ∧ (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r)) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
    ∃ e : ∀ v, G v →ₐc[ZMod p] TensorProduct 𝓞 (ZMod p) (L v),
      (∀ v, Function.Bijective (e v)) ∧
      (∀ v, (e v).comp (s v) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)).comp (e (v + 1))) ∧
      (∀ v, ∀ x ∈ H₁.L, Deformation.DieudonneModule.map (ZMod p) p (e v) (π v x) ∈
        Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom) := by

  obtain ⟨𝒮, hℒ, hNF⟩ :=
    Deformation.HondaSystem.exists_splitCoordinates_lawful_normalForm p hp hker r H₁ G s hs hrankG hkerG hunipG
      π hπ hπker hπF hπV hπs

  obtain ⟨Φ, hΦcomm, c₂, hΦ, h1, h2, h3, h4, h5, hLOGA⟩ :=
    Deformation.HondaSystem.exists_mvFormalGroup_cocycle_of_splitCoordinates p hp hker r H₁ G s hs hrankG hkerG
      hunipG π hπ hπker hπF hπV hπs 𝒮 hℒ hNF
      (fun g _ _ hpg hcg => by
        haveI := hcg
        exact Deformation.HondaSystem.existsUnique_coords_of_mem_fontaineFunctor_of_splitCoordinates p hp hker r
          H₁ G s hs hrankG hkerG hunipG π hπ hπker hπF hπV hπs 𝒮 hℒ hNF g hpg)
      (fun g _ _ hpg hcg => by
        haveI := hcg
        exact Deformation.HondaSystem.exists_mem_fontaineFunctor_of_coords_of_splitCoordinates p hp hker r
          H₁ G s hs hrankG hkerG hunipG π hπ hπker hπF hπV hπs 𝒮 hℒ hNF g hpg)

  haveI : Φ.IsComm := hΦcomm
  exact Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle
    p hp hker r H₁ G s hs hrankG hkerG hunipG π hπ hπker hπF hπV hπs 𝒮 hℒ Φ hΦ c₂ ⟨h1, h2, h3, h4, h5⟩ hLOGA

end S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod (solution)
