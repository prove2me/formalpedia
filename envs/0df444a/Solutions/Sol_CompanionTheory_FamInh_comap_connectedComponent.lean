-- Prove2me | solution 1 for CompanionTheory.FamInh.comap_connectedComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:13:28.432688+00:00
-- url     : https://prove2.me/submissions/db79963e-40ac-48dd-8877-90dda341f660

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinKer
import Theorems.Thm_CompanionTheory_FamInh_isOpen_connInf
import Theorems.Thm_CompanionTheory_FamInh_ofInfinite_eq_map
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_inv
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_mul
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_isOpenMap_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ker_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_toFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_toInfinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_exists_finiteLevel_subset
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_finiteLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ofFinite_mul_ofInfinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology GroundTheory.Global GroundTheory.Global.IdeleGroup
open CompanionTheory CompanionTheory.FamInh
namespace CompanionTheory.FamInh
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    (Subgroup.connectedComponentOfOne (GroundTheory.Global.IdeleClassGroup E)).comap (GroundTheory.Global.IdeleClassGroup.mk E) =
      ((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E).topologicalClosure := by
  apply le_antisymm
  · intro x hx
    have hx' : IdeleClassGroup.mk E x ∈ connectedComponent (1 : IdeleClassGroup E) := hx
    show x ∈ closure (((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E : Subgroup (IdeleGroup E)) :
      Set (IdeleGroup E))
    rw [mem_closure_iff_nhds]
    intro t ht
    have hc : Continuous fun u : (FiniteAdeleRing (𝓞 E) E)ˣ => x * (ofFinite u : IdeleGroup E)⁻¹ :=
      continuous_const.mul continuous_ofFinite.inv
    have hW : (fun u : (FiniteAdeleRing (𝓞 E) E)ˣ => x * (ofFinite u : IdeleGroup E)⁻¹) ⁻¹' t ∈ 𝓝 1 :=
      hc.continuousAt.preimage_mem_nhds (by simpa using ht)
    obtain ⟨S, n, -, hn0, hsub⟩ := exists_finiteLevel_subset hW
    have hsupp : (Function.support n).Finite :=
      S.finite_toSet.subset fun v hv => by
        by_contra h
        exact hv (hn0 v h)
    let V : Subgroup (IdeleGroup E) :=
      (Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ).comap (toInfinite E) ⊓
        (finiteLevel n).comap (toFinite E)
    have hV : IsOpen (V : Set (IdeleGroup E)) :=
      ((isOpen_connInf E).preimage (continuous_toInfinite E)).inter
        ((isOpen_finiteLevel hsupp).preimage (continuous_toFinite E))
    have hVo : IsOpen ((V.map (IdeleClassGroup.mk E) : Subgroup (IdeleClassGroup E)) : Set (IdeleClassGroup E)) :=
      IdeleClassGroup.isOpenMap_mk E _ hV
    have hcl : IsClopen ((V.map (IdeleClassGroup.mk E) : Subgroup (IdeleClassGroup E)) : Set (IdeleClassGroup E)) :=
      ⟨Subgroup.isClosed_of_isOpen _ hVo, hVo⟩
    obtain ⟨y, hy, hyx⟩ := hcl.connectedComponent_subset (one_mem _) hx'
    have hk : x * y⁻¹ ∈ (IdeleClassGroup.mk E).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, mul_inv_cancel]
    rw [IdeleClassGroup.ker_mk] at hk
    refine ⟨x * (ofFinite (toFinite E y))⁻¹, hsub hy.2, ?_⟩
    have e : x * (ofFinite (toFinite E y))⁻¹ = (x * y⁻¹) * ofInfinite (toInfinite E y) := by
      have h := ofFinite_mul_ofInfinite y
      generalize ofFinite (toFinite E y) = a at h ⊢
      generalize ofInfinite (toInfinite E y) = b at h ⊢
      subst h
      rw [mul_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact Subgroup.mul_mem_sup hk ⟨toInfinite E y, hy.1, (ofInfinite_eq_map E _).symm⟩
  · refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
    · rintro _ ⟨k, rfl⟩
      show IdeleClassGroup.mk E (diagonal E k) ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup E)
      rw [IdeleClassGroup.mk_diagonal]
      exact one_mem _
    · rintro _ ⟨y, hy, rfl⟩
      let f : (InfiniteAdeleRing E)ˣ →* IdeleClassGroup E := (IdeleClassGroup.mk E).comp
        (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)))
      have hf : Continuous f := (IdeleClassGroup.continuous_mk E).comp
        (Continuous.units_map _ (continuous_id.prodMk continuous_const))
      have h := hf.image_connectedComponent_subset 1 ⟨y, hy, rfl⟩
      rw [map_one] at h
      exact h
    · exact isClosed_connectedComponent.preimage (IdeleClassGroup.continuous_mk E)
end CompanionTheory.FamInh
