-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d7d28d74-ba6a-586b-8a35-3167def87b70

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData_wittVector_quotient
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isHomogeneousVBasis_bcPhi_apply
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_u_nMap_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L') :
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ)
      (w : Fin 2 → ℤ_[p]), (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (rΦ w) ∈ (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0) := by
  classical
  intro LΦ hLΦ w

  obtain ⟨L₀, hL₀⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed p k ι Φ hΦ hcΦ
  have hw := (hrΦ L₀ hL₀).mapsTo (Set.mem_univ w)
  change rΦ w ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).eta L₀ hL₀.isCartierLMap.map_verschiebung ⊓ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nPiece 0 at hw
  change _ ∈ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).eta LΦ hLΦ.isCartierLMap.map_verschiebung ⊓ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nPiece 0
  rw [AddSubgroup.mem_inf] at hw ⊢

  have hDΦ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData_wittVector_quotient p k ι Φ hΦ hcΦ
  obtain ⟨γ, hγ, hγ'⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isHomogeneousVBasis_bcPhi_apply p k ι Φ hΦ hcΦ ψ' (Rigidified.awayHom (1 : K)) hcΦ1
  have hγlaw := CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt p
    (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) hcΦ1 (fun i => (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (γ i)) hγ'
  have hDbar := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) _ hγlaw hcΦ1).2

  have hWW : ∀ v : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)),
      WittVector.map (reduceMap (p := p) (Rigidified.awayHom (1 : K))) (WittVector.map (residueMap (p := p) ψ') v) = WittVector.map ((reduceMap (p := p) (Rigidified.awayHom (1 : K))).comp (residueMap (p := p) ψ')) v := by
    intro v; ext n; simp [WittVector.map_coeff]

  have hBC : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' ((reduceMap (p := p) (Rigidified.awayHom (1 : K))).comp (residueMap (p := p) ψ')) (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨γ, hγ, hγ'⟩⟩
    · intro v x
      show MvFormalGroup.CartierModule.baseChange (reduceMap (p := p) (Rigidified.awayHom (1 : K)))
          (MvFormalGroup.CartierModule.baseChange (residueMap (p := p) ψ') (v • x)) = _
      erw [MvFormalGroup.CartierModule.baseChangeEq_smul_witt, MvFormalGroup.CartierModule.baseChangeEq_smul_witt, hWW]
      rfl
    · intro x
      rw [CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply,
        CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply]
      show MvFormalGroup.CartierModule.baseChange (reduceMap (p := p) (Rigidified.awayHom (1 : K)))
          (MvFormalGroup.CartierModule.baseChange (residueMap (p := p) ψ') (MvFormalGroup.CartierModule.frobenius x)) = _
      erw [MvFormalGroup.CartierModule.baseChangeEq_frobenius, MvFormalGroup.CartierModule.baseChangeEq_frobenius]
      rfl
    · intro x
      rw [CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply,
        CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply]
      exact Rigidified.bcPhi_verschiebungInt ψ' (Rigidified.awayHom (1 : K)) x
    · intro x
      rw [CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply,
        CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply]
      exact Rigidified.bcPhi_endAct_varpiEnd ψ' (Rigidified.awayHom (1 : K)) x
    · intro i x hx
      have hx' := (CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff Φ _ hcΦ i x).mp hx
      refine (CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcΦ1 i _).mpr ?_
      exact CerednikDrinfeld.FormalODModule.baseChange_mem_gradedPiece _ _ _ _
        (CerednikDrinfeld.FormalODModule.baseChange_mem_gradedPiece _ _ _ _ hx')

  have hB : IsNilpotent (p : WittVector p k ⧸ pIdeal p (WittVector p k)) := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hB' : IsNilpotent (p : Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  have hnat := CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) ((reduceMap (p := p) (Rigidified.awayHom (1 : K))).comp (residueMap (p := p) ψ')) rfl
    hB hB' (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) hDΦ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) hDbar (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) hBC L₀ hL₀ LΦ hLΦ
  constructor
  · exact (CerednikDrinfeld.GradedCartierModuleData.u_nMap_of_comp_eq p (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K)))
      (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K)))
      L₀ hL₀.isCartierLMap.map_verschiebung LΦ hLΦ.isCartierLMap.map_verschiebung hnat (rΦ w) hw.1).1
  · obtain ⟨⟨m, m'⟩, hmm, hEq⟩ := AddSubgroup.mem_map.mp hw.2
    rw [← hEq, CerednikDrinfeld.GradedCartierModuleData.nMap_nMk]
    refine AddSubgroup.mem_map.mpr ⟨((Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) m, (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) m'), ⟨hBC.2.2.2.2.1 0 m hmm.1, hBC.2.2.2.2.1 0 m' hmm.2⟩, rfl⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed (solution)
