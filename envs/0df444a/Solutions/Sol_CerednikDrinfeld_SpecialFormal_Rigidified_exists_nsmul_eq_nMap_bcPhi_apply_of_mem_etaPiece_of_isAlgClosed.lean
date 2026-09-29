-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/678b615f-5f90-5de1-a466-d6f9ac596285

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
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed_uniform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.SpecialFormal.Rigidified in

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
      (x : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod), x ∈ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0 →
      ∃ (N : ℕ) (w : Fin 2 → ℤ_[p]), p ^ N • x = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (rΦ w) := by
  intro LΦ hLΦ x hx
  obtain ⟨N, hN⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed_uniform p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ K ψ' hK t' ht' hc hcb hcΦ1 L' hL' LΦ hLΦ
  exact ⟨N, hN x hx⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed (solution)
