-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/428d6176-9d3e-5a13-840f-8a1d9570da22

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_ne_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
(X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
(hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
(hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)

(f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
(m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
(hOD₀ : FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
(hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(a : ℕ)
(hN : ∀ i : Fin 2,
    p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) (Pi.single i 1) =
      p ^ (a + m) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
          ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] i))
(ρ₁ : FormalODModule.Hom ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X)
(hρ₁0 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1))
(hρ₁1 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0))
(hρ₁h : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X ρ₁.toSeries 4)
    :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* Ω),
      ∃ (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω),
        ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsCartierQuadruple ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q ∧
        Q.IsQuadrupleOf d ∧
        d.line (stdFullLattice ℚ_[p]) =
            Submodule.span Ω {(y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
          d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
            (Submodule.span Ω {(1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
              (actBaseChange Ω g (stdFullLattice ℚ_[p])).toLinearMap
 := by
  intro Ω _ _ _ y
  by_cases hξ : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0
  · by_cases hη : y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0
    · exact CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero
        p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN ρ₁ hρ₁0 hρ₁1 hρ₁h Ω y hξ hη
    · exact CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_ne_zero
        p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN ρ₁ hρ₁0 hρ₁1 hρ₁h Ω y hξ hη
  · exact CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_ne_zero
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN ρ₁ hρ₁0 hρ₁1 hρ₁h Ω y hξ

end S_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny (solution)
