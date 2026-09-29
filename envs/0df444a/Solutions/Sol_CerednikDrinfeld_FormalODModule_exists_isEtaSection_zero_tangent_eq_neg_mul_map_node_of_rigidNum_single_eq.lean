-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isEtaSection_zero_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7d6703fb-f547-5a01-8253-7a2aa146b4e3

import Mathlib
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_zero_of_lieZero_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
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
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_zero_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

set_option maxHeartbeats 8000000 in
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
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y₀ : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* Ω)
    :
    ∃ (hOD : FormalODModule.IsODHom (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).Φbar (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).Xbar ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).ρ)
      (hc : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).IsGradedS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω)))
      (hcb : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).IsGradedSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω)))
      (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω)))
      (L : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).M →+ ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).NMod)
      (hL : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).IsCanonicalLMap L)
      (z₀ z₁ : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).NMod)
      (hz₀ : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).IsEtaSection ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 0 z₀ (((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (hz₁ : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).IsEtaSection ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 0 z₁ (((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (m₀ m₁ : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).M),
      ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).vRange.mkQ m₀ = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩ ∧
      ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).vRange.mkQ m₁ = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩ ∧
      (∀ j : Fin 2, MvFormalGroup.CartierModule.tangent m₁ j =
        -(Rigidified.awayHom (1 : Ω) 0) * MvFormalGroup.CartierModule.tangent m₀ j) ∧
      ∃ j : Fin 2, MvFormalGroup.CartierModule.tangent m₀ j ≠ 0 := by
  classical

  have hpk : ((p : ℕ) : (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hpΩ : ((p : ℕ) : Ω) = 0 := by rw [← map_natCast y₀, hpk, map_zero]
  haveI hcharΩ : CharP Ω p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpΩ
  have hnil : IsNilpotent ((p : ℕ) : Ω) := ⟨1, by rw [pow_one, hpΩ]⟩

  have hJ : y₀.comp (f₀.comp (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) = (structureMap ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) := by
    show y₀.comp (f₀.comp (((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))).comp ι)) = (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))).comp ι
    have h1 : f₀.comp (((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))).comp ι) = (Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι := by
      ext z
      exact RingHom.congr_fun hf₀ _
    rw [h1, RingHom.comp_assoc]

  have hγΩ : ((X.map f₀).map y₀).IsHomogeneousVBasis (structureMap ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (fun i => baseChange y₀ (baseChange f₀ (γ i))) := by
    have h := (hγ.map f₀).map y₀
    rw [hJ] at h
    exact h
  have hγaΩ : ((X.map f₀).map y₀).HasStructureConstants (fun i => baseChange y₀ (baseChange f₀ (γ i))) (fun n i => y₀ (f₀ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k)) n i))) :=
    (hγa.map f₀).map y₀
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have ha0 : ∀ i : Fin 2, y₀ (f₀ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k)) 0 i)) = 0 := by
    intro i
    fin_cases i
    · show y₀ (f₀ (EdgeFamily.edgeConstants p _ _ 0 0)) = 0
      rw [EdgeFamily.edgeConstants_zero_zero, map_sub, map_pow, hf₀η, zero_pow hp0, sub_zero, map_zero]
    · show y₀ (f₀ (EdgeFamily.edgeConstants p _ _ 0 1)) = 0
      rw [EdgeFamily.edgeConstants_zero_one, map_sub, map_pow, hf₀ξ, zero_pow hp0, sub_zero, map_zero]

  obtain ⟨⟨ht0, ht1⟩, huniq0, huniq1, hLieC⟩ :=
    FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent p (structureMap ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hnil ((X.map f₀).map y₀) (fun i => baseChange y₀ (baseChange f₀ (γ i))) hγΩ
  have hlvγ : ∀ i : Fin 2, ((X.map f₀).map y₀).lieVarpi (tangent (baseChange y₀ (baseChange f₀ (γ i)))) = 0 := by
    intro i
    show Matrix.mulVecLin (MvFormalGroup.linearPart ((X.map f₀).map y₀).varpi) (tangent (baseChange y₀ (baseChange f₀ (γ i)))) = 0
    rw [Matrix.mulVecLin_apply]
    have key := FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants p ((X.map f₀).map y₀) (fun i => baseChange y₀ (baseChange f₀ (γ i))) _ hγaΩ i
    rw [ha0 i, zero_smul] at key
    exact key
  have hlv0 : ((X.map f₀).map y₀).lieZero (structureMap ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ≤ LinearMap.ker ((X.map f₀).map y₀).lieVarpi := by
    intro v hv
    obtain ⟨b, hb, -⟩ := huniq0 v hv
    rw [LinearMap.mem_ker, hb, map_smul, smul_eq_zero]
    exact Or.inr (hlvγ 0)
  have hlv1 : ((X.map f₀).map y₀).lieOne (structureMap ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ≤ LinearMap.ker ((X.map f₀).map y₀).lieVarpi := by
    intro v hv
    obtain ⟨b, hb, -⟩ := huniq1 v hv
    rw [LinearMap.mem_ker, hb, map_smul, smul_eq_zero]
    exact Or.inr (hlvγ 1)

  have hODΩ : FormalODModule.IsODHom (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).Φbar (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).Xbar ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).ρ := by
    have h := hOD₀.map (reduceMap (p := p) y₀)
    rw [← Rigidified.Φbar_map] at h
    have e : (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))).map (reduceMap (p := p) y₀) = ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).Xbar := by
      show ((X.map f₀).map _).map _ = ((X.map f₀).map y₀).map _
      simp only [FormalODModule.map_map]
      exact congrArg X.map (RingHom.ext fun _ => rfl)
    rw [e] at h
    exact h

  obtain ⟨hcS, hcbS, hcΦS⟩ :=
    Rigidified.isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hnil ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) (1 : Ω)

  have hR := CerednikDrinfeld.FormalODModule.smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq
    p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN
    Ω y₀ (Rigidified.awayHom (1 : Ω)) hODΩ hcbS hcΦS

  have hinjA : Function.Injective (algebraMap Ω (Rigidified.Baway (1 : Ω))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors one_ne_zero)
  haveI hcharB : CharP (Rigidified.Baway (1 : Ω)) p := charP_of_injective_algebraMap hinjA p
  have hpB : ((p : ℕ) : (Rigidified.Baway (1 : Ω))) = 0 := CharP.cast_eq_zero _ _
  have hsep : IsHausdorff (Ideal.span {((p : ℕ) : (Rigidified.Baway (1 : Ω)))}) (Rigidified.Baway (1 : Ω)) := by
    rw [hpB, Ideal.span_singleton_eq_bot.2 rfl]
    infer_instance

  have hγS : (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).IsHomogeneousVBasis (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) (fun i => baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) := hγΩ.map (Rigidified.awayHom (1 : Ω))
  obtain ⟨L, hL⟩ :=
    FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hsep (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))) (fun i => baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) hγS hcS
  have hcrit0 := FormalODModule.CritChart.isCritical_map_zero_of_lieZero_le_ker_lieVarpi p (structureMap ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ((X.map f₀).map y₀) hLieC hlv0 (Rigidified.awayHom (1 : Ω))
  have hcrit1 := FormalODModule.CritChart.isCritical_map_one_of_lieOne_le_ker_lieVarpi p (structureMap ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ((X.map f₀).map y₀) hLieC hlv1 (Rigidified.awayHom (1 : Ω))
  have hi0 : ∀ m' ∈ (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).gradedPiece (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) 0, ∃ g' : CartierModule p (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).F,
      verschiebungInt g' = endAct (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).varpiEnd m' := by
    intro m' hm'
    obtain ⟨g', hg'⟩ := hcrit0 m' hm'
    exact ⟨g', by rw [verschiebungInt_eq_verschiebung]; exact hg'⟩
  have hi1 : ∀ m' ∈ (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).gradedPiece (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) 1, ∃ g' : CartierModule p (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).F,
      verschiebungInt g' = endAct (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).varpiEnd m' := by
    intro m' hm'
    obtain ⟨g', hg'⟩ := hcrit1 m' hm'
    exact ⟨g', by rw [verschiebungInt_eq_verschiebung]; exact hg'⟩
  have hγaS : (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).HasStructureConstants (fun i => baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) (EdgeFamily.edgeConstants p (0 : (Rigidified.Baway (1 : Ω))) 0) := by
    have h := ((hγa.map f₀).map y₀).map (Rigidified.awayHom (1 : Ω))
    have e : (fun n i => (Rigidified.awayHom (1 : Ω)) (y₀ (f₀ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k)) n i)))) =
        EdgeFamily.edgeConstants p (0 : (Rigidified.Baway (1 : Ω))) 0 := by
      funext n i
      rw [EdgeFamily.edgeRingConstants, EdgeFamily.edgeConstants_map, EdgeFamily.edgeConstants_map,
        EdgeFamily.edgeConstants_map, hf₀ξ, hf₀η, map_zero, map_zero]
    rw [← e]
    exact h
  have hPiV : ∀ i : Fin 2, endAct (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).varpiEnd (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) = verschiebungInt (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) := by
    have h := FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
      p (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) (0 : (Rigidified.Baway (1 : Ω))) 0 (mul_zero _) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))) (fun i => baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) hγS hγaS
    simp only [zero_pow hp0, map_zero, sub_self, zero_smul, zero_add] at h
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  have hLγ : ∀ i : Fin 2, L (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))), 0) := by
    intro i
    fin_cases i
    · exact FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))) hcS L hL 0 hi0 _ _ (hγS.1 0) (hPiV 0).symm
    · exact FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))) hcS L hL 1 hi1 _ _ (hγS.1 1) (hPiV 1).symm
  have hnMk0 : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (0, 0) = 0 := map_zero _
  have hη : ∀ i : Fin 2, ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))), 0) ∈ ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).etaPiece L hL.isCartierLMap.map_verschiebung i := by
    intro i
    refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [GradedCartierModuleData.mem_eta_iff, GradedCartierModuleData.phi_nMk, hLγ i, hnMk0, add_zero]
    · exact AddSubgroup.mem_map.2 ⟨((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))), 0), AddSubgroup.mem_prod.2 ⟨hγS.1 i, zero_mem _⟩, rfl⟩
  have hnVarpi : ∀ m₁ m₂ : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).M, ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (m₁, m₂)) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).varpi m₁, ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).varpi m₂) :=
    fun _ _ => rfl
  have hnVarpiB : ∀ m₁ m₂ : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).M, ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (m₁, m₂)) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).varpi m₁, ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).varpi m₂) :=
    fun _ _ => rfl
  have hEtaPi : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0)) ∈ ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).etaPiece L hL.isCartierLMap.map_verschiebung 0 := by
    have e : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0)) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (verschiebungInt (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0) := by
      rw [hnVarpi, map_zero]
      show ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (endAct (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).varpiEnd (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0) = _
      rw [hPiV 1]
      rfl
    rw [e]
    refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [GradedCartierModuleData.mem_eta_iff, GradedCartierModuleData.phi_nMk, hnMk0, add_zero]
      show L (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).verschiebung (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1))))) = _
      rw [hL.isCartierLMap.map_verschiebung]
      show ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (endAct (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).varpiEnd (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0) = _
      rw [hPiV 1]
      rfl
    · refine AddSubgroup.mem_map.2 ⟨(verschiebungInt (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0), AddSubgroup.mem_prod.2 ⟨?_, zero_mem _⟩, rfl⟩
      have := ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).verschiebung_mem 1 _ (hγS.1 1)
      exact this

  have hred : ∀ i : Fin 2, ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).redC (Rigidified.awayHom (1 : Ω)) (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) = (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y₀ (baseChange f₀ (γ i))))) := by
    intro i
    refine MvFormalGroup.CartierModule.ext (funext fun j => ?_)
    simp only [Rigidified.redC, MvFormalGroup.CartierModule.baseChange,
      MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq]
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map]
    rfl
  have hetaRed0 : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).etaRed ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω)) hcS hcbS (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 0)))), 0)) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y₀ (baseChange f₀ (γ 0))))), 0) := by
    show (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).redC (Rigidified.awayHom (1 : Ω))) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).redC_verschiebungInt (Rigidified.awayHom (1 : Ω))) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).redC_endAct_varpiEnd (Rigidified.awayHom (1 : Ω)))) (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 0)))), 0)) = _
    erw [GradedCartierModuleData.nMap_nMk, map_zero, hred 0]
  have hetaRed1 : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).etaRed ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω)) hcS hcbS (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0))) =
      ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y₀ (baseChange f₀ (γ 1))))), 0)) := by
    rw [hnVarpi, hnVarpiB, map_zero, map_zero]
    show (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMap ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).redC (Rigidified.awayHom (1 : Ω))) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).redC_verschiebungInt (Rigidified.awayHom (1 : Ω))) (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).redC_endAct_varpiEnd (Rigidified.awayHom (1 : Ω)))) (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (endAct (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).varpiEnd (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0)) = ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (endAct (((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS (Rigidified.awayHom (1 : Ω))).varpiEnd (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y₀ (baseChange f₀ (γ 1))))), 0)
    erw [GradedCartierModuleData.nMap_nMk, map_zero, Rigidified.redC_endAct_varpiEnd, hred 1]

  have hn : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).n = m := rfl
  have hrel0 : p ^ a • ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).rigidNum ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hODΩ (Rigidified.awayHom (1 : Ω)) hcbS hcΦS (Pi.single 0 1) =
      p ^ (a + ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).n + 0) • ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).etaRed ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω)) hcS hcbS (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 0)))), 0)) := by
    rw [hR 0, hetaRed0, hn, add_zero]
    rfl
  have hrel1 : p ^ a • ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).rigidNum ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hODΩ (Rigidified.awayHom (1 : Ω)) hcbS hcΦS (Pi.single 1 1) =
      p ^ (a + ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).n + 0) • ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).etaRed ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω)) hcS hcbS (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0))) := by
    rw [hR 1, hetaRed1, hn, add_zero]
    rfl
  have hcoe : ∀ j : Fin 2, ((p : ℚ_[p]) ^ 0 • (Pi.single j 1 : Fin 2 → ℚ_[p])) = fun i => (((Pi.single j 1 : Fin 2 → ℤ_[p]) i : ℤ_[p]) : ℚ_[p]) := by
    intro j
    funext i
    rw [pow_zero, one_smul]
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]

  haveI : Nontrivial (Rigidified.Baway (1 : Ω)) := hinjA.nontrivial
  have hne : ∃ j : Fin 2, tangent (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 0)))) j ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hdet := hγS.2
    have h0 : (Matrix.of fun i k => tangent ((fun i => baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ i)))) i) k).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero 0 (fun k => hall k)
    exact hdet.ne_zero h0
  have hPiV1 : ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).varpi (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))) = verschiebungInt (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))) := hPiV 1
  refine ⟨hODΩ, hcS, hcbS, hcΦS, L, hL, ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 0)))), 0), ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0)), ?_, ?_,
    (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 0)))), ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) (Rigidified.awayHom (1 : Ω))) hcS).varpi (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1)))), rfl, rfl, ?_, hne⟩
  · rw [Rigidified.isEtaSection_zero_iff]
    exact ⟨hη 0, 0, a, Pi.single 0 1, hcoe 0, hrel0⟩
  · rw [Rigidified.isEtaSection_zero_iff]
    exact ⟨hEtaPi, 0, a, Pi.single 1 1, hcoe 1, hrel1⟩
  · intro j
    rw [map_zero, neg_zero, zero_mul, hPiV1]
    exact congrFun (tangent_verschiebungInt (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y₀ (baseChange f₀ (γ 1))))) j

end S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_zero_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_zero_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq (solution)
