-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fd632e7e-f453-52da-bf73-36aa1e9d6e62

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_algClosed_eq_of_isReduced
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isBaseChange_of_isQuadrupleOf
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_edgeRingCharP
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isQuadrupleOf_of_isCartierQuadruple_map_of_forall_algClosed_line_eq
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm MvFormalGroup.CartierModule.instModulePadicInt"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj CerednikDrinfeld.Standard.emb_inr"
p2m_attr_erase "simp" "CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

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
    :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
      (hB : IsNilpotent (p : B)) (hp0 : (p : B) = 0)
      (x : chartERing ℤ_[p] (p : ℤ_[p]) p →ₐ[ℤ_[p]] B)
      (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B),
      d.InEdgeChart (p : ℤ_[p]) (FullLattice.act g (stdFullLattice ℚ_[p])) (stdFullLattice ℚ_[p]) →
      d.line (stdFullLattice ℚ_[p]) =
        Submodule.span B {(x (chartERing.ξ ℤ_[p] (p : ℤ_[p]) p)) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : B) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} →
      d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
        (Submodule.span B {(1 : B) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (x (chartERing.η ℤ_[p] (p : ℤ_[p]) p)) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
          (actBaseChange B g (stdFullLattice ℚ_[p])).toLinearMap →
      ∃ (t : Rigidified p Φ B) (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B),
        t.IsAdmissible ι ψ ∧ t.IsCartierQuadruple ι hcΦ rΦ ψ Q ∧ Q.IsQuadrupleOf d := by
  intro B _ _ _ ψ hB hp0 x d hdin hl0 hl1
  classical

  have J_QN : IsNoetherianRing (FormalOmega.edgeQuot (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    unfold FormalOmega.edgeQuot; exact inferInstance
  haveI J_NOETH : IsNoetherianRing (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k))) p)) _ J_QN

  obtain ⟨tE, htE, hgeo⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_edgeRingCharP
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg

  have J1 : ∃ y : EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* B,
      y.comp (((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) = ψ ∧
      y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = x (chartERing.ξ ℤ_[p] (p : ℤ_[p]) p) ∧
      y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = x (chartERing.η ℤ_[p] (p : ℤ_[p]) p) := by

    have hker : ∀ a ∈ pIdeal p (WittVector p k), ψ a = 0 := by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, map_natCast, hp0, mul_zero]
    let ψbar : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* B := Ideal.Quotient.lift (pIdeal p (WittVector p k)) ψ hker
    letI : Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) B := ψbar.toAlgebra

    have hprod : x (chartERing.ξ ℤ_[p] (p : ℤ_[p]) p) * x (chartERing.η ℤ_[p] (p : ℤ_[p]) p) =
        algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) B 0 := by
      rw [← map_mul, chartERing.ξ_mul_η, AlgHom.commutes, map_zero, map_natCast, hp0]
    have hdisc := (chartERing.isUnit_discr ℤ_[p] (p : ℤ_[p]) p).map x
    rw [map_mul, map_sub, map_sub, map_pow, map_pow, map_one] at hdisc
    let pt : (chartE (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k))) p).obj B :=
      ⟨(x (chartERing.ξ ℤ_[p] (p : ℤ_[p]) p), x (chartERing.η ℤ_[p] (p : ℤ_[p]) p)), hprod,
        isUnit_of_mul_isUnit_left hdisc, isUnit_of_mul_isUnit_right hdisc⟩
    refine ⟨(chartERing.lift pt).toRingHom, ?_, ?_, ?_⟩
    · ext a
      show chartERing.lift pt (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) (Ideal.Quotient.mk (pIdeal p (WittVector p k)) a)) = ψ a
      rw [AlgHom.commutes]
      exact Ideal.Quotient.lift_mk (pIdeal p (WittVector p k)) ψ hker
    · exact chartERing.lift_ξ pt
    · exact chartERing.lift_η pt
  obtain ⟨y, hyψ, hyξ, hyη⟩ := J1

  have hadm : (tE.map y).IsAdmissible ι ψ := by
    have h := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι
      (((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) y tE htE
    rwa [hyψ] at h

  have hLΦ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
    p k ι Φ hΦ hcΦ

  obtain ⟨Q, hQ⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB (tE.map y) hadm

  have hirr : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  have J_FIN : Finite (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).toEquiv.symm
  have hBπ : IsNilpotent (algebraMap ℤ_[p] B (p : ℤ_[p])) := by
    rwa [map_natCast]
  obtain ⟨d', hd', -⟩ :=
    (CerednikDrinfeld.FormalOmega.DrinfeldDatum.forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent
      (K := ℚ_[p]) hirr J_FIN B hBπ).1 Q

  have KEY : d' = d :=
    CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isQuadrupleOf_of_isCartierQuadruple_map_of_forall_algClosed_line_eq
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg tE htE hgeo B ψ hB hp0 x d hdin hl0 hl1 y hyψ hyξ hyη Q d' hQ hd'
  subst KEY
  exact ⟨tE.map y, Q, hadm, hQ, hd'⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP (solution)
