-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isPeriodMap_of_lieVarpi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d9dc3904-85f2-576b-9433-9b8a0631161c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_PeriodMap

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_theta_apply_eta_eq_of_rule
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isPeriodValue_of_isAdmissible
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_of_isIsomorphic
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_isBaseChange
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_isQuadrupleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isPeriodMap_of_lieVarpi_eq_zero
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
    (h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    :
    ∃ θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B,
      CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap p k ι Φ M η hcΦ rΦ θ := by
  classical
  have hd : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
      (hB : IsNilpotent (p : B)) (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ),
      ∃ d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsPeriodValue ι hcΦ rΦ ψ d :=
    fun B _ _ _ ψ hB t ht => CerednikDrinfeld.SpecialFormal.Rigidified.exists_isPeriodValue_of_isAdmissible p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ ψ hB t ht
  obtain ⟨θ, hθd, hθnat⟩ := CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_theta_apply_eta_eq_of_rule p k ι Φ hΦ hΦ4 h0 M hM η hη
    (fun B _ _ _ ψ hB t ht => Rigidified.periodValue ι hcΦ rΦ ψ t (hd B ψ hB t ht))
    (fun B _ _ _ ψ hB t t' ht ht' htt' =>
      CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.eq p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ ψ hB t' ht' _ _
        (CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.of_isIsomorphic p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ ψ hB t t' ht ht' htt' _
          (Rigidified.periodValue_spec ι hcΦ rΦ ψ t (hd B ψ hB t ht)))
        (Rigidified.periodValue_spec ι hcΦ rΦ ψ t' (hd B ψ hB t' ht')))
    (fun B B' _ _ _ _ _ _ ψ ψ' hB hB' f hf t ht ht' =>
      CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isBaseChange p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ ψ hB ψ' hB' f hf t ht _
        (Rigidified.periodValue_spec ι hcΦ rΦ ψ t (hd B ψ hB t ht)) _
        (Rigidified.periodValue_spec ι hcΦ rΦ ψ' (t.map (f : B →+* B')) (hd B' ψ' hB' (t.map (f : B →+* B')) ht')))
  refine ⟨θ, ?_, hθnat⟩
  intro B _ _ _ ψ hB t ht Q hQ
  rw [hθd B ψ hB t ht]
  exact CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isQuadrupleOf p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ ψ hB t ht _
    (Rigidified.periodValue_spec ι hcΦ rΦ ψ t (hd B ψ hB t ht)) Q hQ

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isPeriodMap_of_lieVarpi_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isPeriodMap_of_lieVarpi_eq_zero (solution)
