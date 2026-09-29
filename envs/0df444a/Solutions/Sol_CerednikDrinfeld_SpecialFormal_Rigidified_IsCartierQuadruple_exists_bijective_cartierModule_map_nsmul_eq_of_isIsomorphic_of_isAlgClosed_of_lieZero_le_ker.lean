-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2b0b5f52-8854-5344-99aa-4955c30f4c68

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
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isEtaSection_iff_of_bijective_XS_awayHom_of_lieZero_le_ker
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {κ : Type} [Field κ] [IsAlgClosed κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t t' : Rigidified p Φ κ) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ ψ Q')
    (hiso : Q.IsIsomorphic Q') :
    ∃ (Ψ : MvFormalGroup 2 κ) (_ : Ψ.IsComm) (ρκ : Ψ.Hom t.X.F) (ρκ' : Ψ.Hom t'.X.F)
      (θ : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p t'.X.F),
      Series.map (Ideal.Quotient.mk (pIdeal p κ)) ρκ.toPowerSeries = t.ρ ∧
      Series.map (Ideal.Quotient.mk (pIdeal p κ)) ρκ'.toPowerSeries = t'.ρ ∧
      Function.Bijective θ ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) = MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) = MvFormalGroup.CartierModule.verschiebung (θ f)) ∧
      (∀ (a : κ) f, θ (MvFormalGroup.CartierModule.homothety a f) = MvFormalGroup.CartierModule.homothety a (θ f)) ∧
      (∀ (a : Zp2 p) f, θ (MvFormalGroup.CartierModule.endAct (t.X.actEnd a) f) =
        MvFormalGroup.CartierModule.endAct (t'.X.actEnd a) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct t.X.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct t'.X.varpiEnd (θ f)) ∧
      ∃ c : ℕ, ∀ f : MvFormalGroup.CartierModule p Ψ,
        θ (MvFormalGroup.CartierModule.map ρκ (p ^ (c + t'.n) • f)) =
          MvFormalGroup.CartierModule.map ρκ' (p ^ (c + t.n) • f) := by
  have hκ : IsNilpotent (p : κ) := ⟨1, by rw [pow_one]; exact CharP.cast_eq_zero κ p⟩
  have hLΦ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed p k ι Φ hΦ hcΦ
  obtain ⟨τ₀, τ₁, -, -, hrest⟩ := hQ.2
  obtain ⟨τ₀', τ₁', -, -, hrest'⟩ := hQ'.2
  obtain ⟨hc, hcb, hcΦ1, L, hL, -⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hκ t ht Q.N₀ (fun x => (hrest ht.2.2.1 x).1)
  obtain ⟨hc', hcb', -, L', hL', -⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hκ t' ht' Q'.N₀ (fun x => (hrest' ht'.2.2.1 x).1)
  obtain ⟨i, hi, hi', θη, τ, hθη, hτ, hcompat, hcoord⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ t t' ht ht' Q Q' hQ hQ' hiso hQ.1 hQ'.1 hc hcb hc' hcb' hcΦ1 L hL L' hL'
  obtain ⟨Θ, hΘ, hΘF, hΘV, hΘW, hΘa, hΘPi, hΘη⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ t t' ht ht' Q Q' hQ hQ' hiso hQ.1 hQ'.1 hc hcb hc' hcb' hcΦ1 L hL L' hL' i hi hi' θη τ hθη hτ hcompat
  exact CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isEtaSection_iff_of_bijective_XS_awayHom_of_lieZero_le_ker p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ t t' ht ht' Q Q' hQ hQ' hiso hQ.1 hQ'.1 hc hcb hc' hcb' hcΦ1 L hL L' hL' i hi hi' θη hcoord Θ hΘ hΘF hΘV hΘW hΘa hΘPi hΘη

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker (solution)
