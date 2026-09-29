-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.N_le_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2e15bcfc-4b5a-5232-aaa6-35126542adad

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

import Theorems.Thm_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_baseChange_comparison
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_of_isBaseChangeAlong_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_map_nMap_of_isBaseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_le_of_map
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[p] B'] (ψ' : O →+* B')
    (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B') (hf : (f : B →+* B').comp ψ = ψ')
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadruple ι hcΦ rΦ ψ' Q') (x' : PrimeSpectrum B') :
    Q.N₀ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₀ x' ∧ Q.N₁ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₁ x' := by
  obtain ⟨hOD, σ₀, σ₁, hT0, hT1, hrest⟩ := hQ
  obtain ⟨hOD', σ₀', σ₁', hT0', hT1', hrest'⟩ := hQ'
  obtain ⟨hN0, hN1, -, -⟩ := hrest hOD (DrinfeldDatum.pointUnder f x')
  obtain ⟨hN0', hN1', -, -⟩ := hrest' hOD' x'
  constructor
  · intro v hv
    obtain ⟨g, hg, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN0 v).1 hv
    refine (hN0' v).2 ?_

    obtain ⟨⟨fg, hfg⟩, hmem⟩ := CerednikDrinfeld.exists_ringHom_away_comp_eq_and_not_mem_iff (f : B →+* B') g
    have hg' : f g ∉ x'.asIdeal := (hmem x').2 hg
    have hge : (Rigidified.awayHom (f g)).comp (f : B →+* B') = fg.comp (Rigidified.awayHom g) := hfg.symm

    obtain ⟨hc', hcb', hcΦf'⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom ι ψ' hB' (t.map (f : B →+* B')) (f g)

    obtain ⟨S, _, jl, φl, hφl, htf, Dl, hDl, fl, hfl, Ll, hLl, hLeq⟩ := hL.exists_lift
    obtain ⟨γl, hγl, hγa⟩ := hfl.2.2.2.2.2
    have hγX := CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt p (Rigidified.jS ι ψ (Rigidified.awayHom g)) (t.XS (Rigidified.awayHom g)) hc
      (fun i => fl (γl i)) hγa
    have hDsp := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p (Rigidified.jS ι ψ (Rigidified.awayHom g)) (t.XS (Rigidified.awayHom g))
      (fun i => fl (γl i)) hγX hc).2

    obtain ⟨bc, hbc, htan, bcbar, hred, hrig⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_baseChange_comparison ι hcΦ rΦ ψ ψ' (f : B →+* B') hf t hOD hOD'
      (Rigidified.awayHom g) (Rigidified.awayHom (f g)) fg hge hc hcb hcΦf hc' hcb' hcΦf' (fun i => fl (γl i)) hγX

    obtain ⟨γ₂, hγ₂, hγ₂'⟩ := hbc.2.2.2.2.2
    have hγX' := CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt p (Rigidified.jS ι ψ' (Rigidified.awayHom (f g)))
      ((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))) hc' (fun i => bc (γ₂ i)) hγ₂'
    have hDsp' := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p (Rigidified.jS ι ψ' (Rigidified.awayHom (f g)))
      ((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))) (fun i => bc (γ₂ i)) hγX' hc').2
    have hj : fg.comp (Rigidified.jS ι ψ (Rigidified.awayHom g)) = Rigidified.jS ι ψ' (Rigidified.awayHom (f g)) := by
      rw [← hf]
      exact RingHom.ext fun a => (RingHom.congr_fun hge (ψ (ι a))).symm
    obtain ⟨L', hL'⟩ := CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong_of_comp_eq p (Rigidified.jS ι ψ (Rigidified.awayHom g))
      (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) fg hj ((t.XS (Rigidified.awayHom g)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom g)) hc) hDsp (((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) hc') hDsp' bc hbc L hL

    have hBg : IsNilpotent (p : (Rigidified.Baway g)) := by simpa using hB.map (Rigidified.awayHom g)
    have hBg' : IsNilpotent (p : (Rigidified.Baway (f g))) := by simpa using hB'.map (Rigidified.awayHom (f g))
    have hLL' := CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq p (Rigidified.jS ι ψ (Rigidified.awayHom g))
      (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) fg hj hBg hBg' ((t.XS (Rigidified.awayHom g)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom g)) hc) hDsp (((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) hc') hDsp' bc hbc L hL L' hL'

    have hz' := CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_map_nMap_of_isBaseChangeAlong ι hcΦ rΦ ψ ψ' (f : B →+* B') hf t hOD hOD'
      (Rigidified.awayHom g) (Rigidified.awayHom (f g)) fg hge hc hcb hcΦf hc' hcb' hcΦf' bc hbc L hL L' hL' hLL'
      bcbar hred hrig 0 z v hz
    exact ⟨f g, hg', hc', hcb', hcΦf', L', hL', _, hz'⟩
  · intro v hv
    obtain ⟨g, hg, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN1 v).1 hv
    refine (hN1' v).2 ?_

    obtain ⟨⟨fg, hfg⟩, hmem⟩ := CerednikDrinfeld.exists_ringHom_away_comp_eq_and_not_mem_iff (f : B →+* B') g
    have hg' : f g ∉ x'.asIdeal := (hmem x').2 hg
    have hge : (Rigidified.awayHom (f g)).comp (f : B →+* B') = fg.comp (Rigidified.awayHom g) := hfg.symm

    obtain ⟨hc', hcb', hcΦf'⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom ι ψ' hB' (t.map (f : B →+* B')) (f g)

    obtain ⟨S, _, jl, φl, hφl, htf, Dl, hDl, fl, hfl, Ll, hLl, hLeq⟩ := hL.exists_lift
    obtain ⟨γl, hγl, hγa⟩ := hfl.2.2.2.2.2
    have hγX := CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt p (Rigidified.jS ι ψ (Rigidified.awayHom g)) (t.XS (Rigidified.awayHom g)) hc
      (fun i => fl (γl i)) hγa
    have hDsp := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p (Rigidified.jS ι ψ (Rigidified.awayHom g)) (t.XS (Rigidified.awayHom g))
      (fun i => fl (γl i)) hγX hc).2

    obtain ⟨bc, hbc, htan, bcbar, hred, hrig⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_baseChange_comparison ι hcΦ rΦ ψ ψ' (f : B →+* B') hf t hOD hOD'
      (Rigidified.awayHom g) (Rigidified.awayHom (f g)) fg hge hc hcb hcΦf hc' hcb' hcΦf' (fun i => fl (γl i)) hγX

    obtain ⟨γ₂, hγ₂, hγ₂'⟩ := hbc.2.2.2.2.2
    have hγX' := CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt p (Rigidified.jS ι ψ' (Rigidified.awayHom (f g)))
      ((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))) hc' (fun i => bc (γ₂ i)) hγ₂'
    have hDsp' := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p (Rigidified.jS ι ψ' (Rigidified.awayHom (f g)))
      ((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))) (fun i => bc (γ₂ i)) hγX' hc').2
    have hj : fg.comp (Rigidified.jS ι ψ (Rigidified.awayHom g)) = Rigidified.jS ι ψ' (Rigidified.awayHom (f g)) := by
      rw [← hf]
      exact RingHom.ext fun a => (RingHom.congr_fun hge (ψ (ι a))).symm
    obtain ⟨L', hL'⟩ := CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong_of_comp_eq p (Rigidified.jS ι ψ (Rigidified.awayHom g))
      (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) fg hj ((t.XS (Rigidified.awayHom g)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom g)) hc) hDsp (((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) hc') hDsp' bc hbc L hL

    have hBg : IsNilpotent (p : (Rigidified.Baway g)) := by simpa using hB.map (Rigidified.awayHom g)
    have hBg' : IsNilpotent (p : (Rigidified.Baway (f g))) := by simpa using hB'.map (Rigidified.awayHom (f g))
    have hLL' := CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq p (Rigidified.jS ι ψ (Rigidified.awayHom g))
      (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) fg hj hBg hBg' ((t.XS (Rigidified.awayHom g)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom g)) hc) hDsp (((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) hc') hDsp' bc hbc L hL L' hL'

    have hz' := CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_map_nMap_of_isBaseChangeAlong ι hcΦ rΦ ψ ψ' (f : B →+* B') hf t hOD hOD'
      (Rigidified.awayHom g) (Rigidified.awayHom (f g)) fg hge hc hcb hcΦf hc' hcb' hcΦf' bc hbc L hL L' hL' hLL'
      bcbar hred hrig 1 z v hz
    exact ⟨f g, hg', hc', hcb', hcΦf', L', hL', _, hz'⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_le_of_map
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_le_of_map (solution)
