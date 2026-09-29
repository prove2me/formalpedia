-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/181d0bbc-73f8-584d-ae3c-ed0ce962dcf2

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
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_u_nMap_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_eq_of_mkQ_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_localizedModule_mk_eq_of_coord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_u_baseChange
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

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
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (σ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (σ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q σ₀ σ₁)
    (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (σ₀' : Q'.T₀ ≃ₗ[B'] ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ')))
    (σ₁' : Q'.T₁ ≃ₗ[B'] ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ')))
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadrupleVia ι hcΦ rΦ ψ' Q' σ₀' σ₁')
    (τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀) (τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁)
    (hτ : (Submodule.span B' (Set.range τ₀) = ⊤) ∧ (Submodule.span B' (Set.range τ₁) = ⊤) ∧
      (∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) ∧ (∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s)))
    (hτσ : (∀ (s : Q.T₀) (i : Fin 2), ((σ₀' (τ₀ s) : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i)) ∧
      (∀ (s : Q.T₁) (i : Fin 2), ((σ₁' (τ₁ s) : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i))) :
    (∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Q'.N₀ x')
    (tt : Q.T₀) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₀ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Q'.u₀ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Q'.N₀ x'))) =
      LocalizedModule.mk (τ₀ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)) ∧
    (∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Q'.N₁ x')
    (tt : Q.T₁) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₁ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Q'.u₁ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Q'.N₁ x'))) =
      LocalizedModule.mk (τ₁ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)) := by
  obtain ⟨hOD, hT0, hT1, hrest⟩ := hQ
  obtain ⟨hOD', hT0', hT1', hrest'⟩ := hQ'
  obtain ⟨hs0, hs1, hP0, hP1⟩ := hτ
  obtain ⟨hσ0, hσ1⟩ := hτσ
  constructor
  · intro x' v hv hv' tt s hs hfrac
    obtain ⟨hN0, -, hu0, -⟩ := hrest hOD (DrinfeldDatum.pointUnder f x')
    obtain ⟨g, hg, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN0 v).1 hv
    obtain ⟨m, sQ, b, hmz, hub, hσb⟩ := hu0 v hv g hg hc hcb hcΦf L hL z hz
    obtain ⟨-, -, hu0', -⟩ := hrest' hOD' x'

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

    obtain ⟨-, hmq⟩ := CerednikDrinfeld.GradedCartierModuleData.u_nMap_of_comp_eq p ((t.XS (Rigidified.awayHom g)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom g)) hc) (((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) hc') bc hbc.2.2.1 hbc.2.2.2.1
      L hL.isCartierLMap.map_verschiebung L' hL'.isCartierLMap.map_verschiebung hLL' z (AddSubgroup.mem_inf.mp hz.1).1
    obtain ⟨m', s', b', hmz', hub', hσb'⟩ := hu0' v hv' (f g) hg' hc' hcb' hcΦf' L' hL' _ hz'
    have htm : MvFormalGroup.CartierModule.tangent m' = MvFormalGroup.CartierModule.tangent (bc m) :=
      CerednikDrinfeld.FormalODModule.tangent_eq_of_mkQ_eq p (Rigidified.jS ι ψ' (Rigidified.awayHom (f g)))
        ((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))) hc' m' (bc m)
        (hmz'.trans (hmq m (AddSubgroup.mem_inf.mp hz'.1).1 hmz).symm)
    have hw : ∀ i, MvFormalGroup.CartierModule.tangent m' i = fg (MvFormalGroup.CartierModule.tangent m i) :=
      fun i => by rw [htm]; exact htan m i
    rw [hub']
    exact CerednikDrinfeld.SpecialFormal.Rigidified.localizedModule_mk_eq_of_coord f (t.X.lieZero (structureMap ι ψ)) ((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))
      Q.T₀ Q'.T₀ σ₀ σ₀' τ₀ hσ0 x' g hg hg' fg hfg tt sQ s hs b (hfrac.symm.trans hub)
      (MvFormalGroup.CartierModule.tangent m) hσb s' b' (MvFormalGroup.CartierModule.tangent m') hσb' hw
  · intro x' v hv hv' tt s hs hfrac
    obtain ⟨-, hN1, -, hu1⟩ := hrest hOD (DrinfeldDatum.pointUnder f x')
    obtain ⟨g, hg, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN1 v).1 hv
    obtain ⟨m, sQ, b, hmz, hub, hσb⟩ := hu1 v hv g hg hc hcb hcΦf L hL z hz
    obtain ⟨-, -, -, hu1'⟩ := hrest' hOD' x'

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

    obtain ⟨-, hmq⟩ := CerednikDrinfeld.GradedCartierModuleData.u_nMap_of_comp_eq p ((t.XS (Rigidified.awayHom g)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom g)) hc) (((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (f g))) hc') bc hbc.2.2.1 hbc.2.2.2.1
      L hL.isCartierLMap.map_verschiebung L' hL'.isCartierLMap.map_verschiebung hLL' z (AddSubgroup.mem_inf.mp hz.1).1
    obtain ⟨m', s', b', hmz', hub', hσb'⟩ := hu1' v hv' (f g) hg' hc' hcb' hcΦf' L' hL' _ hz'
    have htm : MvFormalGroup.CartierModule.tangent m' = MvFormalGroup.CartierModule.tangent (bc m) :=
      CerednikDrinfeld.FormalODModule.tangent_eq_of_mkQ_eq p (Rigidified.jS ι ψ' (Rigidified.awayHom (f g)))
        ((t.map (f : B →+* B')).XS (Rigidified.awayHom (f g))) hc' m' (bc m)
        (hmz'.trans (hmq m (AddSubgroup.mem_inf.mp hz'.1).1 hmz).symm)
    have hw : ∀ i, MvFormalGroup.CartierModule.tangent m' i = fg (MvFormalGroup.CartierModule.tangent m i) :=
      fun i => by rw [htm]; exact htan m i
    rw [hub']
    exact CerednikDrinfeld.SpecialFormal.Rigidified.localizedModule_mk_eq_of_coord f (t.X.lieOne (structureMap ι ψ)) ((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))
      Q.T₁ Q'.T₁ σ₁ σ₁' τ₁ hσ1 x' g hg hg' fg hfg tt sQ s hs b (hfrac.symm.trans hub)
      (MvFormalGroup.CartierModule.tangent m) hσb s' b' (MvFormalGroup.CartierModule.tangent m') hσb' hw

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_u_baseChange
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_u_baseChange (solution)
