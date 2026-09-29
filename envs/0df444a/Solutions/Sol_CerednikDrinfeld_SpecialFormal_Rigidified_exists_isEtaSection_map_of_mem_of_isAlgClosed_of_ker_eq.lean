-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/089c3999-3b14-57ae-aee5-9fb202cd413b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_baseChangeEq_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace X2Fwd

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule CerednikDrinfeld.GradedCartierModuleData

theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] {p : ℕ} (h : IsNilpotent (p : S)) :
    IsHausdorff (Ideal.span {(p : S)}) S := by
  obtain ⟨N, hN⟩ := h
  refine ⟨fun x hx => ?_⟩
  have hxN := hx N
  rw [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.sub_mem,
    sub_zero, Submodule.mem_bot] at hxN
  exact hxN

theorem isBaseChangeAlong_congr {p : ℕ} [Fact p.Prime] {B S : Type} [CommRing B] [CommRing S]
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* S) (X : CerednikDrinfeld.FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    {Y₁ Y₂ : CerednikDrinfeld.FormalODModule p S} (e : Y₁ = Y₂)
    (h₁ : X.F.map φ = Y₁.F) (h₂ : X.F.map φ = Y₂.F)
    (hc₁ : IsCompl (Y₁.gradedPiece (φ.comp j) 0) (Y₁.gradedPiece (φ.comp j) 1))
    (hc₂ : IsCompl (Y₂.gradedPiece (φ.comp j) 0) (Y₂.gradedPiece (φ.comp j) 1))
    (H : IsBaseChangeAlong φ (X.toGradedCartierModuleData j hc) (Y₁.toGradedCartierModuleData (φ.comp j) hc₁)
      (baseChangeEq (Φ := X.F) (Ψ := Y₁.F) φ h₁)) :
    IsBaseChangeAlong φ (X.toGradedCartierModuleData j hc) (Y₂.toGradedCartierModuleData (φ.comp j) hc₂)
      (baseChangeEq (Φ := X.F) (Ψ := Y₂.F) φ h₂) := by
  subst e
  exact H

end X2Fwd

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule CerednikDrinfeld.GradedCartierModuleData X2Fwd in

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) (N : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)

    {L : Type} [Field L] [IsAlgClosed L] [Algebra ℤ_[p] L] (g : B →+* L)
    (hg : g.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] L)
    (x : PrimeSpectrum B) (hx : RingHom.ker g = x.asIdeal)
    (ht' : (t.map g).IsAdmissible ι (g.comp ψ)) :
    ∀ (x' : PrimeSpectrum L) (v : Fin 2 → ℚ_[p]), v ∈ N x →
      ∃ (f : L) (_ : f ∉ x'.asIdeal) (hc : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
        (hcb : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
        (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
        (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L'),
        ∃ z, (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L' hL' i z v := by
  intro x' v hv
  obtain ⟨f₀, hf₀, hc₁, hcb₁, hcΦ₁, L₁, hL₁, z₁, hz₁⟩ := (hN x v).mp hv
  refine ⟨1, (Ideal.ne_top_iff_one _).mp x'.isPrime.ne_top, ?_⟩

  have hgf : g f₀ ≠ 0 := by
    intro h0
    apply hf₀
    rw [← hx]
    exact (RingHom.mem_ker).mpr h0
  have hunit : IsUnit (((Rigidified.awayHom (1 : L)).comp g) f₀) := by
    rw [RingHom.comp_apply]; exact (isUnit_iff_ne_zero.mpr hgf).map _
  obtain ⟨hloc, hcomp⟩ : ∃ hloc : Rigidified.Baway f₀ →+* Rigidified.Baway (1 : L),
      hloc.comp (Rigidified.awayHom f₀) = (Rigidified.awayHom (1 : L)).comp g :=
    ⟨IsLocalization.Away.lift f₀ hunit, IsLocalization.Away.lift_comp f₀ hunit⟩

  refine (CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_iff_exists_isEtaSection_comp p ι hcΦ rΦ ψ t
    ht.2.2.1 g ht'.2.2.1 (Rigidified.awayHom (1 : L)) i v).mpr ?_
  rw [← hcomp]

  have hpB₀ : IsNilpotent (p : Rigidified.Baway f₀) := by
    have := hB.map (Rigidified.awayHom f₀); rwa [map_natCast] at this
  have hpS : IsNilpotent (p : Rigidified.Baway (1 : L)) := by
    have := hB.map (hloc.comp (Rigidified.awayHom f₀)); rwa [map_natCast] at this
  have hpSb : IsNilpotent (p : Rigidified.Baway (1 : L) ⧸ pIdeal p (Rigidified.Baway (1 : L))) := by
    have := hpS.map (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : L)))); rwa [map_natCast] at this

  have hc₂ : t.IsGradedS ι ψ (hloc.comp (Rigidified.awayHom f₀)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p (Rigidified.jS ι ψ (hloc.comp (Rigidified.awayHom f₀))) hpS (t.XS (hloc.comp (Rigidified.awayHom f₀)))
  have hcb₂ : t.IsGradedSbar ι ψ (hloc.comp (Rigidified.awayHom f₀)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p (Rigidified.jSbar ι ψ (hloc.comp (Rigidified.awayHom f₀))) hpSb (t.XbarS (hloc.comp (Rigidified.awayHom f₀)))
  have hcΦ₂ : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (hloc.comp (Rigidified.awayHom f₀)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p (Rigidified.jPhiS ι ψ (hloc.comp (Rigidified.awayHom f₀))) hpSb
      (Rigidified.PhibarS (Φ := Φ) ψ (hloc.comp (Rigidified.awayHom f₀)))

  have hXh : (t.XS (Rigidified.awayHom f₀)).F.map hloc = (t.XS (hloc.comp (Rigidified.awayHom f₀))).F :=
    MvFormalGroup.map_map' (Rigidified.awayHom f₀) hloc t.X.F
  have eY : (t.XS (Rigidified.awayHom f₀)).map hloc = t.XS (hloc.comp (Rigidified.awayHom f₀)) :=
    CerednikDrinfeld.FormalODModule.map_map (Rigidified.awayHom f₀) hloc t.X
  have hbcV : ∀ m, baseChangeEq (Φ := (t.XS (Rigidified.awayHom f₀)).F) (Ψ := (t.XS (hloc.comp (Rigidified.awayHom f₀))).F) hloc hXh
      (((t.XS (Rigidified.awayHom f₀)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) hc₁).verschiebung m) =
      ((t.XS (hloc.comp (Rigidified.awayHom f₀))).toGradedCartierModuleData (Rigidified.jS ι ψ (hloc.comp (Rigidified.awayHom f₀))) hc₂).verschiebung
        (baseChangeEq (Φ := (t.XS (Rigidified.awayHom f₀)).F) (Ψ := (t.XS (hloc.comp (Rigidified.awayHom f₀))).F) hloc hXh m) :=
    fun m => baseChangeEq_verschiebungInt hloc hXh m
  have hbcPi : ∀ m, baseChangeEq (Φ := (t.XS (Rigidified.awayHom f₀)).F) (Ψ := (t.XS (hloc.comp (Rigidified.awayHom f₀))).F) hloc hXh
      (((t.XS (Rigidified.awayHom f₀)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) hc₁).varpi m) =
      ((t.XS (hloc.comp (Rigidified.awayHom f₀))).toGradedCartierModuleData (Rigidified.jS ι ψ (hloc.comp (Rigidified.awayHom f₀))) hc₂).varpi
        (baseChangeEq (Φ := (t.XS (Rigidified.awayHom f₀)).F) (Ψ := (t.XS (hloc.comp (Rigidified.awayHom f₀))).F) hloc hXh m) :=
    fun m => baseChangeEq_endAct hloc hXh (φ := (t.XS (Rigidified.awayHom f₀)).varpiEnd) (ψ := (t.XS (hloc.comp (Rigidified.awayHom f₀))).varpiEnd)
      (fun k => (congrFun (Series.map_map (Rigidified.awayHom f₀) hloc t.X.varpi) k).symm) m

  obtain ⟨Sl, _, jl, φl, hφl, htf, Dl, hDl, fl, hfl, Ll, hLl, hcompL⟩ := hL₁.exists_lift
  obtain ⟨γl, hγl, hγ₁D⟩ := hfl.2.2.2.2.2
  have hγ₁ : (t.XS (Rigidified.awayHom f₀)).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) (fun k => fl (γl k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p
      (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) (t.XS (Rigidified.awayHom f₀)) hc₁ _ hγ₁D
  have hD₁ := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) (t.XS (Rigidified.awayHom f₀)) _ hγ₁ hc₁).2

  have hc₂' : IsCompl (((t.XS (Rigidified.awayHom f₀)).map hloc).gradedPiece (hloc.comp (Rigidified.jS ι ψ (Rigidified.awayHom f₀))) 0)
      (((t.XS (Rigidified.awayHom f₀)).map hloc).gradedPiece (hloc.comp (Rigidified.jS ι ψ (Rigidified.awayHom f₀))) 1) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpS _
  have hf' := CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange p
    (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) hloc (t.XS (Rigidified.awayHom f₀)) _ hγ₁ hc₁ hc₂'
  have hf : IsBaseChangeAlong hloc ((t.XS (Rigidified.awayHom f₀)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) hc₁)
      ((t.XS (hloc.comp (Rigidified.awayHom f₀))).toGradedCartierModuleData (Rigidified.jS ι ψ (hloc.comp (Rigidified.awayHom f₀))) hc₂)
      (baseChangeEq (Φ := (t.XS (Rigidified.awayHom f₀)).F) (Ψ := (t.XS (hloc.comp (Rigidified.awayHom f₀))).F) hloc hXh) :=
    isBaseChangeAlong_congr _ hloc _ hc₁ eY rfl hXh hc₂' hc₂ hf'

  obtain ⟨γ', -, hγ'⟩ := hf.2.2.2.2.2
  have hγ₂ : (t.XS (hloc.comp (Rigidified.awayHom f₀))).IsHomogeneousVBasis (Rigidified.jS ι ψ (hloc.comp (Rigidified.awayHom f₀))) (fun k => baseChangeEq (Φ := (t.XS (Rigidified.awayHom f₀)).F) (Ψ := (t.XS (hloc.comp (Rigidified.awayHom f₀))).F) hloc hXh (γ' k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p
      (Rigidified.jS ι ψ (hloc.comp (Rigidified.awayHom f₀))) (t.XS (hloc.comp (Rigidified.awayHom f₀))) hc₂ _ hγ'
  have hD₂ := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (hloc.comp (Rigidified.awayHom f₀))) (t.XS (hloc.comp (Rigidified.awayHom f₀))) _ hγ₂ hc₂).2
  obtain ⟨L₂, hL₂⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (hloc.comp (Rigidified.awayHom f₀))) (isHausdorff_of_isNilpotent hpS) (t.XS (hloc.comp (Rigidified.awayHom f₀))) _ hγ₂ hc₂

  have hLL := CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent p
    (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) hloc hpB₀ hpS _ hD₁ _ hD₂ _ hf L₁ hL₁ L₂ hL₂

  have key := CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_nMap_baseChangeEq_of_comp_eq ι hcΦ rΦ ψ t ht.2.2.1
    (Rigidified.awayHom f₀) hloc (hloc.comp (Rigidified.awayHom f₀)) rfl hc₁ hcb₁ hcΦ₁ hc₂ hcb₂ hcΦ₂ hXh _ rfl hbcV hbcPi L₁ hL₁ L₂ hL₂
    (fun m => hLL m) i z₁ v hz₁
  exact ⟨hc₂, hcb₂, hcΦ₂, L₂, hL₂, _, key⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq (solution)
