-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b36e1f45-8a2d-526c-89b9-ddf74f50c6e9

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_awayToLoc_tangent_eq_of_isEtaSection_of_isEtaSection
import Theorems.Thm_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_baseChangeEq_of_comp_eq
import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open MvFormalGroup MvFormalGroup.CartierModule

universe u

namespace StalkTransportKit

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime]

theorem isBaseChangeAlong'_of_eq {B S : Type} [CommRing B] [CommRing S] (j : Zp2 p →+* B)
    (g : B →+* S) (X : FormalODModule p B)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (X' : FormalODModule p S) (hX : X.map g = X') (j' : Zp2 p →+* S) (hj : g.comp j = j')
    (hc' : IsCompl (X'.gradedPiece j' 0) (X'.gradedPiece j' 1))
    (hF : X.F.map g = X'.F) :
    IsBaseChangeAlong' g (X.toGradedCartierModuleData j hc) (X'.toGradedCartierModuleData j' hc')
      (CartierModule.baseChangeEq g hF) := by
  subst hX; subst hj
  exact CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange p j g X γ hγ hc hc'

theorem natL_of_eq {B B' : Type} [CommRing B] [CommRing B'] (j : Zp2 p →+* B) (φ : B →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (j' : Zp2 p →+* B') (hj : φ.comp j = j')
    (D' : GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : IsBaseChangeAlong' φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by
  subst hj
  exact CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent p j φ hB hB' D hD D' hD' f hf L hL L' hL'

theorem mkQ_eq_toLieQuot_nMap {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B}
    {j' : Zp2 p →+* B'} (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) (m : D.M)
    (hm : D.vRange.mkQ m = D.toLieQuot z) :
    D'.vRange.mkQ (f m) = D'.toLieQuot (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [nMap_nMk]
  change D.vRange.mkQ m = D.vRange.mkQ a at hm
  change D'.vRange.mkQ (f m) = D'.vRange.mkQ (f a)
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hm ⊢
  obtain ⟨y, hy⟩ := (D.mem_vRange_iff _).mp hm
  exact (D'.mem_vRange_iff _).mpr ⟨f y, by rw [← hV, hy, map_sub]⟩

theorem tangent_eq_of_mkQ_eq {S : Type} [CommRing S] (X : FormalODModule p S) (jS : Zp2 p →+* S)
    (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1)) (m m' : CartierModule p X.F)
    (h : (X.toGradedCartierModuleData jS hc).vRange.mkQ m = (X.toGradedCartierModuleData jS hc).vRange.mkQ m') :
    tangent m = tangent m' := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨y, hy⟩ := ((X.toGradedCartierModuleData jS hc).mem_vRange_iff _).mp h
  have hy' : verschiebungInt y = m - m' := hy
  have : tangent (m - m') = 0 := by
    rw [← hy']
    exact tangent_verschiebungInt y
  rwa [map_sub, sub_eq_zero] at this

theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

theorem awayToLoc_comp_awayHom {B : Type} [CommRing B] (x : PrimeSpectrum B) (f : B) (hf : f ∉ x.asIdeal) :
    (Rigidified.awayToLoc x f hf).comp (Rigidified.awayHom f) = Rigidified.locHom x := by
  unfold Rigidified.awayToLoc
  exact IsLocalization.Away.lift_comp (x := f) _

end StalkTransportKit

namespace StalkTransport

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule StalkTransportKit

set_option maxHeartbeats 16000000 in

theorem transport {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
    (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod)
    (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
    {S' : Type} [CommRing S'] (g' : B →+* S') (h : Rigidified.Baway f →+* S') (hg' : h.comp (Rigidified.awayHom f) = g')
    (hS' : IsNilpotent ((p : ℕ) : S'))
    (hc' : t.IsGradedS ι ψ g') (hcb' : t.IsGradedSbar ι ψ g') (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g')
    (L' : ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').M →+ ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').NMod) (hL' : ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').IsCanonicalLMap L')
    (i : Fin 2) (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod) (v : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)
    (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M)
    (hm : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange.mkQ m = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).toLieQuot z) :
    ∃ (z' : ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').NMod) (m' : ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').M),
      t.IsEtaSection ι hcΦ rΦ ψ hOD g' hc' hcb' hcΦg' L' hL' i z' v ∧
      ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').vRange.mkQ m' = ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').toLieQuot z' ∧
      ∀ j : Fin 2, tangent m' j = h (tangent m j) := by
  classical
  subst hg'
  have hpf : IsNilpotent ((p : ℕ) : Rigidified.Baway f) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [← map_natCast (Rigidified.awayHom f) p, ← map_pow, hn, map_zero]⟩
  have hXm : (t.XS (Rigidified.awayHom f)).map h = t.XS (h.comp (Rigidified.awayHom f)) := by
    rw [FormalODModule.map_map]
  have hXh : (t.XS (Rigidified.awayHom f)).F.map h = (t.XS (h.comp (Rigidified.awayHom f))).F :=
    congrArg FormalODModule.F hXm
  have hj : h.comp (Rigidified.jS ι ψ (Rigidified.awayHom f)) = Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f)) := rfl

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS (Rigidified.awayHom f)).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom f))
      (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
      p _ _ hc _ hγf
  set bc : CartierModule p (t.XS (Rigidified.awayHom f)).F →+ CartierModule p (t.XS (h.comp (Rigidified.awayHom f))).F :=
    CartierModule.baseChangeEq h hXh with hbc
  have hbca : IsBaseChangeAlong' h ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc) ((t.XS (h.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f))) hc') bc :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm _ hj hc' hXh
  have hγ' : (t.XS (h.comp (Rigidified.awayHom f))).IsHomogeneousVBasis (Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f)))
      (fun i => bc (fl (γl i))) := by
    refine ⟨fun i => ?_, ?_⟩
    · exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc' i _).mp
        (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
    · rw [hbc]; exact isUnit_det_tangent_baseChangeEq _ hXh _ hγ.2
  have hDf := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hD' := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ' hc').2
  have hbcV := hbca.2.2.1
  have hbcPi := hbca.2.2.2.1
  have hLL' : ∀ y, L' (bc y) = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap ((t.XS (h.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f))) hc') bc hbcV hbcPi (L y) :=
    natL_of_eq _ _ hpf hS' _ hDf _ hj _ hD' bc hbca L hL L' hL'
  have hz' := CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_nMap_baseChangeEq_of_comp_eq
    ι hcΦ rΦ ψ t hOD (Rigidified.awayHom f) h (h.comp (Rigidified.awayHom f)) rfl
    hc hcb hcΦf hc' hcb' hcΦg' hXh bc hbc hbcV hbcPi L hL L' hL' hLL' i z v hz
  refine ⟨_, bc m, hz', mkQ_eq_toLieQuot_nMap ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc) ((t.XS (h.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f))) hc') bc hbcV hbcPi z m hm, fun j => ?_⟩
  rw [hbc, tangent_baseChangeEq]

end StalkTransport

namespace StalkTransport

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule StalkTransportKit

set_option maxHeartbeats 16000000 in

theorem exists_isCanonicalLMap_target {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (t : Rigidified p Φ B)
    (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod)
    (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
    {S' : Type} [CommRing S'] (g' : B →+* S') (h : Rigidified.Baway f →+* S') (hg' : h.comp (Rigidified.awayHom f) = g')
    (hS' : IsNilpotent ((p : ℕ) : S')) (hc' : t.IsGradedS ι ψ g') :
    ∃ L' : ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').M →+ ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').NMod, ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').IsCanonicalLMap L' := by
  classical
  subst hg'
  have hXm : (t.XS (Rigidified.awayHom f)).map h = t.XS (h.comp (Rigidified.awayHom f)) := by
    rw [FormalODModule.map_map]
  have hXh : (t.XS (Rigidified.awayHom f)).F.map h = (t.XS (h.comp (Rigidified.awayHom f))).F :=
    congrArg FormalODModule.F hXm
  have hj : h.comp (Rigidified.jS ι ψ (Rigidified.awayHom f)) = Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f)) := rfl
  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS (Rigidified.awayHom f)).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom f))
      (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
      p _ _ hc _ hγf
  set bc : CartierModule p (t.XS (Rigidified.awayHom f)).F →+ CartierModule p (t.XS (h.comp (Rigidified.awayHom f))).F :=
    CartierModule.baseChangeEq h hXh with hbc
  have hbca : IsBaseChangeAlong' h ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc) ((t.XS (h.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f))) hc') bc :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm _ hj hc' hXh
  have hγ' : (t.XS (h.comp (Rigidified.awayHom f))).IsHomogeneousVBasis (Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f)))
      (fun i => bc (fl (γl i))) := by
    refine ⟨fun i => ?_, ?_⟩
    · exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc' i _).mp
        (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
    · rw [hbc]; exact isUnit_det_tangent_baseChangeEq _ hXh _ hγ.2
  exact CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (h.comp (Rigidified.awayHom f))) (isHausdorff_of_isNilpotent hS') _ _ hγ' hc'

theorem latticeRel_add {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S}
    (E : GradedCartierModuleData p S jS) {n : ℕ} {r : (Fin 2 → ℤ_[p]) →+ E.NMod}
    {R R' : E.NMod} {v v' : Fin 2 → ℚ_[p]}
    (h : Rigidified.LatticeRel E n r R v) (h' : Rigidified.LatticeRel E n r R' v') :
    Rigidified.LatticeRel E n r (R + R') (v + v') := by
  obtain ⟨m, k, w, hw, hrel⟩ := h
  obtain ⟨m', k', w', hw', hrel'⟩ := h'
  refine ⟨m + m', k + k', (p ^ m') • w + (p ^ m) • w', ?_, ?_⟩
  · funext i
    have h1 := congrFun hw i
    have h2 := congrFun hw' i
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Pi.pow_apply]
    push_cast
    linear_combination (p : ℚ_[p]) ^ m' * h1 + (p : ℚ_[p]) ^ m * h2
  · have e1 : p ^ (k + k') • (p ^ m' • r w) = p ^ (k + k' + n + (m + m')) • R := by
      rw [smul_smul, show p ^ (k + k') * p ^ m' = p ^ (k' + m') * p ^ k by ring, ← smul_smul, hrel, smul_smul,
        ← pow_add]
      congr 1; ring
    have e2 : p ^ (k + k') • (p ^ m • r w') = p ^ (k + k' + n + (m + m')) • R' := by
      rw [smul_smul, show p ^ (k + k') * p ^ m = p ^ (k + m) * p ^ k' by ring, ← smul_smul, hrel', smul_smul,
        ← pow_add]
      congr 1; ring
    rw [map_add, map_nsmul, map_nsmul, nsmul_add, e1, e2, ← nsmul_add]

theorem isEtaSection_add {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (i : Fin 2) (z z' : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (v v' : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v)
    (hz' : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z' v') :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i (z + z') (v + v') := by
  unfold Rigidified.IsEtaSection at hz hz' ⊢
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h1', h2'⟩ := hz'
  refine ⟨AddSubgroup.add_mem _ h1 h1', ?_⟩
  rw [map_add, map_add, smul_add]
  exact latticeRel_add _ h2 h2'

theorem mk_eq_mk_of_locHom {B : Type} [CommRing B] (x : PrimeSpectrum B) (P : Submodule B (Fin 2 → B))
    (s s' : ↥P) (b b' : x.asIdeal.primeCompl)
    (h : ∀ i, Rigidified.locHom x ((s : Fin 2 → B) i) * Rigidified.locHom x (b' : B) =
      Rigidified.locHom x ((s' : Fin 2 → B) i) * Rigidified.locHom x (b : B)) :
    (LocalizedModule.mk s b : LocalizedModule x.asIdeal.primeCompl ↥P) = LocalizedModule.mk s' b' := by
  rw [LocalizedModule.mk_eq]
  have key : ∀ i, ∃ c : x.asIdeal.primeCompl,
      (c : B) * ((b' : B) * (s : Fin 2 → B) i) = (c : B) * ((b : B) * (s' : Fin 2 → B) i) := by
    intro i
    refine (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal)).mp ?_
    rw [map_mul, map_mul, mul_comm, h i, mul_comm]
  obtain ⟨c₀, hc₀⟩ := key 0
  obtain ⟨c₁, hc₁⟩ := key 1
  refine ⟨c₀ * c₁, ?_⟩
  apply Subtype.ext
  funext i
  change ((c₀ : B) * c₁) * ((b' : B) * (s : Fin 2 → B) i) = ((c₀ : B) * c₁) * ((b : B) * (s' : Fin 2 → B) i)
  fin_cases i
  · simp only [Fin.zero_eta]
    linear_combination (c₁ : B) * hc₀
  · simp only [Fin.mk_one]
    linear_combination (c₀ : B) * hc₁

theorem awayToLoc_comp_lift {B : Type} [CommRing B] (x : PrimeSpectrum B) (f g : B) (hf : f ∉ x.asIdeal) (hg : g ∉ x.asIdeal)
    (h : Rigidified.Baway f →+* Rigidified.Baway g) (hh : h.comp (Rigidified.awayHom f) = Rigidified.awayHom g) :
    (Rigidified.awayToLoc x g hg).comp h = Rigidified.awayToLoc x f hf := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc]
  show (Rigidified.awayToLoc x g hg).comp (h.comp (Rigidified.awayHom f)) = (Rigidified.awayToLoc x f hf).comp (Rigidified.awayHom f)
  rw [hh, awayToLoc_comp_awayHom, awayToLoc_comp_awayHom]

end StalkTransport

namespace StalkConstr

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule TensorProduct

section ZpExtension

variable {p : ℕ} [Fact p.Prime]

theorem padicInt_exists_nat_add (n : ℕ) (r : ℤ_[p]) : ∃ (k : ℕ) (r' : ℤ_[p]), r = k + (p : ℤ_[p]) ^ n * r' := by
  have hk : r - ((PadicInt.toZModPow n r).val : ℕ) ∈ RingHom.ker (PadicInt.toZModPow (p := p) n) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨r', hr'⟩ := hk
  exact ⟨(PadicInt.toZModPow n r).val, r', by rw [mul_comm, hr']; abel⟩

theorem exists_linearMap_tmul_eq {A N P : Type} [CommRing A] [Algebra ℤ_[p] A] [AddCommGroup N] [Module ℤ_[p] N]
    [AddCommGroup P] [Module A P] (hA : IsNilpotent ((p : ℕ) : A)) (G : N →+ P) :
    ∃ u : A ⊗[ℤ_[p]] N →ₗ[A] P, ∀ v : N, u ((1 : A) ⊗ₜ[ℤ_[p]] v) = G v := by
  letI modP : Module ℤ_[p] P := Module.compHom P (algebraMap ℤ_[p] A)
  have hsmul : ∀ (r : ℤ_[p]) (t : P), r • t = algebraMap ℤ_[p] A r • t := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[p] A P :=
    ⟨fun r a t => by rw [hsmul, Algebra.smul_def, mul_smul]⟩
  haveI : SMulCommClass ℤ_[p] A P :=
    ⟨fun r a t => by rw [hsmul, hsmul, smul_comm]⟩
  obtain ⟨n, hn⟩ := hA
  have hkill : ∀ t : P, ((p : ℕ) : A) ^ n • t = 0 := fun t => by rw [hn, zero_smul]

  have hG : ∀ (r : ℤ_[p]) (v : N), G (r • v) = r • G v := by
    intro r v
    obtain ⟨k, r', rfl⟩ := padicInt_exists_nat_add n r
    have h1 : ((k : ℤ_[p]) + (p : ℤ_[p]) ^ n * r') • v = k • v + (p ^ n) • (r' • v) := by
      rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    have lhs : G (((k : ℤ_[p]) + (p : ℤ_[p]) ^ n * r') • v) = k • G v := by
      rw [h1, map_add, map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul A (p ^ n), Nat.cast_pow, hkill, add_zero]
    have rhs : ((k : ℤ_[p]) + (p : ℤ_[p]) ^ n * r') • G v = k • G v := by
      rw [hsmul, map_add, map_natCast, map_mul, map_pow, map_natCast, add_smul, Nat.cast_smul_eq_nsmul, mul_smul,
        hkill, add_zero]
    rw [lhs, rhs]
  let G' : N →ₗ[ℤ_[p]] P := { toFun := G, map_add' := G.map_add, map_smul' := hG }
  let f : A →ₗ[A] N →ₗ[ℤ_[p]] P :=
    { toFun := fun a => a • G'
      map_add' := fun a b => add_smul a b G'
      map_smul' := fun c a => by rw [smul_eq_mul, RingHom.id_apply, mul_smul] }
  refine ⟨TensorProduct.AlgebraTensorModule.lift f, fun v => ?_⟩
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  show (1 : A) • G v = G v
  rw [one_smul]

end ZpExtension

section LieGerm

variable {p : ℕ} [Fact p.Prime]

theorem exists_smul_eq_map_of_mem_span {B : Type} [CommRing B] (f : B) (P : Submodule B (Fin 2 → B))
    (τ : Fin 2 → Rigidified.Baway f)
    (hτ : τ ∈ Submodule.span (Rigidified.Baway f)
      ((fun m : Fin 2 → B => fun i => Rigidified.awayHom f (m i)) '' (P : Set (Fin 2 → B)))) :
    ∃ (s : ↥P) (d : Submonoid.powers f), ∀ i, Rigidified.awayHom f ((s : Fin 2 → B) i) = Rigidified.awayHom f (d : B) * τ i := by
  induction hτ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨⟨m, hm⟩, 1, fun i => by simp⟩
  | zero => exact ⟨0, 1, fun i => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, d, hs⟩ := hx
    obtain ⟨s', d', hs'⟩ := hy
    refine ⟨(d' : B) • s + (d : B) • s', d * d', fun i => ?_⟩
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
      Submonoid.coe_mul, hs, hs']
    ring
  | smul c x _ hx =>
    obtain ⟨s, d, hs⟩ := hx
    obtain ⟨⟨b, e⟩, hc⟩ := IsLocalization.surj (Submonoid.powers f) c

    refine ⟨b • s, e * d, fun i => ?_⟩
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, Submonoid.coe_mul]
    rw [hs i]
    have hc' : Rigidified.awayHom f b = c * Rigidified.awayHom f (e : B) := hc.symm
    rw [hc']
    ring

end LieGerm

end StalkConstr

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0 : ∀ m ∈ Φ.lieZero (Rigidified.jbar ι), Φ.lieVarpi m = 0)
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
    (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
    (hfull₀ : ∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) (hfull₁ : ∀ x, LT.LatticeTree.IsFullLattice (N₁ x))
    (hle : ∀ x, N₀ x ≤ N₁ x) (hsmul : ∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x)
    (Pi₀ : ↥(t.X.lieZero (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) (Pi₁ : ↥(t.X.lieOne (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (hPi₀ : ∀ s : ↥(t.X.lieZero (structureMap ι ψ)), ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie)) :
    ∃ (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
      (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ))),
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieZero (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieOne (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)) := by
  classical

  have germData0 : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x),
      ∃ (s : ↥(t.X.lieZero (structureMap ι ψ))) (b : x.asIdeal.primeCompl)
        (f : B) (hf : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
        (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
        (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
        (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
        (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M),
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange.mkQ m = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
        ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
          Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i) := by
    intro x v hv
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN₀ x v).mp hv

    obtain ⟨hzeta, hzpiece⟩ := AddSubgroup.mem_inf.mp hz.1
    obtain ⟨⟨a, a'⟩, haa', hz_eq⟩ := AddSubgroup.mem_map.mp hzpiece
    obtain ⟨ha, -⟩ := AddSubgroup.mem_prod.mp haa'

    have hBf : IsNilpotent ((p : ℕ) : Rigidified.Baway f) := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, by rw [← map_natCast (Rigidified.awayHom f), ← map_pow, hn, map_zero]⟩
    have hτ : MvFormalGroup.CartierModule.tangent a ∈ (t.XS (Rigidified.awayHom f)).lieZero (Rigidified.jS ι ψ (Rigidified.awayHom f)) :=
      (CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p
        (Rigidified.jS ι ψ (Rigidified.awayHom f)) hBf (t.XS (Rigidified.awayHom f))).1 a ha
    have hspan := ((CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p (structureMap ι ψ)
      (Rigidified.awayHom f) t.X).2 ht.1.1).1
    obtain ⟨s, d, hsd⟩ := StalkConstr.exists_smul_eq_map_of_mem_span f _ _ (hspan.ge hτ)
    have hd : (d : B) ∉ x.asIdeal := by
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp d.2
      rw [← hn]
      exact fun h => hf (x.isPrime.mem_of_pow_mem _ h)
    refine ⟨s, ⟨(d : B), hd⟩, f, hf, hc, hcb, hcΦf, L, hL, z, hz, a, ?_, fun i => ?_⟩
    · show _ = CerednikDrinfeld.GradedCartierModuleData.toLieQuot _ z
      rw [← hz_eq]; rfl
    · have := congrArg (Rigidified.awayToLoc x f hf) (hsd i)
      rw [map_mul] at this
      unfold Rigidified.awayToLoc at this
      rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at this
      rw [this]
      rfl
  choose s0 b0 f0 hf0 hc0 hcb0 hcΦf0 L0 hL0 z0 hz0 m0 hm0 hs0 using germData0

  have hadd0 : ∀ (x : PrimeSpectrum B) (v w : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (hw : w ∈ N₀ x),
      (LocalizedModule.mk (s0 x (v + w) ((N₀ x).add_mem hv hw)) (b0 x (v + w) ((N₀ x).add_mem hv hw)) :
        FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ))) =
      LocalizedModule.mk (s0 x v hv) (b0 x v hv) + LocalizedModule.mk (s0 x w hw) (b0 x w hw) := by
    intro x v w hv hw
    set hvw : v + w ∈ N₀ x := (N₀ x).add_mem hv hw
    have hf12 : ((f0 x v hv) * (f0 x w hw)) ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim (hf0 x v hv) (hf0 x w hw)

    have hp12 : IsNilpotent ((p : ℕ) : Rigidified.Baway ((f0 x v hv) * (f0 x w hw))) := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, by rw [← map_natCast (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw))) p, ← map_pow, hn, map_zero]⟩
    have hpq12 : IsNilpotent ((p : ℕ) : Rigidified.Baway ((f0 x v hv) * (f0 x w hw)) ⧸ pIdeal p (Rigidified.Baway ((f0 x v hv) * (f0 x w hw)))) :=
      ⟨1, by
        rw [pow_one]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩
    have hc12 : t.IsGradedS ι ψ (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw))) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hp12 _
    have hcb12 : t.IsGradedSbar ι ψ (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw))) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq12 _
    have hcΦ12 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw))) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq12 _

    have hunit : IsUnit (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)) ((f0 x v hv) * (f0 x w hw))) := IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul] at hunit
    let h₁ : Rigidified.Baway (f0 x v hv) →+* Rigidified.Baway ((f0 x v hv) * (f0 x w hw)) :=
      IsLocalization.Away.lift (f0 x v hv) (isUnit_of_mul_isUnit_left hunit)
    have hh₁ : h₁.comp (Rigidified.awayHom (f0 x v hv)) = Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)) := IsLocalization.Away.lift_comp _ _
    let h₂ : Rigidified.Baway (f0 x w hw) →+* Rigidified.Baway ((f0 x v hv) * (f0 x w hw)) :=
      IsLocalization.Away.lift (f0 x w hw) (isUnit_of_mul_isUnit_right hunit)
    have hh₂ : h₂.comp (Rigidified.awayHom (f0 x w hw)) = Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)) := IsLocalization.Away.lift_comp _ _

    obtain ⟨L12, hL12⟩ := StalkTransport.exists_isCanonicalLMap_target ι ψ t (f0 x v hv) (hc0 x v hv) (L0 x v hv)
      (hL0 x v hv) (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw))) h₁ hh₁ hp12 hc12
    obtain ⟨Z₁, M₁, hZ₁, hM₁, hT₁⟩ := StalkTransport.transport ι hcΦ rΦ ψ hB t ht.2.2.1 (f0 x v hv) (hc0 x v hv)
      (hcb0 x v hv) (hcΦf0 x v hv) (L0 x v hv) (hL0 x v hv) (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw))) h₁ hh₁ hp12
      hc12 hcb12 hcΦ12 L12 hL12 0 (z0 x v hv) v (hz0 x v hv) (m0 x v hv) (hm0 x v hv)
    obtain ⟨Z₂, M₂, hZ₂, hM₂, hT₂⟩ := StalkTransport.transport ι hcΦ rΦ ψ hB t ht.2.2.1 (f0 x w hw) (hc0 x w hw)
      (hcb0 x w hw) (hcΦf0 x w hw) (L0 x w hw) (hL0 x w hw) (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw))) h₂ hh₂ hp12
      hc12 hcb12 hcΦ12 L12 hL12 0 (z0 x w hw) w (hz0 x w hw) (m0 x w hw) (hm0 x w hw)
    have hZ := StalkTransport.isEtaSection_add ι hcΦ rΦ ψ t ht.2.2.1 (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw))) hc12 hcb12 hcΦ12 L12 hL12
      0 Z₁ Z₂ v w hZ₁ hZ₂
    have hM : ((t.XS (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)))) hc12).vRange.mkQ (M₁ + M₂) =
        ((t.XS (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)))) hc12).u L12 hL12.isCartierLMap.map_verschiebung ⟨Z₁ + Z₂, (AddSubgroup.mem_inf.mp hZ.1).1⟩ := by
      show _ = ((t.XS (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom ((f0 x v hv) * (f0 x w hw)))) hc12).toLieQuot (Z₁ + Z₂)
      rw [map_add, map_add, hM₁, hM₂]

    have key := CerednikDrinfeld.SpecialFormal.Rigidified.awayToLoc_tangent_eq_of_isEtaSection_of_isEtaSection
      p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ ψ hB t ht x 0 (v + w) ((f0 x v hv) * (f0 x w hw)) hf12 hc12 hcb12 hcΦ12 L12 hL12 (Z₁ + Z₂) hZ (M₁ + M₂) hM
      (f0 x (v + w) hvw) (hf0 x (v + w) hvw) (hc0 x (v + w) hvw) (hcb0 x (v + w) hvw) (hcΦf0 x (v + w) hvw)
      (L0 x (v + w) hvw) (hL0 x (v + w) hvw) (z0 x (v + w) hvw) (hz0 x (v + w) hvw)
      (m0 x (v + w) hvw) (hm0 x (v + w) hvw)
    have hA₁ := StalkTransport.awayToLoc_comp_lift x (f0 x v hv) ((f0 x v hv) * (f0 x w hw)) (hf0 x v hv) hf12 h₁ hh₁
    have hA₂ := StalkTransport.awayToLoc_comp_lift x (f0 x w hw) ((f0 x v hv) * (f0 x w hw)) (hf0 x w hw) hf12 h₂ hh₂
    have hsum : ∀ i, Rigidified.awayToLoc x (f0 x (v + w) hvw) (hf0 x (v + w) hvw) (tangent (m0 x (v + w) hvw) i) =
        Rigidified.awayToLoc x (f0 x v hv) (hf0 x v hv) (tangent (m0 x v hv) i) +
        Rigidified.awayToLoc x (f0 x w hw) (hf0 x w hw) (tangent (m0 x w hw) i) := by
      intro i
      have hA₁' : ∀ y, Rigidified.awayToLoc x ((f0 x v hv) * (f0 x w hw)) hf12 (h₁ y) = Rigidified.awayToLoc x (f0 x v hv) (hf0 x v hv) y :=
        fun y => RingHom.congr_fun hA₁ y
      have hA₂' : ∀ y, Rigidified.awayToLoc x ((f0 x v hv) * (f0 x w hw)) hf12 (h₂ y) = Rigidified.awayToLoc x (f0 x w hw) (hf0 x w hw) y :=
        fun y => RingHom.congr_fun hA₂ y
      have htan : tangent (M₁ + M₂) i = h₁ (tangent (m0 x v hv) i) + h₂ (tangent (m0 x w hw) i) := by
        rw [← hT₁ i, ← hT₂ i, ← Pi.add_apply, ← map_add]
        rfl
      rw [← key i, htan, map_add, hA₁', hA₂']
    rw [LocalizedModule.mk_add_mk]
    apply StalkTransport.mk_eq_mk_of_locHom
    intro i
    rw [(hs0 x (v + w) hvw) i, hsum i]
    simp only [Submodule.coe_add, Submonoid.smul_def, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      map_add, map_mul, Submonoid.coe_mul, (hs0 x v hv) i, (hs0 x w hw) i]
    ring

  have hu0 : ∀ x : PrimeSpectrum B, ∃ u : FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩
        →ₗ[FormalOmega.locRing B x] FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)),
      ∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x),
        u ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk (s0 x v hv) (b0 x v hv) := by
    intro x
    have hA : IsNilpotent ((p : ℕ) : FormalOmega.locRing B x) := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, by rw [← map_natCast (algebraMap B (FormalOmega.locRing B x)), ← map_pow, hn, map_zero]⟩
    let G : ↥(N₀ x) →+ FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)) :=
      AddMonoidHom.mk' (fun v => LocalizedModule.mk (s0 x v.1 v.2) (b0 x v.1 v.2)) (fun v w => hadd0 x v.1 w.1 v.2 w.2)
    obtain ⟨u, hu⟩ := StalkConstr.exists_linearMap_tmul_eq hA G
    exact ⟨u, fun v hv => hu ⟨v, hv⟩⟩
  choose u0 hu0' using hu0

  have germData1 : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x),
      ∃ (s : ↥(t.X.lieOne (structureMap ι ψ))) (b : x.asIdeal.primeCompl)
        (f : B) (hf : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
        (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
        (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
        (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
        (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M),
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange.mkQ m = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
        ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
          Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i) := by
    intro x v hv
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN₁ x v).mp hv

    obtain ⟨hzeta, hzpiece⟩ := AddSubgroup.mem_inf.mp hz.1
    obtain ⟨⟨a, a'⟩, haa', hz_eq⟩ := AddSubgroup.mem_map.mp hzpiece
    obtain ⟨ha, -⟩ := AddSubgroup.mem_prod.mp haa'

    have hBf : IsNilpotent ((p : ℕ) : Rigidified.Baway f) := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, by rw [← map_natCast (Rigidified.awayHom f), ← map_pow, hn, map_zero]⟩
    have hτ : MvFormalGroup.CartierModule.tangent a ∈ (t.XS (Rigidified.awayHom f)).lieOne (Rigidified.jS ι ψ (Rigidified.awayHom f)) :=
      (CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p
        (Rigidified.jS ι ψ (Rigidified.awayHom f)) hBf (t.XS (Rigidified.awayHom f))).2 a ha
    have hspan := ((CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p (structureMap ι ψ)
      (Rigidified.awayHom f) t.X).2 ht.1.1).2
    obtain ⟨s, d, hsd⟩ := StalkConstr.exists_smul_eq_map_of_mem_span f _ _ (hspan.ge hτ)
    have hd : (d : B) ∉ x.asIdeal := by
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp d.2
      rw [← hn]
      exact fun h => hf (x.isPrime.mem_of_pow_mem _ h)
    refine ⟨s, ⟨(d : B), hd⟩, f, hf, hc, hcb, hcΦf, L, hL, z, hz, a, ?_, fun i => ?_⟩
    · show _ = CerednikDrinfeld.GradedCartierModuleData.toLieQuot _ z
      rw [← hz_eq]; rfl
    · have := congrArg (Rigidified.awayToLoc x f hf) (hsd i)
      rw [map_mul] at this
      unfold Rigidified.awayToLoc at this
      rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at this
      rw [this]
      rfl
  choose s1 b1 f1 hf1 hc1 hcb1 hcΦf1 L1 hL1 z1 hz1 m1 hm1 hs1 using germData1

  have hadd1 : ∀ (x : PrimeSpectrum B) (v w : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (hw : w ∈ N₁ x),
      (LocalizedModule.mk (s1 x (v + w) ((N₁ x).add_mem hv hw)) (b1 x (v + w) ((N₁ x).add_mem hv hw)) :
        FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ))) =
      LocalizedModule.mk (s1 x v hv) (b1 x v hv) + LocalizedModule.mk (s1 x w hw) (b1 x w hw) := by
    intro x v w hv hw
    set hvw : v + w ∈ N₁ x := (N₁ x).add_mem hv hw
    have hf12 : ((f1 x v hv) * (f1 x w hw)) ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim (hf1 x v hv) (hf1 x w hw)

    have hp12 : IsNilpotent ((p : ℕ) : Rigidified.Baway ((f1 x v hv) * (f1 x w hw))) := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, by rw [← map_natCast (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw))) p, ← map_pow, hn, map_zero]⟩
    have hpq12 : IsNilpotent ((p : ℕ) : Rigidified.Baway ((f1 x v hv) * (f1 x w hw)) ⧸ pIdeal p (Rigidified.Baway ((f1 x v hv) * (f1 x w hw)))) :=
      ⟨1, by
        rw [pow_one]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩
    have hc12 : t.IsGradedS ι ψ (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw))) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hp12 _
    have hcb12 : t.IsGradedSbar ι ψ (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw))) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq12 _
    have hcΦ12 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw))) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq12 _

    have hunit : IsUnit (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)) ((f1 x v hv) * (f1 x w hw))) := IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul] at hunit
    let h₁ : Rigidified.Baway (f1 x v hv) →+* Rigidified.Baway ((f1 x v hv) * (f1 x w hw)) :=
      IsLocalization.Away.lift (f1 x v hv) (isUnit_of_mul_isUnit_left hunit)
    have hh₁ : h₁.comp (Rigidified.awayHom (f1 x v hv)) = Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)) := IsLocalization.Away.lift_comp _ _
    let h₂ : Rigidified.Baway (f1 x w hw) →+* Rigidified.Baway ((f1 x v hv) * (f1 x w hw)) :=
      IsLocalization.Away.lift (f1 x w hw) (isUnit_of_mul_isUnit_right hunit)
    have hh₂ : h₂.comp (Rigidified.awayHom (f1 x w hw)) = Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)) := IsLocalization.Away.lift_comp _ _

    obtain ⟨L12, hL12⟩ := StalkTransport.exists_isCanonicalLMap_target ι ψ t (f1 x v hv) (hc1 x v hv) (L1 x v hv)
      (hL1 x v hv) (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw))) h₁ hh₁ hp12 hc12
    obtain ⟨Z₁, M₁, hZ₁, hM₁, hT₁⟩ := StalkTransport.transport ι hcΦ rΦ ψ hB t ht.2.2.1 (f1 x v hv) (hc1 x v hv)
      (hcb1 x v hv) (hcΦf1 x v hv) (L1 x v hv) (hL1 x v hv) (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw))) h₁ hh₁ hp12
      hc12 hcb12 hcΦ12 L12 hL12 1 (z1 x v hv) v (hz1 x v hv) (m1 x v hv) (hm1 x v hv)
    obtain ⟨Z₂, M₂, hZ₂, hM₂, hT₂⟩ := StalkTransport.transport ι hcΦ rΦ ψ hB t ht.2.2.1 (f1 x w hw) (hc1 x w hw)
      (hcb1 x w hw) (hcΦf1 x w hw) (L1 x w hw) (hL1 x w hw) (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw))) h₂ hh₂ hp12
      hc12 hcb12 hcΦ12 L12 hL12 1 (z1 x w hw) w (hz1 x w hw) (m1 x w hw) (hm1 x w hw)
    have hZ := StalkTransport.isEtaSection_add ι hcΦ rΦ ψ t ht.2.2.1 (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw))) hc12 hcb12 hcΦ12 L12 hL12
      1 Z₁ Z₂ v w hZ₁ hZ₂
    have hM : ((t.XS (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)))) hc12).vRange.mkQ (M₁ + M₂) =
        ((t.XS (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)))) hc12).u L12 hL12.isCartierLMap.map_verschiebung ⟨Z₁ + Z₂, (AddSubgroup.mem_inf.mp hZ.1).1⟩ := by
      show _ = ((t.XS (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom ((f1 x v hv) * (f1 x w hw)))) hc12).toLieQuot (Z₁ + Z₂)
      rw [map_add, map_add, hM₁, hM₂]

    have key := CerednikDrinfeld.SpecialFormal.Rigidified.awayToLoc_tangent_eq_of_isEtaSection_of_isEtaSection
      p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ ψ hB t ht x 1 (v + w) ((f1 x v hv) * (f1 x w hw)) hf12 hc12 hcb12 hcΦ12 L12 hL12 (Z₁ + Z₂) hZ (M₁ + M₂) hM
      (f1 x (v + w) hvw) (hf1 x (v + w) hvw) (hc1 x (v + w) hvw) (hcb1 x (v + w) hvw) (hcΦf1 x (v + w) hvw)
      (L1 x (v + w) hvw) (hL1 x (v + w) hvw) (z1 x (v + w) hvw) (hz1 x (v + w) hvw)
      (m1 x (v + w) hvw) (hm1 x (v + w) hvw)
    have hA₁ := StalkTransport.awayToLoc_comp_lift x (f1 x v hv) ((f1 x v hv) * (f1 x w hw)) (hf1 x v hv) hf12 h₁ hh₁
    have hA₂ := StalkTransport.awayToLoc_comp_lift x (f1 x w hw) ((f1 x v hv) * (f1 x w hw)) (hf1 x w hw) hf12 h₂ hh₂
    have hsum : ∀ i, Rigidified.awayToLoc x (f1 x (v + w) hvw) (hf1 x (v + w) hvw) (tangent (m1 x (v + w) hvw) i) =
        Rigidified.awayToLoc x (f1 x v hv) (hf1 x v hv) (tangent (m1 x v hv) i) +
        Rigidified.awayToLoc x (f1 x w hw) (hf1 x w hw) (tangent (m1 x w hw) i) := by
      intro i
      have hA₁' : ∀ y, Rigidified.awayToLoc x ((f1 x v hv) * (f1 x w hw)) hf12 (h₁ y) = Rigidified.awayToLoc x (f1 x v hv) (hf1 x v hv) y :=
        fun y => RingHom.congr_fun hA₁ y
      have hA₂' : ∀ y, Rigidified.awayToLoc x ((f1 x v hv) * (f1 x w hw)) hf12 (h₂ y) = Rigidified.awayToLoc x (f1 x w hw) (hf1 x w hw) y :=
        fun y => RingHom.congr_fun hA₂ y
      have htan : tangent (M₁ + M₂) i = h₁ (tangent (m1 x v hv) i) + h₂ (tangent (m1 x w hw) i) := by
        rw [← hT₁ i, ← hT₂ i, ← Pi.add_apply, ← map_add]
        rfl
      rw [← key i, htan, map_add, hA₁', hA₂']
    rw [LocalizedModule.mk_add_mk]
    apply StalkTransport.mk_eq_mk_of_locHom
    intro i
    rw [(hs1 x (v + w) hvw) i, hsum i]
    simp only [Submodule.coe_add, Submonoid.smul_def, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      map_add, map_mul, Submonoid.coe_mul, (hs1 x v hv) i, (hs1 x w hw) i]
    ring

  have hu1 : ∀ x : PrimeSpectrum B, ∃ u : FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩
        →ₗ[FormalOmega.locRing B x] FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)),
      ∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x),
        u ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk (s1 x v hv) (b1 x v hv) := by
    intro x
    have hA : IsNilpotent ((p : ℕ) : FormalOmega.locRing B x) := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, by rw [← map_natCast (algebraMap B (FormalOmega.locRing B x)), ← map_pow, hn, map_zero]⟩
    let G : ↥(N₁ x) →+ FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)) :=
      AddMonoidHom.mk' (fun v => LocalizedModule.mk (s1 x v.1 v.2) (b1 x v.1 v.2)) (fun v w => hadd1 x v.1 w.1 v.2 w.2)
    obtain ⟨u, hu⟩ := StalkConstr.exists_linearMap_tmul_eq hA G
    exact ⟨u, fun v hv => hu ⟨v, hv⟩⟩
  choose u1 hu1' using hu1

  refine ⟨u0, u1, ?_, ?_⟩
  · intro x v hv f hf hc hcb hcΦf L hL z hz
    obtain ⟨⟨a, a'⟩, rfl⟩ := ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMk_surjective z
    refine ⟨a, s0 x v hv, b0 x v hv, rfl, hu0' x v hv, fun i => ?_⟩
    rw [(hs0 x v hv) i]
    congr 1
    exact CerednikDrinfeld.SpecialFormal.Rigidified.awayToLoc_tangent_eq_of_isEtaSection_of_isEtaSection p ι Φ hΦ hΦ4 hcΦ rΦ
      hLΦ hrΦ ψ hB t ht x 0 v (f0 x v hv) (hf0 x v hv) (hc0 x v hv) (hcb0 x v hv) (hcΦf0 x v hv) (L0 x v hv) (hL0 x v hv)
      (z0 x v hv) (hz0 x v hv) (m0 x v hv) (hm0 x v hv) f hf hc hcb hcΦf L hL _ hz a rfl i
  · intro x v hv f hf hc hcb hcΦf L hL z hz
    obtain ⟨⟨a, a'⟩, rfl⟩ := ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMk_surjective z
    refine ⟨a, s1 x v hv, b1 x v hv, rfl, hu1' x v hv, fun i => ?_⟩
    rw [(hs1 x v hv) i]
    congr 1
    exact CerednikDrinfeld.SpecialFormal.Rigidified.awayToLoc_tangent_eq_of_isEtaSection_of_isEtaSection p ι Φ hΦ hΦ4 hcΦ rΦ
      hLΦ hrΦ ψ hB t ht x 1 v (f1 x v hv) (hf1 x v hv) (hc1 x v hv) (hcb1 x v hv) (hcΦf1 x v hv) (L1 x v hv) (hL1 x v hv)
      (z1 x v hv) (hz1 x v hv) (m1 x v hv) (hm1 x v hv) f hf hc hcb hcΦf L hL _ hz a rfl i

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ (solution)
