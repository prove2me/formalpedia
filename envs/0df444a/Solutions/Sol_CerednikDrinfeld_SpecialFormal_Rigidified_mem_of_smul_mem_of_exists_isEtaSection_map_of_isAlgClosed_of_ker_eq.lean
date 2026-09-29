-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c90e4227-ec94-535c-b237-bd51ab2bf357

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_baseChangeEq_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

universe u

namespace PDivAsm

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

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

theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

end PDivAsm

open PDivAsm CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule in

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
    ∀ (x' : PrimeSpectrum L) (v : Fin 2 → ℚ_[p]),
      algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N x →
      (∃ (f : L) (_ : f ∉ x'.asIdeal) (hc : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
        (hcb : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
        (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
        (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L'),
        ∃ z, (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L' hL' i z v) →
      v ∈ N x := by
  intro x' v hpv hfib
  classical
  obtain ⟨f', hf', hc', hcb', hcΦf', L', hL', z', hz'⟩ := hfib
  obtain ⟨f₀, hf₀, hc₀, hcb₀, hcΦf₀, L₀, hL₀, z₀, hz₀⟩ := (hN x _).1 hpv

  have hpL : IsNilpotent ((p : ℕ) : L) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [← map_natCast g p, ← map_pow, hn, map_zero]⟩
  have hgf₀ : IsUnit (g f₀) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hf₀
    rw [← hx]
    exact h0
  have hf'0 : f' ≠ 0 := fun h => hf' (h ▸ x'.asIdeal.zero_mem)

  obtain ⟨hc₁, hcb₁, hcΦ₁, L₁, hL₁, z₁, hz₁, ⟨hXh, hbcV, hbcPi, hz₁eq⟩, -⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
      p ι Φ hcΦ rΦ ψ hB t ht f₀ hc₀ hcb₀ hcΦf₀ L₀ hL₀ i z₀ _ hz₀ g hg hpL hgf₀ ht'

  obtain ⟨y, hy, hz₁y⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap
      p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ (g.comp ψ) hpL (t.map g) ht' i v 1 one_ne_zero hc₁ hcb₁ hcΦ₁ L₁ hL₁ z₁ hz₁
      f' hf'0 hc' hcb' hcΦf' L' hL' z' hz'

  obtain ⟨f₂, hf₂, hcD, L₂, hL₂, hXr, hrV, hrPi, z₂, hz₂m, hz₂e⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq
      p ι Φ ψ hB t ht i f₀ hc₀ L₀ hL₀ z₀ hz₀.1 g hg x hx hgf₀ ht' hc₁ L₁ hL₁ hXh hbcV hbcPi
      ⟨y, hy, by rw [← hz₁eq]; exact hz₁y⟩

  have hff : f₀ * f₂ ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim hf₀ hf₂
  have hp0 : IsNilpotent ((p : ℕ) : Rigidified.Baway (f₀ * f₂)) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [← map_natCast (Rigidified.awayHom (f₀ * f₂)) p, ← map_pow, hn, map_zero]⟩
  have hp1 : IsNilpotent ((p : ℕ) : Rigidified.Baway f₀) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [← map_natCast (Rigidified.awayHom f₀) p, ← map_pow, hn, map_zero]⟩
  have hpq : IsNilpotent ((p : ℕ) : Rigidified.Baway (f₀ * f₂) ⧸ pIdeal p (Rigidified.Baway (f₀ * f₂))) :=
    ⟨1, by
      rw [pow_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩
  have hcbD : t.IsGradedSbar ι ψ (Rigidified.awayHom (f₀ * f₂)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq _
  have hcΦD : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (f₀ * f₂)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq _
  set res : Rigidified.Baway f₀ →+* Rigidified.Baway (f₀ * f₂) :=
    (IsLocalization.Away.awayToAwayRight f₀ f₂ : Rigidified.Baway f₀ →+* Rigidified.Baway (f₀ * f₂)) with hresdef
  have hres : res.comp (Rigidified.awayHom f₀) = Rigidified.awayHom (f₀ * f₂) := by
    rw [hresdef]
    unfold IsLocalization.Away.awayToAwayRight
    exact IsLocalization.Away.lift_comp (x := f₀) _
  have hXm : (t.XS (Rigidified.awayHom f₀)).map res = t.XS (Rigidified.awayHom (f₀ * f₂)) := by
    rw [FormalODModule.map_map, hres]
  have hj : res.comp (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) = Rigidified.jS ι ψ (Rigidified.awayHom (f₀ * f₂)) := by
    rw [← hres]; rfl

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL₀.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS (Rigidified.awayHom f₀)).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom f₀))
      (fun k => fl (γl k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
      p _ _ hc₀ _ hγf
  have hbca : IsBaseChangeAlong' res ((t.XS (Rigidified.awayHom f₀)).toGradedCartierModuleData _ hc₀) ((t.XS (Rigidified.awayHom (f₀ * f₂))).toGradedCartierModuleData _ hcD)
      (CartierModule.baseChangeEq _ hXr) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc₀ _ hXm _ hj hcD hXr
  have hγD : (t.XS (Rigidified.awayHom (f₀ * f₂))).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom (f₀ * f₂)))
      (fun k => CartierModule.baseChangeEq _ hXr (fl (γl k))) := by
    refine ⟨fun k => ?_, isUnit_det_tangent_baseChangeEq _ hXr _ hγ.2⟩
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcD k _).mp
      (hbca.2.2.2.2.1 k _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc₀ k _).mpr (hγ.1 k)))
  have hD₀ := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc₀).2
  have hDD := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγD hcD).2
  have hLL : ∀ m, L₂ (CartierModule.baseChangeEq _ hXr m) =
      ((t.XS (Rigidified.awayHom f₀)).toGradedCartierModuleData _ hc₀).nMap ((t.XS (Rigidified.awayHom (f₀ * f₂))).toGradedCartierModuleData _ hcD)
        (CartierModule.baseChangeEq _ hXr) hbca.2.2.1 hbca.2.2.2.1 (L₀ m) :=
    natL_of_eq _ res hp1 hp0 _ hD₀ _ hj _ hDD _ hbca L₀ hL₀ L₂ hL₂
  have hzres := CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_nMap_baseChangeEq_of_comp_eq ι hcΦ rΦ ψ t ht.2.2.1
    (Rigidified.awayHom f₀) res (Rigidified.awayHom (f₀ * f₂)) hres hc₀ hcb₀ hcΦf₀ hcD hcbD hcΦD hXr
    (CartierModule.baseChangeEq _ hXr) rfl hbca.2.2.1 hbca.2.2.2.1 L₀ hL₀ L₂ hL₂ hLL i z₀ _ hz₀

  refine (hN x v).2 ⟨f₀ * f₂, hff, hcD, hcbD, hcΦD, L₂, hL₂, z₂, hz₂m, ?_⟩
  obtain ⟨-, hrel⟩ := hzres
  have hnm : ((t.XS (Rigidified.awayHom f₀)).toGradedCartierModuleData _ hc₀).nMap ((t.XS (Rigidified.awayHom (f₀ * f₂))).toGradedCartierModuleData _ hcD)
        (CartierModule.baseChangeEq _ hXr) hbca.2.2.1 hbca.2.2.2.1 z₀ = p • z₂ := by
    rw [hz₂e]
  rw [hnm, map_nsmul, map_nsmul] at hrel
  obtain ⟨m, k, w, hw, hr⟩ := hrel
  refine ⟨m + 1, k, w, ?_, ?_⟩
  · rw [← hw, map_natCast, pow_succ, mul_smul, smul_comm ((p : ℚ_[p]) ^ (i : ℕ)) (p : ℚ_[p]) v]
  · rw [hr, smul_smul, ← pow_succ, show k + t.n + (m + 1) = k + t.n + m + 1 by omega]

end S_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq (solution)
