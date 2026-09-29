-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_add_of_isAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ec94a54c-0f6d-5515-9b0a-2617d6e51b4c

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_baseChangeEq_of_comp_eq
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

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible.CerednikDrinfeld CerednikDrinfeld.SpecialFormal P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible.CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega"

open scoped PadicInt Padic

universe u

namespace APLUSAsm

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible.CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule"

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

end APLUSAsm

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange Zp2 FormalODModule FormalODModule.map_map FormalODModule.IsODHom SpecialFormal.Rigidified FormalODModule.F GradedCartierModuleData FormalODModule.mem_toGradedCartierModuleData_piece_iff FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData GradedCartierModuleData.IsCanonicalLMap FormalODModule.isSpecialCartierModule_toGradedCartierModuleData FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData SpecialFormal.Rigidified.isEtaSection_nMap_baseChangeEq_of_comp_eq"
namespace SpecialFormal
p2m_export "CerednikDrinfeld.SpecialFormal" "pIdeal Rigidified Rigidified.isEtaSection_nMap_baseChangeEq_of_comp_eq Rigidified.jbar Rigidified.jS Rigidified.IsGradedPhiS Rigidified.Baway Rigidified.awayHom"
namespace Rigidified
p2m_export "CerednikDrinfeld.SpecialFormal.Rigidified" "Xbar Φbar IsAdmissible map n ρ X isEtaSection_nMap_baseChangeEq_of_comp_eq jbar XS jS IsGradedS IsGradedSbar IsGradedPhiS LatticeRel IsEtaSection Baway awayHom"
p2m_open "CerednikDrinfeld.SpecialFormal.Rigidified CerednikDrinfeld.SpecialFormal CerednikDrinfeld"

theorem QXA_LatticeRel_add {p : ℕ} [Fact p.Prime] {S' : Type} [CommRing S'] {jS' : Zp2 p →+* S'}
    {E : GradedCartierModuleData p S' jS'} {n : ℕ} {r : (Fin 2 → ℤ_[p]) →+ E.NMod} {zbar zbar' : E.NMod}
    {v v' : Fin 2 → ℚ_[p]} (h : LatticeRel E n r zbar v) (h' : LatticeRel E n r zbar' v') :
    LatticeRel E n r (zbar + zbar') (v + v') := by
  obtain ⟨m, k, w, hv, hr⟩ := h
  obtain ⟨m', k', w', hv', hr'⟩ := h'
  refine ⟨m + m', k + k', (p : ℕ) ^ m' • w + (p : ℕ) ^ m • w', ?_, ?_⟩
  ·
    have e : (p : ℚ_[p]) ^ (m + m') • (v + v') =
        (p : ℚ_[p]) ^ m' • ((p : ℚ_[p]) ^ m • v) + (p : ℚ_[p]) ^ m • ((p : ℚ_[p]) ^ m' • v') := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm m' m]
    rw [e, hv, hv']
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [nsmul_eq_mul, Nat.cast_pow, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast]
  · rw [map_add, map_nsmul, map_nsmul, nsmul_add]
    have e1 : p ^ (k + k') • (p ^ m' • r w) = p ^ (k' + m') • (p ^ k • r w) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    have e2 : p ^ (k + k') • (p ^ m • r w') = p ^ (k + m) • (p ^ k' • r w') := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [e1, e2, hr, hr', smul_smul, smul_smul, nsmul_add]
    congr 1 <;> (congr 1; ring)

theorem QXA_IsEtaSection_add {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) {S : Type} [CommRing S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).IsCanonicalLMap L) (i : Fin 2)
    {z z' : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod} {v v' : Fin 2 → ℚ_[p]}
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v)
    (hz' : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z' v') :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i (z + z') (v + v') := by
  refine ⟨add_mem hz.1 hz'.1, ?_⟩
  rw [map_add, map_add, smul_add]
  exact QXA_LatticeRel_add hz.2 hz'.2

end CerednikDrinfeld.SpecialFormal.Rigidified

set_option maxHeartbeats 3200000 in
open APLUSAsm CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
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
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∀ (x : PrimeSpectrum B) (i : Fin 2) (v v' : Fin 2 → ℚ_[p]),
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v) →
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v') →
      ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
        (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
        (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z (v + v') := by
  intro x i v v' ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ ⟨f', hf', hc', hcb', hcΦf', L', hL', z', hz'⟩
  classical
  have hff : f * f' ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim hf hf'

  have hp0 : IsNilpotent ((p : ℕ) : Rigidified.Baway (f * f')) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [← map_natCast (Rigidified.awayHom (f * f')) p, ← map_pow, hn, map_zero]⟩
  have hpq : IsNilpotent ((p : ℕ) : Rigidified.Baway (f * f') ⧸ pIdeal p (Rigidified.Baway (f * f'))) :=
    ⟨1, by
      rw [pow_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩

  have hc₀ : t.IsGradedS ι ψ (Rigidified.awayHom (f * f')) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hp0 _
  have hcb₀ : t.IsGradedSbar ι ψ (Rigidified.awayHom (f * f')) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq _
  have hcΦ₀ : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (f * f')) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq _

  have prep : ∀ (f₁ : B) (h : Rigidified.Baway f₁ →+* Rigidified.Baway (f * f'))
      (hh : h.comp (Rigidified.awayHom f₁) = Rigidified.awayHom (f * f'))
      (hc₁ : t.IsGradedS ι ψ (Rigidified.awayHom f₁))
      (L₁ : _) (hL₁ : ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).IsCanonicalLMap L₁),
      ∃ (hXh : (t.XS (Rigidified.awayHom f₁)).F.map h = (t.XS (Rigidified.awayHom (f * f'))).F)
        (bc : CartierModule p (t.XS (Rigidified.awayHom f₁)).F →+ CartierModule p (t.XS (Rigidified.awayHom (f * f'))).F)
        (hbc : bc = CartierModule.baseChangeEq _ hXh)
        (hbca : IsBaseChangeAlong' h
          ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁)
          ((t.XS (Rigidified.awayHom (f * f'))).toGradedCartierModuleData _ hc₀) bc),
        ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).IsSpecialCartierModule ∧
        ((t.XS (Rigidified.awayHom (f * f'))).toGradedCartierModuleData _ hc₀).IsSpecialCartierModule ∧
        ∃ L₀, ((t.XS (Rigidified.awayHom (f * f'))).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀ := by
    intro f₁ h hh hc₁ L₁ hL₁
    have hXm : (t.XS (Rigidified.awayHom f₁)).map h = t.XS (Rigidified.awayHom (f * f')) := by
      rw [FormalODModule.map_map, hh]
    have hXh : (t.XS (Rigidified.awayHom f₁)).F.map h = (t.XS (Rigidified.awayHom (f * f'))).F :=
      congrArg FormalODModule.F hXm
    have hj : h.comp (Rigidified.jS ι ψ (Rigidified.awayHom f₁)) = Rigidified.jS ι ψ (Rigidified.awayHom (f * f')) := by
      rw [← hh]; rfl
    obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL₁.exists_lift
    obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
    have hγ : (t.XS (Rigidified.awayHom f₁)).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom f₁))
        (fun i => fl (γl i)) :=
      CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
        p _ _ hc₁ _ hγf
    refine ⟨hXh, CartierModule.baseChangeEq _ hXh, rfl, ?_⟩
    have hbca : IsBaseChangeAlong' h
        ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁)
        ((t.XS (Rigidified.awayHom (f * f'))).toGradedCartierModuleData _ hc₀) (CartierModule.baseChangeEq _ hXh) :=
      isBaseChangeAlong'_of_eq _ _ _ _ hγ hc₁ _ hXm _ hj hc₀ hXh
    have hγ₀ : (t.XS (Rigidified.awayHom (f * f'))).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom (f * f')))
        (fun i => CartierModule.baseChangeEq _ hXh (fl (γl i))) := by
      refine ⟨fun i => ?_, isUnit_det_tangent_baseChangeEq _ hXh _ hγ.2⟩
      exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc₀ i _).mp
        (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc₁ i _).mpr (hγ.1 i)))
    exact ⟨hbca,
      (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc₁).2,
      (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ₀ hc₀).2,
      CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
        (Rigidified.jS ι ψ (Rigidified.awayHom (f * f'))) (isHausdorff_of_isNilpotent hp0) _ _ hγ₀ hc₀⟩

  have hh₁ : (IsLocalization.Away.awayToAwayRight (P := Rigidified.Baway (f * f')) f f' :
      Rigidified.Baway f →+* Rigidified.Baway (f * f')).comp (Rigidified.awayHom f) = Rigidified.awayHom (f * f') := by
    unfold IsLocalization.Away.awayToAwayRight
    exact IsLocalization.Away.lift_comp (x := f) _
  have hh₂ : (IsLocalization.Away.awayToAwayLeft (P := Rigidified.Baway (f * f')) f' f :
      Rigidified.Baway f' →+* Rigidified.Baway (f * f')).comp (Rigidified.awayHom f') = Rigidified.awayHom (f * f') := by
    unfold IsLocalization.Away.awayToAwayLeft
    exact IsLocalization.Away.lift_comp (x := f') _

  obtain ⟨-, -, -, -, -, -, L₀, hL₀⟩ := prep f _ hh₁ hc L hL

  have step : ∀ (f₁ : B) (h : Rigidified.Baway f₁ →+* Rigidified.Baway (f * f'))
      (hh : h.comp (Rigidified.awayHom f₁) = Rigidified.awayHom (f * f'))
      (hc₁ : t.IsGradedS ι ψ (Rigidified.awayHom f₁))
      (hcb₁ : t.IsGradedSbar ι ψ (Rigidified.awayHom f₁))
      (hcΦf₁ : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f₁))
      (L₁ : _) (hL₁ : ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).IsCanonicalLMap L₁)
      (w : Fin 2 → ℚ_[p])
      (z₁ : _) (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f₁) hc₁ hcb₁ hcΦf₁ L₁ hL₁ i z₁ w),
      ∃ z₀, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (f * f')) hc₀ hcb₀ hcΦ₀ L₀ hL₀ i z₀ w := by
    intro f₁ h hh hc₁ hcb₁ hcΦf₁ L₁ hL₁ w z₁ hz₁
    have hp1 : IsNilpotent ((p : ℕ) : Rigidified.Baway f₁) := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, by rw [← map_natCast (Rigidified.awayHom f₁) p, ← map_pow, hn, map_zero]⟩
    have hj : h.comp (Rigidified.jS ι ψ (Rigidified.awayHom f₁)) = Rigidified.jS ι ψ (Rigidified.awayHom (f * f')) := by
      rw [← hh]; rfl
    obtain ⟨hXh, bc, hbc, hbca, hD₁, hD₀, -⟩ := prep f₁ h hh hc₁ L₁ hL₁
    have hbcV := hbca.2.2.1
    have hbcPi := hbca.2.2.2.1
    have hLL₀ : ∀ y, L₀ (bc y) =
        ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).nMap
          ((t.XS (Rigidified.awayHom (f * f'))).toGradedCartierModuleData _ hc₀) bc hbcV hbcPi (L₁ y) :=
      natL_of_eq _ _ hp1 hp0 _ hD₁ _ hj _ hD₀ bc hbca L₁ hL₁ L₀ hL₀
    exact ⟨_, CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_nMap_baseChangeEq_of_comp_eq
      ι hcΦ rΦ ψ t ht.2.2.1 (Rigidified.awayHom f₁) h (Rigidified.awayHom (f * f')) hh
      hc₁ hcb₁ hcΦf₁ hc₀ hcb₀ hcΦ₀ hXh bc hbc hbcV hbcPi L₁ hL₁ L₀ hL₀ hLL₀ i z₁ w hz₁⟩
  obtain ⟨z₀, hz₀⟩ := step f _ hh₁ hc hcb hcΦf L hL v z hz
  obtain ⟨z₀', hz₀'⟩ := step f' _ hh₂ hc' hcb' hcΦf' L' hL' v' z' hz'
  exact ⟨f * f', hff, hc₀, hcb₀, hcΦ₀, L₀, hL₀, z₀ + z₀',
    CerednikDrinfeld.SpecialFormal.Rigidified.QXA_IsEtaSection_add ι hcΦ rΦ ψ t ht.2.2.1 _ hc₀ hcb₀ hcΦ₀ L₀ hL₀ i hz₀ hz₀'⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible (solution)
