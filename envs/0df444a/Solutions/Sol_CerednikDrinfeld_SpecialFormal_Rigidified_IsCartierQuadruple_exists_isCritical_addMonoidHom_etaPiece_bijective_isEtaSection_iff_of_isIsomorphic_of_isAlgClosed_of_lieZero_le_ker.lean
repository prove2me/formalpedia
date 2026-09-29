-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/5388bbef-eb32-5e46-b8c3-8a2aa551cc81

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_zero_of_lieZero_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_coordinates_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isEtaSection_of_isEtaSection
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_eq_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.SpecialFormal.Rigidified

namespace F2aAux

variable {p : ℕ} [Fact p.Prime]

theorem latticeRel_add {S' : Type} [CommRing S'] {jS' : Zp2 p →+* S'} (E : GradedCartierModuleData p S' jS')
    (n : ℕ) (r : (Fin 2 → ℤ_[p]) →+ E.NMod) (z z' : E.NMod) (v v' : Fin 2 → ℚ_[p])
    (h : Rigidified.LatticeRel E n r z v) (h' : Rigidified.LatticeRel E n r z' v') :
    Rigidified.LatticeRel E n r (z + z') (v + v') := by
  obtain ⟨m, k, w, hv, hr⟩ := h
  obtain ⟨m', k', w', hv', hr'⟩ := h'
  refine ⟨m + m', k + k', (p ^ m') • w + (p ^ m) • w', ?_, ?_⟩
  · funext j
    have hvj := congr_fun hv j
    have hvj' := congr_fun hv' j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hvj hvj' ⊢
    rw [nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    rw [← hvj, ← hvj']
    ring
  · have e1 : p ^ (k + k') • (p ^ m' • r w) = p ^ (k + k' + n + (m + m')) • z := by
      rw [smul_smul, show p ^ (k + k') * p ^ m' = p ^ (k' + m') * p ^ k by ring, ← smul_smul, hr, smul_smul]
      congr 1; ring
    have e2 : p ^ (k + k') • (p ^ m • r w') = p ^ (k + k' + n + (m + m')) • z' := by
      rw [smul_smul, show p ^ (k + k') * p ^ m = p ^ (k + m) * p ^ k' by ring, ← smul_smul, hr', smul_smul]
      congr 1; ring
    rw [map_add, map_nsmul, map_nsmul, nsmul_add, e1, e2, ← nsmul_add]

theorem isEtaSection_add {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (i : Fin 2) (z z' : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (v v' : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v)
    (hz' : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z' v') :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i (z + z') (v + v') := by
  refine ⟨add_mem hz.1 hz'.1, ?_⟩
  have h := latticeRel_add _ _ _ _ _ _ _ hz.2 hz'.2
  rw [map_add, map_add, smul_add]
  exact h

theorem isEtaSection_zero {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (i : Fin 2) :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i 0 0 := by
  refine ⟨zero_mem _, 0, 0, 0, ?_, ?_⟩
  · funext j; simp
  · simp only [map_zero, smul_zero, nsmul_zero]

theorem crit_of_pi_eq_zero
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t : Rigidified p Φ κ) (ht : t.IsAdmissible ι ψ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ) (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (i : Fin 2) (hPi : (i = 0 ∧ ∀ s : Q.T₀, Q.Pi₀ s = 0) ∨ (i = 1 ∧ ∀ s : Q.T₁, Q.Pi₁ s = 0)) :
    ∀ m ∈ (t.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F,
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd m := by
  classical

  haveI hnt : Nontrivial (Rigidified.Baway (1 : κ)) := by
    have hM : Submonoid.powers (1 : κ) ≤ IsUnit.submonoid κ := by
      rw [Submonoid.powers_one]; exact bot_le
    exact (IsLocalization.atUnits (R := κ) (M := Submonoid.powers (1 : κ)) (S := Rigidified.Baway (1 : κ)) hM).injective.nontrivial
  haveI : CharP (Rigidified.Baway (1 : κ)) p :=
    charP_of_injective_algebraMap (algebraMap κ (Rigidified.Baway (1 : κ))).injective p
  obtain ⟨-, τ₀, τ₁, hT0, hT1, -⟩ := hQ
  have hLie : IsCompl (t.X.lieZero (structureMap ι ψ)) (t.X.lieOne (structureMap ι ψ)) := ht.1.1
  rcases hPi with ⟨rfl, h0⟩ | ⟨rfl, h1⟩
  ·
    have hle : t.X.lieZero (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi := by
      intro v hv
      rw [LinearMap.mem_ker]
      have h := hT0 (τ₀.symm ⟨v, hv⟩)
      rw [h0, map_zero, LinearEquiv.apply_symm_apply] at h
      simpa using h.symm
    have hcrit := CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_zero_of_lieZero_le_ker_lieVarpi p
      (structureMap ι ψ) t.X hLie hle (Rigidified.awayHom (1 : κ))
    intro m hm
    obtain ⟨g, hg⟩ := hcrit m (by simpa using hm)
    exact ⟨g, by rw [MvFormalGroup.CartierModule.verschiebungInt_apply_eq_verschiebung]; exact hg⟩
  ·
    have hle : t.X.lieOne (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi := by
      intro v hv
      rw [LinearMap.mem_ker]
      have h := hT1 (τ₁.symm ⟨v, hv⟩)
      rw [h1, map_zero, LinearEquiv.apply_symm_apply] at h
      simpa using h.symm
    have hcrit := CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_one_of_lieOne_le_ker_lieVarpi p
      (structureMap ι ψ) t.X hLie hle (Rigidified.awayHom (1 : κ))
    intro m hm
    obtain ⟨g, hg⟩ := hcrit m (by simpa using hm)
    exact ⟨g, by rw [MvFormalGroup.CartierModule.verschiebungInt_apply_eq_verschiebung]; exact hg⟩

end F2aAux

open F2aAux

namespace F2aAux

theorem isSpecialCartierModule_of_isCanonicalLMap {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] [Algebra ℤ_[p] S] (j : Zp2 p →+* S)
    (X : FormalODModule p S)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    (X.toGradedCartierModuleData j hc).IsSpecialCartierModule := by
  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : X.IsHomogeneousVBasis j (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf
  exact (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
end F2aAux

theorem main
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
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
    (hiso : Q.IsIsomorphic Q')
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hc' : t'.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb' : t'.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (L' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) (hL' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').IsCanonicalLMap L')
    (i : Fin 2)
    (hsets : ∀ v : Fin 2 → ℚ_[p], (∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i z v) ↔ (∃ z', t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i z' v)) :
    ∃ (θη : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
        (τ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).LieQuot →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').LieQuot),
        Function.Bijective θη ∧ Function.Injective τ ∧
        (∀ (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (m' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M) (hm : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0) ∈ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
            ((θη ⟨((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0), hm⟩ : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) =
              ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (m', 0) →
            τ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).vRange.mkQ m) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').vRange.mkQ m') ∧
        (∀ (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i) (v : Fin 2 → ℚ_[p]),
            t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) v ↔
              t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i ((θη z : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) v) := by
  classical

  have hκ : IsNilpotent ((p : ℕ) : κ) := ⟨1, by rw [pow_one]; exact CharP.cast_eq_zero κ p⟩
  haveI : Nontrivial (Rigidified.Baway (1 : κ)) := by
    have hM : Submonoid.powers (1 : κ) ≤ IsUnit.submonoid κ := by
      rw [Submonoid.powers_one]; exact bot_le
    exact (IsLocalization.atUnits (R := κ) (M := Submonoid.powers (1 : κ)) (S := Rigidified.Baway (1 : κ)) hM).injective.nontrivial
  haveI : CharP (Rigidified.Baway (1 : κ)) p :=
    charP_of_injective_algebraMap (algebraMap κ (Rigidified.Baway (1 : κ))).injective p
  have hS : IsNilpotent ((p : ℕ) : Rigidified.Baway (1 : κ)) := ⟨1, by rw [pow_one]; exact CharP.cast_eq_zero _ p⟩
  haveI : IsNoetherianRing (Rigidified.Baway (1 : κ)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (1 : κ)) _ inferInstance

  have C := CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ
    κ ψ hκ t ht hc hcb hcΦg L hL i
  have C' := CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ
    κ ψ hκ t' ht' hc' hcb' hcΦg L' hL' i
  have INJ : ∀ (v : Fin 2 → ℚ_[p]) (z z' : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod), t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i z v → t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i z' v → z = z' :=
    fun v z z' hz hz' => CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isEtaSection_of_isEtaSection p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ
      ψ t ht (Rigidified.awayHom (1 : κ)) hS hc hcb hcΦg L hL i v z z' hz hz'
  have INJ' : ∀ (v : Fin 2 → ℚ_[p]) (z z' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod), t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i z v → t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i z' v → z = z' :=
    fun v z z' hz hz' => CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isEtaSection_of_isEtaSection p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ
      ψ t' ht' (Rigidified.awayHom (1 : κ)) hS hc' hcb' hcΦg L' hL' i v z z' hz hz'

  have key : ∀ z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i, ∃ z' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod, ∃ v : Fin 2 → ℚ_[p],
      t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) v ∧ t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i z' v := by
    intro z
    obtain ⟨v, hv⟩ := C.1 (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) z.2
    obtain ⟨z', hz'⟩ := (hsets v).1 ⟨_, hv⟩
    exact ⟨z', v, hv, hz'⟩
  choose θf hθf using key
  have hco : ∀ (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i) (v : Fin 2 → ℚ_[p]),
      t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) v ↔ t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i (θf z) v := by
    intro z v
    obtain ⟨v₀, h1, h2⟩ := hθf z
    constructor
    · intro h
      have := C.2.2 _ _ _ h1 h
      subst this
      exact h2
    · intro h
      have := C'.2.2 _ _ _ h2 h
      subst this
      exact h1
  have hmem : ∀ z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i, θf z ∈ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i := by
    intro z
    obtain ⟨v₀, -, h2⟩ := hθf z
    exact h2.1
  have hadd : ∀ z₁ z₂ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i, θf (z₁ + z₂) = θf z₁ + θf z₂ := by
    intro z₁ z₂
    obtain ⟨v₁, h11, h12⟩ := hθf z₁
    obtain ⟨v₂, h21, h22⟩ := hθf z₂
    have hs : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i ((z₁ + z₂ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i) : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (v₁ + v₂) := by
      rw [AddSubgroup.coe_add]
      exact isEtaSection_add ι hcΦ rΦ ψ t hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i _ _ _ _ h11 h21
    have h3 := (hco _ _).1 hs
    have h4 := isEtaSection_add ι hcΦ rΦ ψ t' hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i _ _ _ _ h12 h22
    exact INJ' _ _ _ h3 h4
  let θη : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i :=
    AddMonoidHom.mk' (fun z => ⟨θf z, hmem z⟩) (fun z₁ z₂ => Subtype.ext (hadd z₁ z₂))
  have hθη : ∀ z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i, ((θη z : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) = θf z := fun _ => rfl

  obtain ⟨τ, hτi, hτ⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one
      p k ι Φ hcΦ rΦ ψ t t' ht ht' Q Q' hQ hQ' hiso hOD hOD' hc hcb hc' hcb' hcΦg L hL L' hL'
  refine ⟨θη, τ, ⟨?_, ?_⟩, hτi, ?_, ?_⟩
  ·
    intro z₁ z₂ h
    have h' : θf z₁ = θf z₂ := by rw [← hθη, ← hθη, h]
    obtain ⟨v₁, h11, h12⟩ := hθf z₁
    obtain ⟨v₂, h21, h22⟩ := hθf z₂
    rw [h'] at h12
    have hv : v₁ = v₂ := C'.2.2 _ _ _ h12 h22
    subst hv
    exact Subtype.ext (INJ _ _ _ h11 h21)
  ·
    intro z'
    obtain ⟨v, hv⟩ := C'.1 (z' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) z'.2
    obtain ⟨z, hz⟩ := (hsets v).2 ⟨_, hv⟩
    refine ⟨⟨z, hz.1⟩, Subtype.ext ?_⟩
    rw [hθη]
    exact INJ' _ _ _ ((hco ⟨z, hz.1⟩ v).1 hz) hv
  ·
    intro m m' hm h
    obtain ⟨v, hv⟩ := C.1 _ hm
    have h2 := (hco ⟨_, hm⟩ v).1 hv
    rw [← hθη, h] at h2
    exact hτ i m m' v hv h2
  ·
    intro z v
    rw [hθη]
    exact hco z v

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
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
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
    (hiso : Q.IsIsomorphic Q')
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hc' : t'.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb' : t'.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (L' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) (hL' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').IsCanonicalLMap L') :    ∃ i : Fin 2,
      (∀ m ∈ (t.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F,
          MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd m) ∧
      (∀ m ∈ (t'.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F,
          MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd m) ∧
      ∃ (θη : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
        (τ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).LieQuot →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').LieQuot),
        Function.Bijective θη ∧ Function.Injective τ ∧
        (∀ (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (m' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M) (hm : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0) ∈ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
            ((θη ⟨((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0), hm⟩ : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) =
              ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (m', 0) →
            τ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).vRange.mkQ m) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').vRange.mkQ m') ∧
        (∀ (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i) (v : Fin 2 → ℚ_[p]),
            t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) v ↔
              t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i ((θη z : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) v)  := by
  classical
  have hκ : IsNilpotent ((p : ℕ) : κ) := ⟨1, by rw [pow_one]; exact CharP.cast_eq_zero κ p⟩
  haveI : Nontrivial (Rigidified.Baway (1 : κ)) := by
    have hM : Submonoid.powers (1 : κ) ≤ IsUnit.submonoid κ := by
      rw [Submonoid.powers_one]; exact bot_le
    exact (IsLocalization.atUnits (R := κ) (M := Submonoid.powers (1 : κ)) (S := Rigidified.Baway (1 : κ)) hM).injective.nontrivial
  haveI : CharP (Rigidified.Baway (1 : κ)) p :=
    charP_of_injective_algebraMap (algebraMap κ (Rigidified.Baway (1 : κ))).injective p
  have hS : IsNilpotent ((p : ℕ) : Rigidified.Baway (1 : κ)) := ⟨1, by rw [pow_one]; exact CharP.cast_eq_zero _ p⟩
  let x₀ : PrimeSpectrum κ := ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨I⟩ := id hiso
  obtain ⟨τ₀, τ₁, -, -, hNu⟩ := hQ.2
  obtain ⟨τ₀', τ₁', -, -, hNu'⟩ := hQ'.2

  have hPi : ∃ i : Fin 2, (i = 0 ∧ ∀ s : Q.T₀, Q.Pi₀ s = 0) ∨ (i = 1 ∧ ∀ s : Q.T₁, Q.Pi₁ s = 0) := by
    by_cases h0 : ∀ s : Q.T₀, Q.Pi₀ s = 0
    · exact ⟨0, Or.inl ⟨rfl, h0⟩⟩
    · push_neg at h0
      obtain ⟨s₀, hs₀⟩ := h0
      refine ⟨1, Or.inr ⟨rfl, fun s => ?_⟩⟩
      have hrank : Module.finrank κ Q.T₁ = 1 := Module.Invertible.finrank_eq_one κ Q.T₁
      obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (Q.Pi₀ s₀) hs₀).mp hrank s
      have hp0 : (algebraMap ℤ_[p] κ) (p : ℤ_[p]) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero κ p
      rw [map_smul, Q.Pi₁_Pi₀, hp0, zero_smul, smul_zero]
  obtain ⟨i, hPi⟩ := hPi
  have hPi' : (i = 0 ∧ ∀ s : Q'.T₀, Q'.Pi₀ s = 0) ∨ (i = 1 ∧ ∀ s : Q'.T₁, Q'.Pi₁ s = 0) := by
    rcases hPi with ⟨hi, h⟩ | ⟨hi, h⟩
    · refine Or.inl ⟨hi, fun s => ?_⟩
      obtain ⟨s₁, rfl⟩ := I.τ₀.surjective s
      rw [← I.τ₁_Pi₀, h, map_zero]
    · refine Or.inr ⟨hi, fun s => ?_⟩
      obtain ⟨s₁, rfl⟩ := I.τ₁.surjective s
      rw [← I.τ₀_Pi₁, h, map_zero]

  have hD := F2aAux.isSpecialCartierModule_of_isCanonicalLMap (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (t.XS (Rigidified.awayHom (1 : κ))) hc L hL
  have hD' := F2aAux.isSpecialCartierModule_of_isCanonicalLMap (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (t'.XS (Rigidified.awayHom (1 : κ))) hc' L' hL'
  have hsets : ∀ v : Fin 2 → ℚ_[p], (∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i z v) ↔ (∃ z', t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i z' v) := by
    rcases hPi with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · obtain ⟨hc₁, hcb₁, hcΦ₁, L₁, hL₁, hN₁⟩ :=
        CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
          p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hκ t ht Q.N₀ (fun x v => (hNu ht.2.2.1 x).1 v)
      have hLL : L₁ = L :=
        CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hS _ hD L₁ L hL₁ hL
      subst hLL
      obtain ⟨hc₁', hcb₁', hcΦ₁', L₁', hL₁', hN₁'⟩ :=
        CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
          p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hκ t' ht' Q'.N₀ (fun x v => (hNu' ht'.2.2.1 x).1 v)
      have hLL' : L₁' = L' :=
        CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hS _ hD' L₁' L' hL₁' hL'
      subst hLL'
      intro v
      exact ((hN₁ x₀ v).symm.trans (by rw [I.N₀_eq x₀])).trans (hN₁' x₀ v)
    · obtain ⟨hc₁, hcb₁, hcΦ₁, L₁, hL₁, hN₁⟩ :=
        CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector
          p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hκ t ht Q.N₁ (fun x v => (hNu ht.2.2.1 x).2.1 v)
      have hLL : L₁ = L :=
        CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hS _ hD L₁ L hL₁ hL
      subst hLL
      obtain ⟨hc₁', hcb₁', hcΦ₁', L₁', hL₁', hN₁'⟩ :=
        CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector
          p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hκ t' ht' Q'.N₁ (fun x v => (hNu' ht'.2.2.1 x).2.1 v)
      have hLL' : L₁' = L' :=
        CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hS _ hD' L₁' L' hL₁' hL'
      subst hLL'
      intro v
      exact ((hN₁ x₀ v).symm.trans (by rw [I.N₁_eq x₀])).trans (hN₁' x₀ v)
  exact ⟨i, F2aAux.crit_of_pi_eq_zero p k ι Φ hcΦ rΦ ψ t ht Q hQ i hPi,
    F2aAux.crit_of_pi_eq_zero p k ι Φ hcΦ rΦ ψ t' ht' Q' hQ' i hPi',
    main p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ t t' ht ht' Q Q' hQ hQ' hiso hOD hOD' hc hcb hc' hcb' hcΦg L hL L' hL' i hsets⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker (solution)
