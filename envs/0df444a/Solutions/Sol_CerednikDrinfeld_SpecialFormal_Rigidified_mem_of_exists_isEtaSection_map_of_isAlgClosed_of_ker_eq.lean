-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6ff00c6d-4285-5ace-ab63-d0a6310a22c3

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_mem_of_isAdmissible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace BwdAsm

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.Rigidified CerednikDrinfeld.GradedCartierModuleData

theorem latticeRel_nsmul {p : ℕ} [Fact p.Prime] {S' : Type} [CommRing S'] {jS' : Zp2 p →+* S'}
    (E : GradedCartierModuleData p S' jS') (n : ℕ) (r : (Fin 2 → ℤ_[p]) →+ E.NMod) (zbar : E.NMod)
    (v : Fin 2 → ℚ_[p]) (k : ℕ) (h : LatticeRel E n r zbar v) :
    LatticeRel E n r (p ^ k • zbar) ((p : ℚ_[p]) ^ k • v) := by
  obtain ⟨m, kk, w, hw, hr⟩ := h
  refine ⟨m, kk, p ^ k • w, ?_, ?_⟩
  · rw [smul_comm, hw]
    funext i
    simp [Pi.smul_apply, nsmul_eq_mul]
  · rw [map_nsmul, smul_comm, hr, smul_comm]

end BwdAsm

open BwdAsm in

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
      (∃ (f : L) (_ : f ∉ x'.asIdeal) (hc : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
        (hcb : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
        (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
        (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L'),
        ∃ z, (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L' hL' i z v) →
      v ∈ N x := by
  classical
  intro x' v hv

  have hscale : ∀ k : ℕ, ∃ (f : L) (_ : f ∉ x'.asIdeal) (hc : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
      (hcb : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
      (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
      (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L'),
      ∃ z, (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L' hL' i z
        ((algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ k • v) := by
    intro k
    obtain ⟨f, hf, hc, hcb, hcΦf, L', hL', z, hz⟩ := hv
    refine ⟨f, hf, hc, hcb, hcΦf, L', hL', p ^ k • z, ?_⟩
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨AddSubgroup.nsmul_mem _ hz1 _, ?_⟩
    rw [map_natCast]
    have e1 : ((((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nVarpi ^ (i : ℕ)) (p ^ k • z) =
        p ^ k • ((((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nVarpi ^ (i : ℕ)) z := map_nsmul _ _ _
    rw [e1, map_nsmul, smul_comm]
    exact latticeRel_nsmul _ _ _ _ _ k hz2

  obtain ⟨c, hc⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_mem_of_isAdmissible p ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ
    ψ hB t ht i N hN x v

  have hdesc : ∀ k : ℕ, k ≤ c → (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ (c - k) • v ∈ N x := by
    intro k
    induction k with
    | zero => intro _; simpa using hc
    | succ k ih =>
      intro hk
      have hk' : k ≤ c := Nat.le_of_succ_le hk
      have hprev := ih hk'
      have e : c - k = c - (k + 1) + 1 := by omega
      rw [e, pow_succ', mul_smul] at hprev
      exact CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
        p ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht i N hN g hg x hx ht' x' _ hprev (hscale (c - (k + 1)))
  have := hdesc c le_rfl
  simpa using this

end S_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq (solution)
