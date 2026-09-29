-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_and_forall_exists_isEtaSection_one_iff_mulVec_eq_of_lieOne_le_ker_of_isAlgClosed_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/773dad61-caac-5675-ae15-de3a67ca44a2

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_two_mul_add_one_of_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_and_forall_exists_isEtaSection_one_iff_mulVec_eq_of_lieOne_le_ker_of_isAlgClosed_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
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
    {B : Type} [Field B] [IsAlgClosed B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : B))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : B)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : B)))
    (L : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).NMod)
    (hL : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).IsCanonicalLMap L)
    (h1X : t.X.lieOne (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi) :
    ∃ (e : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (u : ℤ_[p]ˣ),
      γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ (2 * e + 1) ∧
      ∀ v : Fin 2 → ℚ_[p],
        (∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (1 : B)) hc hcb hcΦ1 L hL 1 z v) ↔
        ∃ (m : ℕ) (w c : Fin 2 → ℤ_[p]),
          (p : ℚ_[p]) ^ m • v = (fun i => ((w i : ℤ_[p]) : ℚ_[p])) ∧
            γ.mulVec w = (p : ℤ_[p]) ^ (e + m) • c := by
  obtain ⟨c, e, γ, he, heb, himg, hinj, hrig⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht hc hcb hcΦ1 L hL h1X
  obtain ⟨u, hu⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_two_mul_add_one_of_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht hc hcb hcΦ1 L hL h1X c e he heb γ hrig
  refine ⟨t.n, γ, u, hu, fun v => ?_⟩
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have key : ∀ (q : ℕ) (a : Fin 2 → ℤ_[p]),
      q • ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData
          (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0) =
        ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData
          (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (((q : ℤ_[p]) • a) r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0) := by
    intro q a
    rw [← map_nsmul, Prod.smul_mk, smul_zero, Finset.smul_sum]
    refine congrArg _ (Prod.ext ?_ rfl)
    show (∑ r, q • (c (a r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r))) =
      ∑ r, c (((q : ℤ_[p]) • a) r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r)
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast,
      ← Nat.cast_smul_eq_nsmul (WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B)))),
      smul_smul]
  constructor
  · rintro ⟨z, hz⟩
    rw [Rigidified.isEtaSection_one_iff] at hz
    obtain ⟨hzη, m, kk, w, hvw, hrel⟩ := hz
    obtain ⟨a, ha⟩ := (himg _).1 ⟨z, hzη, rfl⟩

    have hrel' := congrArg (fun y => p • y) hrel
    rw [smul_comm p (p ^ kk), hrig w, ha, ← mul_smul, ← pow_succ', key, key] at hrel'
    have h2 := hinj _ _ hrel'
    refine ⟨m + 1, w, a, ?_, ?_⟩
    · rw [pow_succ, mul_smul]; exact hvw
    have hpk : ((p : ℤ_[p]) ^ kk) ≠ 0 := pow_ne_zero _ hp0
    apply smul_right_injective (Fin 2 → ℤ_[p]) hpk
    show (p : ℤ_[p]) ^ kk • γ.mulVec w = (p : ℤ_[p]) ^ kk • ((p : ℤ_[p]) ^ (t.n + (m + 1)) • a)
    push_cast at h2
    rw [h2, ← mul_smul, ← pow_add]
    congr 1; ring
  · rintro ⟨m, w, cc, hvw, hγw⟩
    obtain ⟨z, hzη, hz⟩ := (himg _).2 ⟨cc, rfl⟩
    refine ⟨z, ?_⟩
    rw [Rigidified.isEtaSection_one_iff]
    refine ⟨hzη, m, 0, p • w, ?_, ?_⟩
    · rw [smul_comm, hvw]
      funext i
      simp [Pi.smul_apply]
    rw [pow_zero, one_smul, zero_add, map_nsmul, hrig w, hγw, hz, key]
    push_cast
    rfl

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_and_forall_exists_isEtaSection_one_iff_mulVec_eq_of_lieOne_le_ker_of_isAlgClosed_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_and_forall_exists_isEtaSection_one_iff_mulVec_eq_of_lieOne_le_ker_of_isAlgClosed_wittVector (solution)
