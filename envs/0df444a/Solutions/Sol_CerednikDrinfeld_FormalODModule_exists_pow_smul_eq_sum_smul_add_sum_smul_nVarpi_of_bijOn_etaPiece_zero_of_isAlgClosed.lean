-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d441ab8e-8e2f-539e-a0c3-085527e34573

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
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierLMapFibre
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk
import Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists
import Theorems.Thm_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Theorems.Thm_PadicInt_addMonoidHom_map_smul_of_free
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_map_varpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData_wittVector_quotient
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace NSpanBase

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime]

theorem isAlgClosed_of_ringEquiv {F F' : Type} [Field F] [Field F'] [IsAlgClosed F] (e : F ≃+* F') :
    IsAlgClosed F' := by
  refine IsAlgClosed.of_exists_root F' fun q _ hqi => ?_
  set q' : Polynomial F := q.map e.symm.toRingHom with hq'def
  have hq' : q'.degree ≠ 0 := by
    rw [hq'def, Polynomial.degree_map_eq_of_injective e.symm.injective]
    exact (Polynomial.degree_pos_of_irreducible hqi).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q' hq'
  refine ⟨e x, ?_⟩
  have hqq : q = q'.map e.toRingHom := by
    rw [hq'def, Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
  rw [hqq, Polynomial.eval_map]
  show Polynomial.eval₂ e.toRingHom (e.toRingHom x) q' = 0
  rw [Polynomial.eval₂_at_apply, hx.eq_zero, map_zero]

theorem nsmul_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (n : ℕ) (m m' : D.M) : n • D.nMk (m, m') = D.nMk (n • m, n • m') := by
  rw [← map_nsmul]; rfl

theorem nVarpi_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (m m' : D.M) : D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem smul_nMk_zero {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (w : WittVector p B) (m : D.M) : w • D.nMk (m, 0) = D.nMk (w • m, 0) := by
  rw [smul_nMk, smul_zero]

theorem nMk_verschiebung_zero {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (y : D.M) : D.nMk (D.verschiebung y, 0) = D.nMk (0, D.varpi y) := by
  have h := D.nMk_verschiebung_neg_varpi y
  have : ((D.verschiebung y, (0 : D.M)) : D.M × D.M) = (D.verschiebung y, -D.varpi y) + (0, D.varpi y) := by
    simp
  rw [this, map_add, h, zero_add]

theorem exists_nsmul_eq_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (x : D.NMod) : ∃ n : D.M, (p : ℕ) • x = D.nMk (n, 0) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective x
  refine ⟨(p : ℕ) • m + D.verschiebung (D.varpi m'), ?_⟩
  have h1 : ((((p : ℕ) • m + D.verschiebung (D.varpi m')), (0 : D.M)) : D.M × D.M) =
      ((p : ℕ) • m, 0) + (D.verschiebung (D.varpi m'), 0) := by simp
  rw [nsmul_nMk, h1, map_add, nMk_verschiebung_zero, D.varpi_varpi, ← map_add]
  congr 1
  simp

theorem nVarpi_nVarpi {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (x : D.NMod) : D.nVarpi (D.nVarpi x) = (p : ℕ) • x := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective x
  rw [nVarpi_nMk, nVarpi_nMk, D.varpi_varpi, D.varpi_varpi, nsmul_nMk]

theorem phi_smul {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (w : WittVector p B) (z : D.NMod) :
    D.phi L hL.map_verschiebung (w • z) = WittVector.frobenius w • D.phi L hL.map_verschiebung z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [smul_nMk, phi_nMk, phi_nMk, hL.map_smul, smul_add, smul_nMk_zero]

theorem smul_mem_eta {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (w : WittVector p B) (hw : WittVector.frobenius w = w)
    (z : D.NMod) (hz : z ∈ D.eta L hL.map_verschiebung) : w • z ∈ D.eta L hL.map_verschiebung := by
  rw [mem_eta_iff] at hz ⊢
  rw [phi_smul D L hL, hw, hz]

theorem map_smul_of_bijOn {N : Type} [AddCommGroup N] (S : Set N) (c : ℤ_[p] → N → N)
    (ψ : (Fin 2 → ℤ_[p]) →+ N) (hψlin : ∀ (t : ℤ_[p]) (v : Fin 2 → ℤ_[p]), ψ (t • v) = c t (ψ v))
    (hψ : Set.BijOn ψ Set.univ S)
    (r : (Fin 2 → ℤ_[p]) →+ N) (hr : Set.BijOn r Set.univ S)
    (t : ℤ_[p]) (v : Fin 2 → ℤ_[p]) : r (t • v) = c t (r v) := by
  classical

  let g : N → (Fin 2 → ℤ_[p]) := Function.invFunOn ψ Set.univ
  have hgr : ∀ s ∈ S, ψ (g s) = s := fun s hs => hψ.surjOn.rightInvOn_invFunOn hs
  have hrS : ∀ u, r u ∈ S := fun u => hr.mapsTo (Set.mem_univ u)
  let θ : (Fin 2 → ℤ_[p]) →+ (Fin 2 → ℤ_[p]) :=
    { toFun := fun u => g (r u)
      map_zero' := by
        apply hψ.injOn (Set.mem_univ _) (Set.mem_univ _)
        rw [hgr _ (hrS 0), map_zero, map_zero]
      map_add' := fun a b => by
        apply hψ.injOn (Set.mem_univ _) (Set.mem_univ _)
        rw [hgr _ (hrS _), map_add, map_add, hgr _ (hrS _), hgr _ (hrS _)] }
  have hθ : ∀ u, ψ (θ u) = r u := fun u => hgr _ (hrS u)
  have hθlin : θ (t • v) = t • θ v := PadicInt.addMonoidHom_map_smul_of_free p θ t v
  rw [← hθ, hθlin, hψlin, hθ]

theorem nVarpi_mem_etaPiece_zero
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
    (z : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod) (hz : z ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 1) :
    (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi z ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 := by
  have hDspec : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsSpecialCartierModule :=
    CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData_wittVector_quotient p k ι Φ hΦ hcΦ
  rw [GradedCartierModuleData.etaPiece, AddSubgroup.mem_inf] at hz
  obtain ⟨hzη, hzp⟩ := hz
  rw [GradedCartierModuleData.etaPiece, AddSubgroup.mem_inf]
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hzp
  obtain ⟨ha, hb⟩ := hab
  constructor
  · rw [mem_eta_iff] at hzη ⊢
    rw [nVarpi_nMk, phi_nMk,
      CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.map_varpi p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) hDspec L hL a]
    rw [phi_nMk] at hzη
    have h2 := congrArg (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi hzη
    rw [map_add, nVarpi_nMk, nVarpi_nMk, map_zero] at h2
    exact h2
  · refine ⟨((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi a, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi b), ⟨?_, ?_⟩, (nVarpi_nMk (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) a b).symm⟩
    · have := (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi_mem 1 a ha
      exact this
    · have := (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi_mem 1 b hb
      exact this

theorem critFacts
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
    (i : Fin 2)
    (hi' : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((i : Fin 2) : ℕ),
      ∃ g : CartierModule p Φ.F, verschiebungInt g = endAct Φ.varpiEnd m) :
    (∀ z : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
        z ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung i ↔
          ∃ m : CartierModule p Φ.F, m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (i : ℕ) ∧
            endAct Φ.varpiEnd m = verschiebungInt m ∧ z = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0)) ∧
      (∀ m m' : CartierModule p Φ.F, m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (i : ℕ) → m' ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (i : ℕ) →
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0) = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m', 0) → m = m') ∧
      (∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (i : ℕ), ∃ (w : Fin 2 → WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) (z : Fin 2 → (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
        (∀ r, z r ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung i) ∧
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0) = ∑ r, w r • z r) := by
  classical
  haveI hmax : (pIdeal p (WittVector p k)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)
  letI instF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
  haveI hchar : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
    CharP.quotient (WittVector p k) p (mem_nonunits_iff.2 (WittVector.irreducible p).not_isUnit)
  obtain ⟨eK⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI hac : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) := isAlgClosed_of_ringEquiv eK
  let Φ' : SpecialFormalODModule p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) := ⟨Φ, hΦ, hΦ4⟩
  have hV : ∀ f : CartierModule p Φ.F, verschiebungInt f = verschiebung f :=
    fun f => verschiebungInt_apply_eq_verschiebung f
  have hi : CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (i : ℕ) := fun m hm => by
    obtain ⟨g, hg⟩ := hi' m hm
    exact ⟨g, by rw [← hV]; exact hg⟩
  have hLi : ∀ x y : CartierModule p Φ.F, x ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((i : Fin 2) : ℕ) →
      verschiebungInt y = endAct Φ.varpiEnd x → L x = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (y, 0) := fun x y hx hy =>
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
      p k ι Φ hΦ hΦ4 hcΦ L hL i hi' x y hx hy
  obtain ⟨hmem, hinj⟩ :=
    CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk
      p k ι Φ hΦ hΦ4 hcΦ L hL i hi' hLi
  obtain ⟨e, he_inv, he_basis, -, -, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
      p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ' i hi
  refine ⟨hmem, hinj, fun m hm => ?_⟩
  obtain ⟨w, hw, -⟩ := he_basis m hm
  refine ⟨w, fun r => (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (e r, 0), fun r => ?_, ?_⟩
  · exact (hmem _).2 ⟨e r, (he_inv r).1, by rw [hV]; exact (he_inv r).2, rfl⟩
  · rw [hw]
    have hsum : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk ((∑ r, w r • e r), 0) = ∑ r, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (w r • e r, 0) :=
      map_sum ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk.comp (AddMonoidHom.inl _ _)) (fun r => w r • e r) Finset.univ
    refine hsum.trans (Finset.sum_congr rfl fun r _ => ?_)
    exact (smul_nMk_zero (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) (w r) (e r)).symm

theorem exists_psi
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L) :
    ∃ (c : ℤ_[p] →+* WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) (ψ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
      (∀ t : ℤ_[p], WittVector.frobenius (c t) = c t) ∧
      (∀ (t : ℤ_[p]) (v : Fin 2 → ℤ_[p]), ψ (t • v) = c t • ψ v) ∧
      Set.BijOn ψ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _) := by
  classical
  haveI hmax : (pIdeal p (WittVector p k)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)
  letI instF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
  haveI hchar : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
    CharP.quotient (WittVector p k) p (mem_nonunits_iff.2 (WittVector.irreducible p).not_isUnit)
  obtain ⟨eK⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI hac : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) := isAlgClosed_of_ringEquiv eK
  let Φ' : SpecialFormalODModule p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) := ⟨Φ, hΦ, hΦ4⟩
  have hV : ∀ f : CartierModule p Φ.F, verschiebungInt f = verschiebung f :=
    fun f => verschiebungInt_apply_eq_verschiebung f
  have hcrit := CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ'
  obtain ⟨c, hcinj, hcfix⟩ :=
    WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range p (WittVector p k ⧸ pIdeal p (WittVector p k))
  have hcfix' : ∀ t : ℤ_[p], WittVector.frobenius (c t) = c t := fun t => (hcfix (c t)).2 ⟨t, rfl⟩
  have hsmul : ∀ (n : ℕ) (w : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) (f : CartierModule p Φ.F),
      f ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) n → w • f ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) n := fun n =>
    (CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ' n).1

  have coordFacts : ∀ (i : ℕ) (e : Fin 2 → CartierModule p Φ.F),
      (∀ r, e r ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i) →
      (∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i, ∃! w : Fin 2 → WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)), m = ∑ r, w r • e r) →
      (∀ w : Fin 2 → WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)),
        (∑ r, w r • e r) ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i ↔ ∀ r, WittVector.frobenius (w r) = w r) →
      ∃ coord : (Fin 2 → ℤ_[p]) →+ CartierModule p Φ.F,
        (∀ v, coord v = ∑ r, c (v r) • e r) ∧
        Set.BijOn coord Set.univ {m | m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i ∧ endAct Φ.varpiEnd m = verschiebungInt m} := by
    intro i e he_inv he_basis he_iff
    let coord : (Fin 2 → ℤ_[p]) →+ CartierModule p Φ.F :=
      { toFun := fun v => ∑ r, c (v r) • e r
        map_zero' := by simp
        map_add' := fun a b => by
          simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib] }
    have hcoord : ∀ v, coord v = ∑ r, c (v r) • e r := fun v => rfl
    have hpiece : ∀ v, coord v ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i := fun v => by
      rw [hcoord]
      exact AddSubgroup.sum_mem _ fun r _ => hsmul i _ _ (he_inv r).1
    have hinv : ∀ v, coord v ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i := fun v => by
      rw [hcoord]
      exact (he_iff _).2 fun r => hcfix' (v r)
    refine ⟨coord, hcoord, ?_, ?_, ?_⟩
    · intro v _
      refine ⟨hpiece v, ?_⟩
      rw [hV]
      exact (hinv v).2
    · intro v _ v' _ hvv
      have h1 : coord v = ∑ r, (fun r => c (v r)) r • e r := hcoord v
      have h2 : coord v = ∑ r, (fun r => c (v' r)) r • e r := hvv.trans (hcoord v')
      have := (he_basis _ (hpiece v)).unique h1 h2
      funext r
      exact hcinj (congrFun this r)
    · intro m hm
      obtain ⟨hm1, hm2⟩ := hm
      have hm' : m ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i := ⟨hm1, by rw [← hV]; exact hm2⟩
      obtain ⟨w, hw, -⟩ := he_basis m hm1
      have hfix : ∀ r, WittVector.frobenius (w r) = w r := (he_iff w).1 (hw ▸ hm')
      choose v hv using fun r => (hcfix (w r)).1 (hfix r)
      refine ⟨v, Set.mem_univ _, ?_⟩
      rw [hcoord, hw]
      exact Finset.sum_congr rfl fun r _ => by rw [hv r]
  have hcoordlin : ∀ (i : ℕ) (e : Fin 2 → CartierModule p Φ.F) (coord : (Fin 2 → ℤ_[p]) →+ CartierModule p Φ.F),
      (∀ v, coord v = ∑ r, c (v r) • e r) → ∀ (t : ℤ_[p]) (v : Fin 2 → ℤ_[p]), coord (t • v) = c t • coord v := by
    intro i e coord hcoord t v
    rw [hcoord, hcoord, Finset.smul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  have hψ : ∃ ψ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      (∀ (t : ℤ_[p]) (v : Fin 2 → ℤ_[p]), ψ (t • v) = c t • ψ v) ∧
      Set.BijOn ψ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _) := by

    have caseA : CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 →
        ∃ ψ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
          (∀ (t : ℤ_[p]) (v : Fin 2 → ℤ_[p]), ψ (t • v) = c t • ψ v) ∧
          Set.BijOn ψ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _) := by
      intro h0
      have h0' : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ),
          ∃ g : CartierModule p Φ.F, verschiebungInt g = endAct Φ.varpiEnd m := fun m hm => by
        obtain ⟨g, hg⟩ := h0 m hm
        exact ⟨g, by rw [hV]; exact hg⟩
      obtain ⟨hmem, hinj0, -⟩ := critFacts p k ι Φ hΦ hΦ4 hcΦ L hL 0 h0'
      obtain ⟨e, he_inv, he_basis, he_iff, -, -⟩ :=
        CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
          p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ' 0 h0
      obtain ⟨coord, hcoord, hbij⟩ := coordFacts 0 e he_inv he_basis he_iff
      let ψ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod := (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk.comp ((AddMonoidHom.inl _ _).comp coord)
      have hψ' : ∀ v, ψ v = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (coord v, 0) := fun v => rfl
      refine ⟨ψ, fun t v => ?_, ?_, ?_, ?_⟩
      · rw [hψ', hψ', hcoordlin 0 e coord hcoord t v, smul_nMk_zero]
        rfl
      · intro v _
        rw [hψ']
        obtain ⟨h1, h2⟩ := hbij.1 (Set.mem_univ v)
        exact (hmem _).2 ⟨coord v, h1, h2, rfl⟩
      · intro v _ v' _ hvv
        rw [hψ', hψ'] at hvv
        have := hinj0 _ _ (hbij.1 (Set.mem_univ v)).1 (hbij.1 (Set.mem_univ v')).1 hvv
        exact hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) this
      · intro z hz
        obtain ⟨m, hm, hPV, rfl⟩ := (hmem z).1 hz
        obtain ⟨v, -, hv⟩ := hbij.2.2 ⟨hm, hPV⟩
        exact ⟨v, Set.mem_univ _, by rw [hψ', hv]⟩
    by_cases h0 : CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0
    · exact caseA h0

    have hpb : Φ'.IsPiBijective ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 := (hcrit.1 0).resolve_left h0
    have h1 : CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1 := hcrit.2.resolve_left h0
    obtain ⟨hpb1, hpb2⟩ := hpb
    have hinj' : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ),
        (∃ g : CartierModule p Φ.F, verschiebungInt g = endAct Φ.varpiEnd m) →
          ∃ g' : CartierModule p Φ.F, verschiebungInt g' = m := by
      intro m hm ⟨g, hg⟩
      obtain ⟨g', hg'⟩ := hpb1 m hm ⟨g, by rw [← hV]; exact hg⟩
      exact ⟨g', by rw [hV]; exact hg'⟩
    have hsurj' : ∀ z ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (((0 : Fin 2) + 1 : Fin 2) : ℕ), ∃ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ),
        ∃ m' : CartierModule p Φ.F, z = endAct Φ.varpiEnd m + verschiebungInt m' := by
      intro z hz
      obtain ⟨f, hf, g, hfg⟩ := hpb2 z hz
      exact ⟨f, hf, g, by rw [hV]; exact hfg⟩
    have hB := CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists
      p k ι Φ hΦ hΦ4 hcΦ L hL 0 hsurj' hinj'
    obtain ⟨e, he_inv, he_basis, he_iff, -, -⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
        p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ' 1 h1
    obtain ⟨coord, hcoord, hbij⟩ := coordFacts 1 e he_inv he_basis he_iff
    replace hB : Set.BijOn (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).lambda
        (((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : AddSubgroup (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod) : Set (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
        {m : CartierModule p Φ.F | m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1 ∧ endAct Φ.varpiEnd m = verschiebungInt m} := hB
    set S : Set (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod := (((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : AddSubgroup (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod) : Set (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod) with hS
    set T : Set (CartierModule p Φ.F) := {m | m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1 ∧ endAct Φ.varpiEnd m = verschiebungInt m} with hTdef
    let g : CartierModule p Φ.F → (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod := Function.invFunOn (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).lambda S
    have hgS : Set.MapsTo g T S := hB.surjOn.mapsTo_invFunOn
    have hgr : ∀ t ∈ T, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).lambda (g t) = t := fun t ht => hB.surjOn.rightInvOn_invFunOn ht
    have hgl : ∀ z ∈ S, g ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).lambda z) = z := fun z hz => hB.injOn.leftInvOn_invFunOn hz
    have hTadd : ∀ a ∈ T, ∀ b ∈ T, a + b ∈ T := by
      intro a ha b hb
      exact ⟨AddSubgroup.add_mem _ ha.1 hb.1, by rw [map_add, map_add, ha.2, hb.2]⟩
    have hT0 : (0 : CartierModule p Φ.F) ∈ T := ⟨AddSubgroup.zero_mem _, by rw [map_zero, map_zero]⟩
    have hgadd : ∀ a ∈ T, ∀ b ∈ T, g (a + b) = g a + g b := by
      intro a ha b hb
      apply hB.injOn (hgS (hTadd a ha b hb)) (AddSubgroup.add_mem _ (hgS ha) (hgS hb))
      rw [map_add, hgr _ (hTadd a ha b hb), hgr _ ha, hgr _ hb]
      rfl
    have hg0 : g 0 = 0 := by
      apply hB.injOn (hgS hT0) (AddSubgroup.zero_mem _)
      rw [map_zero, hgr _ hT0]
      rfl

    have hTsmul : ∀ (t : ℤ_[p]) (m : CartierModule p Φ.F), m ∈ T → c t • m ∈ T := by
      intro t m hm
      refine ⟨hsmul 1 (c t) m hm.1, ?_⟩
      have hlin : endAct Φ.varpiEnd (c t • m) = c t • endAct Φ.varpiEnd m := ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi).map_smul (c t) m
      rw [hlin, hm.2, smul_verschiebungInt, hcfix']
    have hSsmul : ∀ (t : ℤ_[p]) (z : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod), z ∈ S → c t • z ∈ S := by
      intro t z hz
      have hz' : z ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 := hz
      show c t • z ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0
      rw [GradedCartierModuleData.etaPiece, AddSubgroup.mem_inf] at hz' ⊢
      obtain ⟨hzη, hzp⟩ := hz'
      refine ⟨smul_mem_eta (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) L hL.isCartierLMap (c t) (hcfix' t) z hzη, ?_⟩
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hzp
      refine ⟨(c t • a, WittVector.frobenius (c t) • b), ⟨?_, ?_⟩, (smul_nMk (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) (c t) a b).symm⟩
      · exact hsmul 0 (c t) a ha
      · rw [hcfix']; exact hsmul 0 (c t) b hb
    have hgsmul : ∀ (t : ℤ_[p]) (m : CartierModule p Φ.F), m ∈ T → g (c t • m) = c t • g m := by
      intro t m hm
      apply hB.injOn (hgS (hTsmul t m hm)) (hSsmul t _ (hgS hm))
      rw [hgr _ (hTsmul t m hm), map_smul, hgr _ hm]
      rfl
    have hcT : ∀ v, coord v ∈ T := fun v => hbij.1 (Set.mem_univ v)
    let ψ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod :=
      { toFun := fun v => g (coord v)
        map_zero' := by rw [map_zero, hg0]
        map_add' := fun a b => by rw [map_add, hgadd _ (hcT a) _ (hcT b)] }
    have hψ' : ∀ v, ψ v = g (coord v) := fun v => rfl
    refine ⟨ψ, fun t v => ?_, ?_, ?_, ?_⟩
    · rw [hψ', hψ', hcoordlin 1 e coord hcoord t v, hgsmul t _ (hcT v)]
    · intro v _
      rw [hψ']
      exact hgS (hcT v)
    · intro v _ v' _ hvv
      rw [hψ', hψ'] at hvv
      have : coord v = coord v' := by rw [← hgr _ (hcT v), ← hgr _ (hcT v'), hvv]
      exact hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) this
    · intro z hz
      obtain ⟨v, -, hv⟩ := hbij.2.2 (hB.mapsTo hz)
      refine ⟨v, Set.mem_univ _, ?_⟩
      rw [hψ', hv, hgl z hz]
  obtain ⟨ψ, h1, h2⟩ := hψ
  exact ⟨c, ψ, hcfix', h1, h2⟩

end NSpanBase

end

open NSpanBase MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in
open scoped PadicInt Padic in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _)) :
    ∃ a : ℕ, ∀ x : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      ∃ c d : Fin 2 → WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)),
        p ^ a • x = (∑ i : Fin 2, c i • rΦ (Pi.single i 1)) +
          ∑ i : Fin 2, d i • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi (rΦ (Pi.single i 1)) := by
  classical
  haveI hmax : (pIdeal p (WittVector p k)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)
  letI instF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
  haveI hchar : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
    CharP.quotient (WittVector p k) p (mem_nonunits_iff.2 (WittVector.irreducible p).not_isUnit)
  obtain ⟨eK⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI hac : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) := isAlgClosed_of_ringEquiv eK
  let Φ' : SpecialFormalODModule p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) := ⟨Φ, hΦ, hΦ4⟩
  have hV : ∀ f : CartierModule p Φ.F, verschiebungInt f = verschiebung f :=
    fun f => verschiebungInt_apply_eq_verschiebung f
  have hcrit := (CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ').2
  obtain ⟨L, hL⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
      p k ι Φ hΦ hcΦ
  have hr := hrΦ L hL
  obtain ⟨c, ψ, hcfix', hψlin, hψbij⟩ := exists_psi p k ι Φ hΦ hΦ4 hcΦ L hL

  have hrlin : ∀ (t : ℤ_[p]) (v : Fin 2 → ℤ_[p]), rΦ (t • v) = c t • rΦ v :=
    map_smul_of_bijOn _ (fun t x => c t • x) ψ hψlin hψbij rΦ hr
  set P₀ : Submodule (WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod :=
    Submodule.span (WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) (Set.range fun i : Fin 2 => rΦ (Pi.single i 1)) with hP₀
  set P₁ : Submodule (WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod :=
    Submodule.span (WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) (Set.range fun i : Fin 2 => (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi (rΦ (Pi.single i 1))) with hP₁
  have hη₀ : ∀ z ∈ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _), z ∈ P₀ := by
    intro z hz
    obtain ⟨v, -, rfl⟩ := hr.surjOn hz
    have hv : v = ∑ i : Fin 2, v i • (Pi.single i (1 : ℤ_[p]) : Fin 2 → ℤ_[p]) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply, Fin.sum_univ_two]
    rw [hv, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hrlin]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmapP₀ : P₀.map (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi ≤ P₁ := by
    rw [hP₀, Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  have hmapP₁ : P₁.map (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi ≤ P₀ := by
    rw [hP₁, Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    rw [nVarpi_nVarpi]
    have hmem : rΦ (Pi.single i 1) ∈ P₀ := by
      rw [hP₀]; exact Submodule.subset_span (Set.mem_range_self i)
    exact nsmul_mem hmem _

  suffices H : ∃ a : ℕ, ∀ x : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod, p ^ a • x ∈ P₀ ⊔ P₁ by
    obtain ⟨a, ha⟩ := H
    refine ⟨a, fun x => ?_⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (ha x)
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)))).1 hy
    obtain ⟨dd, hdd⟩ := (Submodule.mem_span_range_iff_exists_fun (WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)))).1 hz
    exact ⟨cc, dd, by rw [← hyz, ← hcc, ← hdd]⟩

  have hdecomp : ∀ n : CartierModule p Φ.F, ∃ n₀ ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0, ∃ n₁ ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1,
      n₀ + n₁ = n := fun n => by
    have : n ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 ⊔ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1 := by
      rw [hcΦ.sup_eq_top]; trivial
    exact AddSubgroup.mem_sup.1 this
  have hPi01 : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0, endAct Φ.varpiEnd m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1 := fun m hm =>
    Φ.endAct_varpiEnd_mem_gradedPiece_succ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 m hm
  have hPi10 : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1, endAct Φ.varpiEnd m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 := fun m hm => by
    have h := Φ.endAct_varpiEnd_mem_gradedPiece_succ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1 m hm
    have h2 := FormalODModule.gradedPiece_add_two Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0
    rw [zero_add] at h2
    rwa [h2] at h

  have hpPi : ∀ m : CartierModule p Φ.F,
      (p : ℕ) • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0) = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (endAct Φ.varpiEnd m, 0)) := fun m => by
    rw [nVarpi_nMk, map_zero, nsmul_nMk, smul_zero]
    congr 1
    ext
    · exact ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi_varpi m).symm
    · rfl
  rcases hcrit with h0 | h1
  ·
    have h0' : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ),
        ∃ g : CartierModule p Φ.F, verschiebungInt g = endAct Φ.varpiEnd m := fun m hm => by
      obtain ⟨g, hg⟩ := h0 m hm
      exact ⟨g, by rw [hV]; exact hg⟩
    obtain ⟨-, -, hspan0⟩ := critFacts p k ι Φ hΦ hΦ4 hcΦ L hL 0 h0'
    have hM0 : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0) ∈ P₀ := fun m hm => by
      obtain ⟨w, z, hz, hmz⟩ := hspan0 m hm
      rw [hmz]
      exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hη₀ _ (hz r))
    refine ⟨2, fun x => ?_⟩
    obtain ⟨n, hn⟩ := exists_nsmul_eq_nMk (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) x
    obtain ⟨n₀, hn₀, n₁, hn₁, rfl⟩ := hdecomp n
    have e1 : p ^ 2 • x = (p : ℕ) • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (n₀, 0) + (p : ℕ) • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (n₁, 0) := by
      rw [pow_two, mul_smul, hn, ← nsmul_add, ← map_add, Prod.mk_add_mk, add_zero]
      rfl
    rw [e1]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (nsmul_mem (hM0 n₀ hn₀) _))
      (Submodule.mem_sup_right ?_)
    rw [hpPi]
    exact hmapP₀ (Submodule.mem_map_of_mem (hM0 _ (hPi10 n₁ hn₁)))
  ·
    have h1' : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((1 : Fin 2) : ℕ),
        ∃ g : CartierModule p Φ.F, verschiebungInt g = endAct Φ.varpiEnd m := fun m hm => by
      obtain ⟨g, hg⟩ := h1 m hm
      exact ⟨g, by rw [hV]; exact hg⟩
    obtain ⟨-, -, hspan1⟩ := critFacts p k ι Φ hΦ hΦ4 hcΦ L hL 1 h1'
    have hPieta := nVarpi_mem_etaPiece_zero p k ι Φ hΦ hΦ4 hcΦ L hL
    have hM1 : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0)) ∈ P₀ := fun m hm => by
      obtain ⟨w, z, hz, hmz⟩ := hspan1 m hm
      have hz' : ∀ r, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi (z r) ∈ P₀ := fun r => hη₀ _ (hPieta _ (hz r))
      have hs : (∑ r, w r • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi (z r)) ∈ P₀ :=
        Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hz' r)
      have h1 : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi (∑ r, w r • z r) = ∑ r, w r • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi (z r) := by
        simp only [Fin.sum_univ_two, map_add, LinearMap.map_smul]
      have h2 : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0)) = ∑ r, w r • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi (z r) :=
        (congrArg (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi hmz).trans h1
      exact h2.symm ▸ hs
    have hM1' : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1, (p : ℕ) • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0) ∈ P₁ := fun m hm => by
      rw [← nVarpi_nVarpi (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (m, 0))]
      exact hmapP₀ (Submodule.mem_map_of_mem (hM1 m hm))
    refine ⟨3, fun x => ?_⟩
    obtain ⟨n, hn⟩ := exists_nsmul_eq_nMk (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) x
    obtain ⟨n₀, hn₀, n₁, hn₁, rfl⟩ := hdecomp n
    have e1 : p ^ 3 • x = (p : ℕ) • ((p : ℕ) • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (n₀, 0)) + (p : ℕ) • ((p : ℕ) • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (n₁, 0)) := by
      rw [show p ^ 3 = p * p * p by ring, mul_smul, mul_smul, hn, ← nsmul_add, ← nsmul_add, ← map_add,
        Prod.mk_add_mk, add_zero]
      rfl
    rw [e1]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (nsmul_mem (hM1' n₁ hn₁) _))
    rw [hpPi n₀, ← map_nsmul]
    exact hmapP₁ (Submodule.mem_map_of_mem (hM1' _ (hPi01 n₀ hn₀)))

end S_CerednikDrinfeld_FormalODModule_exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed (solution)
