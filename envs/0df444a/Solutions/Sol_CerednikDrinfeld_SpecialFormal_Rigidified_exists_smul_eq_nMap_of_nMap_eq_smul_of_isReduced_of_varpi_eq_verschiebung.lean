-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_verschiebung
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/abb2bedf-7860-5d46-ae17-4739860d55c3

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_digits_mem_sq_of_varpi_eq_verschiebung
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_varpi_eq_teichmuller_smul_add_verschiebung_mul_eq
import Theorems.Thm_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_verschiebung
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace StratumDescent

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

section Datum

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j)

theorem exists_eq_teichmuller_smul_add_verschiebung {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  classical
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 x

  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hy : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := Submodule.mem_sup.1 hy

  fin_cases i
  ·
    have hdec : x = (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) +
        (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have hz : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 0 := by
      have : x - (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) ∈ D.piece 0 := Submodule.sub_mem _ hx h0
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ hz h1
    refine ⟨c 0, y1, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl
  · have hdec : x = (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) +
        (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have hz : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 1 := by
      have : x - (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) ∈ D.piece 1 := Submodule.sub_mem _ hx h1
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ h0 hz
    refine ⟨c 1, y0, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl

theorem teichmuller_coeff_unique {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (c c' : Fin 2 → B) (y y' : D.M)
    (h : (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y =
      (∑ i : Fin 2, WittVector.teichmuller p (c' i) • γ i) + D.verschiebung y') :
    c = c' ∧ y = y' := by
  obtain ⟨cy, -, huniq⟩ := hγ.2 ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y)
  have h1 : (c, y) = cy := huniq (c, y) rfl
  have h2 : (c', y') = cy := huniq (c', y') h
  have := h1.trans h2.symm
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem fin_two_add_one_add_one (l : Fin 2) : l + 1 + 1 = l := by
  fin_cases l <;> rfl

theorem exists_piece_split (l : Fin 2) (g : D.M) :
    ∃ g₁ ∈ D.piece l, ∃ g₂ ∈ D.piece (l + 1), g = g₁ + g₂ := by
  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hg : g ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨g0, hg0, g1, hg1, rfl⟩ := Submodule.mem_sup.1 hg
  fin_cases l
  · exact ⟨g0, hg0, g1, hg1, rfl⟩
  · exact ⟨g1, hg1, g0, hg0, add_comm _ _⟩

theorem eq_zero_of_mem_piece_of_mem_piece_add_one (l : Fin 2) (m : D.M) (h₁ : m ∈ D.piece l)
    (h₂ : m ∈ D.piece (l + 1)) : m = 0 := by
  have hd := D.isCompl_piece.disjoint
  rw [Submodule.disjoint_def] at hd
  fin_cases l
  · exact hd _ h₁ h₂
  · exact hd _ h₂ h₁

theorem mem_piece_of_verschiebung_mem (hV : Function.Injective D.verschiebung) (l : Fin 2) (g : D.M)
    (hg : D.verschiebung g ∈ D.piece (l + 1)) : g ∈ D.piece l := by
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := exists_piece_split D l g
  have h2 : D.verschiebung g₂ ∈ D.piece l := by
    have := D.verschiebung_mem (l + 1) g₂ hg₂
    rwa [fin_two_add_one_add_one] at this
  have h2' : D.verschiebung g₂ ∈ D.piece (l + 1) := by
    have h1 : D.verschiebung g₁ ∈ D.piece (l + 1) := D.verschiebung_mem l g₁ hg₁
    have := Submodule.sub_mem _ hg h1
    rwa [map_add, add_sub_cancel_left] at this
  have hz : D.verschiebung g₂ = 0 := eq_zero_of_mem_piece_of_mem_piece_add_one D l _ h2 h2'
  have : g₂ = 0 := hV (by rw [hz, map_zero])
  rw [this, add_zero]
  exact hg₁

theorem exists_eq_teichmuller_smul_add_verschiebung' {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), m ∈ D.piece (i + 1) ∧ x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  obtain ⟨c, m, hxm⟩ := exists_eq_teichmuller_smul_add_verschiebung D hγ i x hx
  refine ⟨c, m, ?_, hxm⟩
  apply mem_piece_of_verschiebung_mem D hγ.verschiebung_injective
  rw [fin_two_add_one_add_one]
  have := Submodule.sub_mem _ hx (Submodule.smul_mem _ (WittVector.teichmuller p c) (hγ.1 i))
  rwa [hxm, add_sub_cancel_left] at this

theorem mem_nPiece_iff (l : Fin 2) (z : D.NMod) :
    z ∈ D.nPiece l ↔ ∃ m m' : D.M, m ∈ D.piece l ∧ m' ∈ D.piece l ∧ D.nMk (m, m') = z := by
  constructor
  · rintro ⟨⟨m, m'⟩, hmm, rfl⟩
    exact ⟨m, m', hmm.1, hmm.2, rfl⟩
  · rintro ⟨m, m', hm, hm', rfl⟩
    exact ⟨(m, m'), ⟨hm, hm'⟩, rfl⟩

theorem nMk_mem_nPiece (l : Fin 2) {m m' : D.M} (hm : m ∈ D.piece l) (hm' : m' ∈ D.piece l) :
    D.nMk (m, m') ∈ D.nPiece l :=
  (mem_nPiece_iff D l _).2 ⟨m, m', hm, hm', rfl⟩

theorem smul_mem_nPiece (l : Fin 2) (w : WittVector p B) {z : D.NMod} (hz : z ∈ D.nPiece l) :
    w • z ∈ D.nPiece l := by
  obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff D l z).1 hz
  rw [smul_nMk]
  exact nMk_mem_nPiece D l (Submodule.smul_mem _ _ hm) (Submodule.smul_mem _ _ hm')

theorem lambda_mem_piece (l : Fin 2) {z : D.NMod} (hz : z ∈ D.nPiece l) : D.lambda z ∈ D.piece (l + 1) := by
  obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff D l z).1 hz
  rw [lambda_nMk]
  exact Submodule.add_mem _ (D.varpi_mem l m hm) (D.verschiebung_mem l m' hm')

theorem teichmuller_smul_eq_sum (γ : Fin 2 → D.M) (i : Fin 2) (c : B) :
    WittVector.teichmuller p c • γ i =
      ∑ r : Fin 2, WittVector.teichmuller p ((if r = i then c else 0 : B)) • γ r := by
  fin_cases i <;> simp [Fin.sum_univ_two, WittVector.teichmuller_zero]

theorem digit_unique {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ) (i : Fin 2) (c c' : B) (y y' : D.M)
    (h : WittVector.teichmuller p c • γ i + D.verschiebung y =
      WittVector.teichmuller p c' • γ i + D.verschiebung y') : c = c' ∧ y = y' := by
  rw [teichmuller_smul_eq_sum D γ i c, teichmuller_smul_eq_sum D γ i c'] at h
  obtain ⟨hcc, hyy⟩ := teichmuller_coeff_unique D hγ _ _ y y' h
  have := congrFun hcc i
  simp only [] at this
  exact ⟨by simpa using this, hyy⟩

theorem nsmul_eq_verschiebung_verschiebung (n : D.M) (hn : D.varpi n = D.verschiebung n) :
    p • n = D.verschiebung (D.verschiebung n) := by
  rw [← D.varpi_varpi, hn, D.varpi_verschiebung, hn]

end Datum

section Law

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (jR : Zp2 p →+* R)
  (X : FormalODModule p R) (hc : IsCompl (X.gradedPiece jR 0) (X.gradedPiece jR 1))

theorem crit_of_basis (γ : Fin 2 → (X.toGradedCartierModuleData jR hc).M)
    (hγ : (X.toGradedCartierModuleData jR hc).IsHomogeneousVBasis γ) (i : Fin 2) (xi : (X.toGradedCartierModuleData jR hc).M)
    (hcrit : (X.toGradedCartierModuleData jR hc).varpi (γ i) = (X.toGradedCartierModuleData jR hc).verschiebung xi) :
    ∀ m ∈ X.gradedPiece jR (i : ℕ), ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m := by
  intro m hm
  obtain ⟨c, m', hmm⟩ := exists_eq_teichmuller_smul_add_verschiebung (X.toGradedCartierModuleData jR hc) hγ i m hm
  refine ⟨(WittVector.frobenius (WittVector.teichmuller p c) • xi + (X.toGradedCartierModuleData jR hc).varpi m' :
    (X.toGradedCartierModuleData jR hc).M), ?_⟩
  have : (X.toGradedCartierModuleData jR hc).varpi m =
      (X.toGradedCartierModuleData jR hc).verschiebung
        (WittVector.frobenius (WittVector.teichmuller p c) • xi + (X.toGradedCartierModuleData jR hc).varpi m') := by
    rw [hmm, map_add, map_smul, hcrit, (X.toGradedCartierModuleData jR hc).smul_verschiebung,
      (X.toGradedCartierModuleData jR hc).varpi_verschiebung, ← map_add]
  exact this.symm

variable [CharP R p]

theorem nMk_mem_etaPiece (L : (X.toGradedCartierModuleData jR hc).M →+ (X.toGradedCartierModuleData jR hc).NMod)
    (hL : (X.toGradedCartierModuleData jR hc).IsCanonicalLMap L) (i : Fin 2)
    (hi : ∀ m ∈ X.gradedPiece jR (i : ℕ), ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m)
    (n : CartierModule p X.F) (hn : n ∈ X.gradedPiece jR (i : ℕ))
    (hinv : endAct X.varpiEnd n = verschiebungInt n) :
    (X.toGradedCartierModuleData jR hc).nMk (n, 0) ∈
      (X.toGradedCartierModuleData jR hc).etaPiece L hL.isCartierLMap.map_verschiebung i := by
  have hLe : L n = (X.toGradedCartierModuleData jR hc).nMk (n, 0) :=
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p jR X hc L hL (i : ℕ) hi n n hn hinv.symm
  refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_eta_iff, phi_nMk, hLe, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  · exact AddSubgroup.mem_map.2 ⟨(n, 0), AddSubgroup.mem_prod.2 ⟨hn, zero_mem _⟩, rfl⟩

end Law

theorem hasHeight_map_field {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B)
    (hX4 : X.HasHeight 4) {K : Type} [Field K] (g : B →+* K) : (X.map g).HasHeight 4 := by
  obtain ⟨-, -, hfib⟩ := hX4
  have hK : Module.finrank K (FormalODModule.KerAlgebra ((X.act (p : Zp2 p)).map g)) = p ^ 4 := hfib K g
  show FormalODModule.HasKernelOfDegree ((X.map g).act (p : Zp2 p)) (p ^ 4)
  rw [FormalODModule.map_act]
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · exact Module.finite_of_finrank_pos (by rw [hK]; exact pow_pos (Nat.Prime.pos Fact.out) 4)
  · exact Module.Projective.of_free
  · rw [CerednikDrinfeld.SpecialFormal.Series.map_map]; exact hfib κ (f.comp g)

theorem isBaseChangeAlong'_of_eq {p : ℕ} [Fact p.Prime] {B S : Type} [CommRing B] [CommRing S] (j : Zp2 p →+* B)
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

theorem isHausdorff_of_eq_zero {p : ℕ} {S : Type} [CommRing S] (hS : ((p : ℕ) : S) = 0) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  refine ⟨fun x hx => ?_⟩
  have := hx 1
  rwa [pow_one, hS, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

end StratumDescent

end

set_option maxHeartbeats 6400000 in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
open StratumDescent CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2) (γ : Fin 2 → ((t.XS g).toGradedCartierModuleData _ hc).M) (hγ : ((t.XS g).toGradedCartierModuleData _ hc).IsHomogeneousVBasis γ)
    (xj : ((t.XS g).toGradedCartierModuleData _ hc).M) (hcrit : ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ j) = ((t.XS g).toGradedCartierModuleData _ hc).verschiebung xj)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    {K : Type} [Field K] [IsAlgClosed K] (k : S →+* K) (hk : RingHom.ker k = x.asIdeal)
    (hc' : t.IsGradedS ι ψ (k.comp g))
    (L' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').M →+ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').NMod) (hL' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').IsCanonicalLMap L')
    (hXh : (t.XS g).F.map k = (t.XS (k.comp g)).F)
    (hbcV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hbcPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hdiv : ∃ y ∈ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').etaPiece L' hL'.isCartierLMap.map_verschiebung j,
      ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by
  classical

  haveI hNontriv : Nontrivial S := nontrivial_of_ne 1 0 (fun h10 =>
    x.2.ne_top ((Ideal.eq_top_iff_one _).2 (h10.symm ▸ x.asIdeal.zero_mem)))
  haveI : CharP S p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Fact.out hS)
  have hpS : IsNilpotent ((p : ℕ) : S) := ⟨1, by rw [pow_one, hS]⟩
  have hXS : (t.XS g).IsSpecial (Rigidified.jS ι ψ g) :=
    CerednikDrinfeld.FormalODModule.IsSpecial.map _ g t.X ht.1
  have hX4S : (t.XS g).HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree ((t.X.map g).act (p : Zp2 p)) (p ^ 4)
    rw [FormalODModule.map_act]
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map g _ (t.X.isLawHom_act _).1 ht.2.1
  have htorsS : ∀ m : CartierModule p (t.XS g).F, endAct (t.XS g).varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p (Rigidified.jS ι ψ g)
      (t.XS g) hXS hX4S
  have hVinj : Function.Injective ((t.XS g).toGradedCartierModuleData _ hc).verschiebung := hγ.verschiebung_injective

  have hcritS := crit_of_basis (Rigidified.jS ι ψ g) (t.XS g) hc γ hγ j xj hcrit
  have hLjS : ∀ x y : CartierModule p (t.XS g).F, x ∈ (t.XS g).gradedPiece (Rigidified.jS ι ψ g) (j : ℕ) →
      verschiebungInt y = endAct (t.XS g).varpiEnd x → L x = ((t.XS g).toGradedCartierModuleData _ hc).nMk (y, 0) :=
    fun x y hx hy => CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p _ (t.XS g) hc L hL
      (j : ℕ) hcritS x y hx hy
  obtain ⟨hdesc, -⟩ := CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
    p _ (t.XS g) hc L hL htorsS j hcritS hLjS
  obtain ⟨m, hmj, hinv, rfl⟩ := (hdesc z).1 hz

  have hinvD : ((t.XS g).toGradedCartierModuleData _ hc).varpi m = ((t.XS g).toGradedCartierModuleData _ hc).verschiebung m := hinv
  have hmD : m ∈ ((t.XS g).toGradedCartierModuleData _ hc).piece j := hmj

  obtain ⟨a, xs, hΓ, hxs, -⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.exists_varpi_eq_teichmuller_smul_add_verschiebung_mul_eq p _ ((t.XS g).toGradedCartierModuleData _ hc) γ hγ
  have hnext : ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ (j + 1)) = WittVector.teichmuller p (a (j + 1)) • γ j + ((t.XS g).toGradedCartierModuleData _ hc).verschiebung (xs (j + 1)) := by
    have := hΓ (j + 1)
    rwa [fin_two_add_one_add_one] at this
  obtain ⟨c, d, m₂, hm_eq, hcI, hdI⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.exists_digits_mem_sq_of_varpi_eq_verschiebung p _ ((t.XS g).toGradedCartierModuleData _ hc) γ hγ j xj (xs (j + 1))
      (a (j + 1)) hcrit hnext m hmD hinvD
  set I : Ideal S := Ideal.span {c, d} with hI
  have hcmem : c ∈ I := Ideal.subset_span (by simp)
  have hdmem : d ∈ I := Ideal.subset_span (by simp)
  have hII : I ≤ I ^ 2 := by
    rw [hI, Ideal.span_le]
    rintro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · have h1 : a (j + 1) * d ∈ (Ideal.span {u, d}) ^ 2 := Ideal.mul_mem_left _ _ hdI
      have h2 := Ideal.add_mem _ hcI h1
      rwa [sub_add_cancel] at h2
    · exact hdI

  obtain ⟨y, hyη, hNz⟩ := hdiv
  haveI : CharP K p := by
    have hpK : ((p : ℕ) : K) = 0 := by rw [← map_natCast k p, hS, map_zero]
    exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Fact.out hpK)
  have hXK : (t.XS (k.comp g)).IsSpecial (Rigidified.jS ι ψ (k.comp g)) :=
    CerednikDrinfeld.FormalODModule.IsSpecial.map _ (k.comp g) t.X ht.1
  have hX4K : (t.XS (k.comp g)).HasHeight 4 := hasHeight_map_field t.X ht.2.1 (k.comp g)
  have htorsK : ∀ m : CartierModule p (t.XS (k.comp g)).F, endAct (t.XS (k.comp g)).varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p (Rigidified.jS ι ψ (k.comp g))
      (t.XS (k.comp g)) hXK hX4K
  letI : Algebra ℤ_[p] S := (g.comp (algebraMap ℤ_[p] B)).toAlgebra
  have hγS : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) γ :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
      p _ (t.XS g) hc γ hγ
  set bcK : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').M := CartierModule.baseChangeEq (p := p) k hXh with hbcK
  have hXmK : (t.XS g).map k = t.XS (k.comp g) := by rw [FormalODModule.map_map]
  have hjK : k.comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ (k.comp g) := rfl
  have hbca : IsBaseChangeAlong' k ((t.XS g).toGradedCartierModuleData _ hc) ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') bcK := by
    rw [hbcK]; exact isBaseChangeAlong'_of_eq _ _ _ _ hγS hc _ hXmK _ hjK hc' hXh
  have hγK_law : (t.XS (k.comp g)).IsHomogeneousVBasis (Rigidified.jS ι ψ (k.comp g))
      (fun i => bcK (γ i)) :=
    ⟨fun i => hbca.2.2.2.2.1 i _ (hγ.1 i), by rw [hbcK]; exact isUnit_det_tangent_baseChangeEq k hXh γ hγS.2⟩
  obtain ⟨hγK, hDK⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData
    p _ (t.XS (k.comp g)) _ hγK_law hc'
  have hcritK : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').varpi (bcK (γ j)) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (bcK xj) := by
    have h0 := hbcPi (γ j)
    rw [hcrit, hbcV] at h0
    exact h0.symm
  have hcritK' := crit_of_basis (Rigidified.jS ι ψ (k.comp g)) (t.XS (k.comp g)) hc' _ hγK j _ hcritK
  have hLjK : ∀ x y : CartierModule p (t.XS (k.comp g)).F,
      x ∈ (t.XS (k.comp g)).gradedPiece (Rigidified.jS ι ψ (k.comp g)) (j : ℕ) →
      verschiebungInt y = endAct (t.XS (k.comp g)).varpiEnd x → L' x = ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').nMk (y, 0) :=
    fun x y hx hy => CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p _ (t.XS (k.comp g))
      hc' L' hL' (j : ℕ) hcritK' x y hx hy
  obtain ⟨hdescK, hinjK⟩ := CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
    p _ (t.XS (k.comp g)) hc' L' hL' htorsK j hcritK' hLjK
  obtain ⟨m', hm'j, hinv', rfl⟩ := (hdescK y).1 hyη
  have hinv'D : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').varpi m' = ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung m' := hinv'
  have h1 : ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') (bcK) hbcV hbcPi (((t.XS g).toGradedCartierModuleData _ hc).nMk (m, 0)) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').nMk (bcK m, 0) := by
    rw [nMap_nMk, map_zero]
  have h2 : p • ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').nMk (m', 0) = ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').nMk (((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung m'), 0) := by
    rw [← nsmul_eq_verschiebung_verschiebung ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') m' hinv'D, ← map_nsmul, Prod.smul_mk, smul_zero]
  have h3 : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').nMk (bcK m, 0) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').nMk (((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung m'), 0) := by
    rw [← h1, hNz, h2]
  have hVVmem : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung m') ∈
      (t.XS (k.comp g)).gradedPiece (Rigidified.jS ι ψ (k.comp g)) (j : ℕ) := by
    have := ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung_mem _ _ (((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung_mem j m' hm'j)
    rwa [fin_two_add_one_add_one] at this
  have hbcm_mem : bcK m ∈
      (t.XS (k.comp g)).gradedPiece (Rigidified.jS ι ψ (k.comp g)) (j : ℕ) := hbca.2.2.2.2.1 j m hmD
  have h4 : bcK m = ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung m') :=
    hinjK _ _ hbcm_mem hVVmem h3
  have h5 : bcK m =
      WittVector.teichmuller p (k c) • bcK (γ j) +
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (WittVector.teichmuller p (k d) • bcK (γ (j + 1)) +
        ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (bcK m₂)) := by
    conv_lhs => rw [hm_eq]
    erw [map_add, hbca.1, WittVector.map_teichmuller, hbcV, map_add, hbca.1, WittVector.map_teichmuller, hbcV]
    rfl
  have h6 : WittVector.teichmuller p (k c) • bcK (γ j) +
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (WittVector.teichmuller p (k d) • bcK (γ (j + 1)) +
        ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (bcK m₂)) =
      WittVector.teichmuller p (0 : K) • bcK (γ j) +
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung m') := by
    rw [← h5, h4, WittVector.teichmuller_zero, zero_smul, zero_add]
  obtain ⟨hkc, h7⟩ := digit_unique _ hγK j _ _ _ _ h6
  have h8 : WittVector.teichmuller p (k d) • bcK (γ (j + 1)) +
        ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (bcK m₂) =
      WittVector.teichmuller p (0 : K) • bcK (γ (j + 1)) + ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung m' := by
    rw [h7, WittVector.teichmuller_zero, zero_smul, zero_add]
  obtain ⟨hkd, -⟩ := digit_unique _ hγK (j + 1) _ _ _ _ h8

  have hIP : I ≤ x.asIdeal := by
    rw [hI, Ideal.span_le, ← hk]
    rintro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hkc
    · exact hkd
  haveI := x.2
  obtain ⟨f₀, hf₀, hkill⟩ := Ideal.exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le I hII x.asIdeal hIP

  have hr0 : ∀ u ∈ I, algebraMap S (Localization.Away f₀) u = 0 := fun u hu =>
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f₀) (Localization.Away f₀) u).2 ⟨⟨f₀, Submonoid.mem_powers f₀⟩, hkill u hu⟩
  have hrc : algebraMap S (Localization.Away f₀) c = 0 := hr0 c hcmem
  have hrd : algebraMap S (Localization.Away f₀) d = 0 := hr0 d hdmem
  have hp0 : ((p : ℕ) : Localization.Away f₀) = 0 := by rw [← map_natCast (algebraMap S (Localization.Away f₀)) p, hS, map_zero]
  have hpn0 : IsNilpotent ((p : ℕ) : Localization.Away f₀) := ⟨1, by rw [pow_one, hp0]⟩
  have hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpn0 _
  have hXm0 : (t.XS g).map (algebraMap S (Localization.Away f₀)) = t.XS ((algebraMap S (Localization.Away f₀)).comp g) := by rw [FormalODModule.map_map]
  have hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F := congrArg FormalODModule.F hXm0
  have hj0 : (algebraMap S (Localization.Away f₀)).comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g) := rfl
  set res : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M := CartierModule.baseChangeEq (p := p) (algebraMap S (Localization.Away f₀)) hXr with hres
  have hresa : IsBaseChangeAlong' (algebraMap S (Localization.Away f₀)) ((t.XS g).toGradedCartierModuleData _ hc) ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) res := by
    rw [hres]; exact isBaseChangeAlong'_of_eq _ _ _ _ hγS hc _ hXm0 _ hj0 hc₀ hXr
  have hrV := hresa.2.2.1
  have hrPi := hresa.2.2.2.1
  have hγ0_law : (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).IsHomogeneousVBasis (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (fun i => res (γ i)) :=
    ⟨fun i => hresa.2.2.2.2.1 i _ (hγ.1 i), by rw [hres]; exact isUnit_det_tangent_baseChangeEq _ hXr γ hγS.2⟩
  obtain ⟨hγ0, hD0⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData
    p _ (t.XS ((algebraMap S (Localization.Away f₀)).comp g)) _ hγ0_law hc₀
  obtain ⟨L₀, hL₀⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData
    p (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (isHausdorff_of_eq_zero hp0) (t.XS ((algebraMap S (Localization.Away f₀)).comp g)) _ hγ0_law hc₀

  have hresm : res m = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res m₂)) := by
    conv_lhs => rw [hm_eq]
    erw [map_add, hresa.1, WittVector.map_teichmuller, hrV, map_add, hresa.1, WittVector.map_teichmuller, hrV]
    rw [hrc, hrd, WittVector.teichmuller_zero, zero_smul, zero_add, zero_smul, zero_add]

  have hV0inj : Function.Injective ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung := hγ0.verschiebung_injective
  have hresm_mem : res m ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).piece j := hresa.2.2.2.2.1 j m hmD
  have hVm₂_mem : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res m₂) ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).piece (j + 1) := by
    apply mem_piece_of_verschiebung_mem _ hV0inj
    rw [fin_two_add_one_add_one, ← hresm]; exact hresm_mem
  have hm₂_mem : res m₂ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).piece j := by
    have := mem_piece_of_verschiebung_mem _ hV0inj j (res m₂) hVm₂_mem
    exact this
  have hinv0 : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (res m) = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res m) := by
    have h0 := hrPi m
    rw [hinvD, hrV] at h0
    exact h0.symm
  have hinv₂ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (res m₂) = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res m₂) := by
    apply hV0inj; apply hV0inj
    rw [← ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi_verschiebung, ← ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi_verschiebung, ← hresm, hinv0, hresm]

  haveI : Nontrivial (Localization.Away f₀) := by
    rw [← not_subsingleton_iff_nontrivial, IsLocalization.subsingleton_iff (M := Submonoid.powers f₀)]
    rintro ⟨n, hn⟩
    have hn' : f₀ ^ n = 0 := hn
    exact hf₀ (x.2.mem_of_pow_mem n (hn' ▸ x.asIdeal.zero_mem))
  haveI : CharP (Localization.Away f₀) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Fact.out hp0)

  have hcrit0 : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (res (γ j)) = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res xj) := by
    have h0 := hrPi (γ j)
    rw [hcrit, hrV] at h0
    exact h0.symm
  have hcrit0' := crit_of_basis (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (t.XS ((algebraMap S (Localization.Away f₀)).comp g)) hc₀ _ hγ0 j _ hcrit0
  have hz₀ := nMk_mem_etaPiece (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (t.XS ((algebraMap S (Localization.Away f₀)).comp g)) hc₀ L₀ hL₀ j hcrit0' (res m₂) hm₂_mem hinv₂
  refine ⟨f₀, hf₀, hc₀, L₀, hL₀, hXr, ?_, ?_, ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).nMk (res m₂, 0), hz₀, ?_⟩
  · intro u; exact hrV u
  · intro u; exact hrPi u
  ·
    rw [nMap_nMk, map_zero, ← map_nsmul, Prod.smul_mk, smul_zero,
      nsmul_eq_verschiebung_verschiebung ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (res m₂) hinv₂, ← hresm]

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_verschiebung
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_verschiebung (solution)
