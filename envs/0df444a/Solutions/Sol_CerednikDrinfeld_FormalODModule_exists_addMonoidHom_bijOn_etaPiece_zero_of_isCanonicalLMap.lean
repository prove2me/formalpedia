-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijOn_etaPiece_zero_of_isCanonicalLMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ef156b79-0369-5e83-b121-a01bb12473e2

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk
import Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists
import Theorems.Thm_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijOn_etaPiece_zero_of_isCanonicalLMap
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace EtaFreeRank2

open MvFormalGroup MvFormalGroup.CartierModule

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

theorem isMaximal_pIdeal [IsAlgClosed k] : (pIdeal p (WittVector p k)).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)

theorem charP_quot : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
  CharP.quotient (WittVector p k) p (mem_nonunits_iff.2 (WittVector.irreducible p).not_isUnit)

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

end EtaFreeRank2

end

open EtaFreeRank2 MvFormalGroup MvFormalGroup.CartierModule in
open scoped PadicInt Padic in

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod) (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L) :
    ∃ r : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      Set.BijOn r Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _) := by
  classical

  haveI hmax : (pIdeal p (WittVector p k)).IsMaximal := isMaximal_pIdeal p k
  letI instF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
  haveI hchar : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := charP_quot p k
  obtain ⟨eK⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI hac : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) := isAlgClosed_of_ringEquiv eK

  let Φ' : SpecialFormalODModule p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) := ⟨Φ, hΦ, hΦ4⟩
  have hcrit := CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ'
  obtain ⟨c, hcinj, hcfix⟩ :=
    WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range p (WittVector p k ⧸ pIdeal p (WittVector p k))
  have hV : ∀ f : CartierModule p Φ.F, verschiebungInt f = verschiebung f :=
    fun f => verschiebungInt_apply_eq_verschiebung f
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

  have caseA : CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 →
      ∃ r : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
        Set.BijOn r Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _) := by
    intro h0
    have hi' : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ),
        ∃ g : CartierModule p Φ.F, verschiebungInt g = endAct Φ.varpiEnd m := fun m hm => by
      obtain ⟨g, hg⟩ := h0 m hm
      exact ⟨g, by rw [hV]; exact hg⟩
    have hL0 : ∀ x y : CartierModule p Φ.F, x ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ) →
        verschiebungInt y = endAct Φ.varpiEnd x → L x = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (y, 0) := fun x y hx hy =>
      CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
        p k ι Φ hΦ hΦ4 hcΦ L hL 0 hi' x y hx hy
    obtain ⟨hmem, hinj0⟩ :=
      CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk
        p k ι Φ hΦ hΦ4 hcΦ L hL 0 hi' hL0
    obtain ⟨e, he_inv, he_basis, he_iff, -, -⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
        p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ' 0 h0
    obtain ⟨coord, hcoord, hbij⟩ := coordFacts 0 e he_inv he_basis he_iff
    let r : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod := (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk.comp ((AddMonoidHom.inl _ _).comp coord)
    have hr : ∀ v, r v = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (coord v, 0) := fun v => rfl
    refine ⟨r, ?_, ?_, ?_⟩
    · intro v _
      rw [hr]
      obtain ⟨h1, h2⟩ := hbij.1 (Set.mem_univ v)
      exact (hmem _).2 ⟨coord v, h1, h2, rfl⟩
    · intro v _ v' _ hvv
      rw [hr, hr] at hvv
      have := hinj0 _ _ (hbij.1 (Set.mem_univ v)).1 (hbij.1 (Set.mem_univ v')).1 hvv
      exact hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) this
    · intro z hz
      obtain ⟨m, hm, hPV, rfl⟩ := (hmem z).1 hz
      obtain ⟨v, -, hv⟩ := hbij.2.2 ⟨hm, hPV⟩
      exact ⟨v, Set.mem_univ _, by rw [hr, hv]⟩
  rcases hcrit.2 with h0 | h1
  · exact caseA h0
  rcases hcrit.1 0 with h0 | hpb
  · exact caseA h0

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
  have hcT : ∀ v, coord v ∈ T := fun v => hbij.1 (Set.mem_univ v)
  let r : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod :=
    { toFun := fun v => g (coord v)
      map_zero' := by rw [map_zero, hg0]
      map_add' := fun a b => by rw [map_add, hgadd _ (hcT a) _ (hcT b)] }
  have hr : ∀ v, r v = g (coord v) := fun v => rfl
  refine ⟨r, ?_, ?_, ?_⟩
  · intro v _
    rw [hr]
    exact hgS (hcT v)
  · intro v _ v' _ hvv
    rw [hr, hr] at hvv
    have : coord v = coord v' := by rw [← hgr _ (hcT v), ← hgr _ (hcT v'), hvv]
    exact hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) this
  · intro z hz
    obtain ⟨v, -, hv⟩ := hbij.2.2 (hB.mapsTo hz)
    refine ⟨v, Set.mem_univ _, ?_⟩
    rw [hr, hv, hgl z hz]

end S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijOn_etaPiece_zero_of_isCanonicalLMap
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijOn_etaPiece_zero_of_isCanonicalLMap (solution)
