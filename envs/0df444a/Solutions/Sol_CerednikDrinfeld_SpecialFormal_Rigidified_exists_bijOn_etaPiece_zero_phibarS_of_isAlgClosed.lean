-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_bijOn_etaPiece_zero_phibarS_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/836a00ba-0658-5455-a836-835ef94bed68

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
import Theorems.Thm_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_bijOn_etaPiece_zero_phibarS_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"
set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace EtaFreeFibre

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule

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

theorem core (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K] [CharP K p] (j : Zp2 p →+* K)
    (X : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) (i : Fin 2) :
    ∃ r : (Fin 2 → ℤ_[p]) →+ (X.toGradedCartierModuleData j hc).NMod,
      Set.BijOn r Set.univ ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i : Set _) := by
  classical
  let Φs : SpecialFormalODModule p j := ⟨X, hX, hX4⟩
  obtain ⟨hdich, hcrit01⟩ := CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field p j Φs
  obtain ⟨c, hcinj, hcfix⟩ := WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range p K
  have hV : ∀ f : CartierModule p X.F, verschiebungInt f = verschiebung f :=
    fun f => verschiebungInt_apply_eq_verschiebung f
  have hcfix' : ∀ t : ℤ_[p], WittVector.frobenius (c t) = c t := fun t => (hcfix (c t)).2 ⟨t, rfl⟩
  have htors : ∀ m : CartierModule p X.F, endAct X.varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p j X hX hX4

  have coordFacts : ∀ (n : ℕ) (e : Fin 2 → CartierModule p X.F),
      (∀ r, e r ∈ CritChart.invariants X j n) →
      (∀ m ∈ X.gradedPiece j n, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r) →
      (∀ w : Fin 2 → WittVector p K,
        (∑ r, w r • e r) ∈ CritChart.invariants X j n ↔ ∀ r, WittVector.frobenius (w r) = w r) →
      ∃ coord : (Fin 2 → ℤ_[p]) →+ CartierModule p X.F,
        (∀ v, coord v = ∑ r, c (v r) • e r) ∧
        Set.BijOn coord Set.univ {m | m ∈ X.gradedPiece j n ∧ endAct X.varpiEnd m = verschiebungInt m} := by
    intro n e he_inv he_basis he_iff
    let coord : (Fin 2 → ℤ_[p]) →+ CartierModule p X.F :=
      { toFun := fun v => ∑ r, c (v r) • e r
        map_zero' := by simp
        map_add' := fun a b => by
          simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib] }
    have hcoord : ∀ v, coord v = ∑ r, c (v r) • e r := fun v => rfl
    have hpiece : ∀ v, coord v ∈ X.gradedPiece j n := fun v => by
      rw [hcoord]
      exact AddSubgroup.sum_mem _ fun r _ => smul_mem_gradedPiece X j n _ _ (he_inv r).1
    have hinv : ∀ v, coord v ∈ CritChart.invariants X j n := fun v => by
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
      have hm' : m ∈ CritChart.invariants X j n := ⟨hm1, by rw [← hV]; exact hm2⟩
      obtain ⟨w, hw, -⟩ := he_basis m hm1
      have hfix : ∀ r, WittVector.frobenius (w r) = w r := (he_iff w).1 (hw ▸ hm')
      choose v hv using fun r => (hcfix (w r)).1 (hfix r)
      refine ⟨v, Set.mem_univ _, ?_⟩
      rw [hcoord, hw]
      exact Finset.sum_congr rfl fun r _ => by rw [hv r]

  have caseA : CritChart.IsCritical X j (i : ℕ) →
      ∃ r : (Fin 2 → ℤ_[p]) →+ (X.toGradedCartierModuleData j hc).NMod,
        Set.BijOn r Set.univ ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i : Set _) := by
    intro hi
    have hi' : ∀ m ∈ X.gradedPiece j (i : ℕ), ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m := by
      intro m hm
      obtain ⟨g, hg⟩ := hi m hm
      exact ⟨g, by rw [hV]; exact hg⟩
    have hLi : ∀ x y : CartierModule p X.F, x ∈ X.gradedPiece j (i : ℕ) →
        verschiebungInt y = endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0) := fun x y hx hy =>
      CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL (i : ℕ) hi' x y hx hy
    obtain ⟨hmem, hinj0⟩ :=
      CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
        p j X hc L hL htors i hi' hLi
    obtain ⟨e, he_inv, he_basis, he_iff, -, -⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
        p j Φs (i : ℕ) hi
    obtain ⟨coord, hcoord, hbij⟩ := coordFacts (i : ℕ) e he_inv he_basis he_iff
    let r : (Fin 2 → ℤ_[p]) →+ (X.toGradedCartierModuleData j hc).NMod := (X.toGradedCartierModuleData j hc).nMk.comp ((AddMonoidHom.inl _ _).comp coord)
    have hr : ∀ v, r v = (X.toGradedCartierModuleData j hc).nMk (coord v, 0) := fun v => rfl
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
  by_cases hcrit : CritChart.IsCritical X j (i : ℕ)
  · exact caseA hcrit

  have hbij : X.IsPiBijective j (i : ℕ) := (hdich (i : ℕ)).resolve_left hcrit
  have hcrit' : CritChart.IsCritical X j ((i + 1 : Fin 2) : ℕ) := by
    fin_cases i
    · exact hcrit01.resolve_left hcrit
    · exact hcrit01.resolve_right hcrit
  have hsurj : ∀ z ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ), ∃ m ∈ X.gradedPiece j (i : ℕ),
      ∃ m' : CartierModule p X.F, z = endAct X.varpiEnd m + verschiebungInt m' := by
    intro z hz
    rw [gradedPiece_fin_add_one] at hz
    obtain ⟨f, hf, g, hg⟩ := hbij.2 z hz
    exact ⟨f, hf, g, by rw [hV]; exact hg⟩
  have hinj : ∀ m ∈ X.gradedPiece j (i : ℕ),
      (∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m) →
        ∃ g' : CartierModule p X.F, verschiebungInt g' = m := by
    rintro m hm ⟨g, hg⟩
    obtain ⟨g', hg'⟩ := hbij.1 m hm ⟨g, by rw [← hV]; exact hg⟩
    exact ⟨g', by rw [hV]; exact hg'⟩
  have hB := CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
    p j X hc L hL i hsurj hinj
  obtain ⟨e, he_inv, he_basis, he_iff, -, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
      p j Φs ((i + 1 : Fin 2) : ℕ) hcrit'
  obtain ⟨coord, hcoord, hbijc⟩ := coordFacts ((i + 1 : Fin 2) : ℕ) e he_inv he_basis he_iff

  set S : Set (X.toGradedCartierModuleData j hc).NMod := (((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i : AddSubgroup (X.toGradedCartierModuleData j hc).NMod) : Set (X.toGradedCartierModuleData j hc).NMod) with hS
  set T : Set (CartierModule p X.F) := {m | m ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ) ∧ endAct X.varpiEnd m = verschiebungInt m} with hTdef
  let g : CartierModule p X.F → (X.toGradedCartierModuleData j hc).NMod := Function.invFunOn (X.toGradedCartierModuleData j hc).lambda S
  have hgS : Set.MapsTo g T S := hB.surjOn.mapsTo_invFunOn
  have hgr : ∀ t ∈ T, (X.toGradedCartierModuleData j hc).lambda (g t) = t := fun t ht => hB.surjOn.rightInvOn_invFunOn ht
  have hgl : ∀ z ∈ S, g ((X.toGradedCartierModuleData j hc).lambda z) = z := fun z hz => hB.injOn.leftInvOn_invFunOn hz
  have hTadd : ∀ a ∈ T, ∀ b ∈ T, a + b ∈ T := by
    intro a ha b hb
    exact ⟨AddSubgroup.add_mem _ ha.1 hb.1, by rw [map_add, map_add, ha.2, hb.2]⟩
  have hT0 : (0 : CartierModule p X.F) ∈ T := ⟨AddSubgroup.zero_mem _, by rw [map_zero, map_zero]⟩
  have hgadd : ∀ a ∈ T, ∀ b ∈ T, g (a + b) = g a + g b := by
    intro a ha b hb
    apply hB.injOn (hgS (hTadd a ha b hb)) (AddSubgroup.add_mem _ (hgS ha) (hgS hb))
    rw [map_add, hgr _ (hTadd a ha b hb), hgr _ ha, hgr _ hb]
    rfl
  have hg0 : g 0 = 0 := by
    apply hB.injOn (hgS hT0) (AddSubgroup.zero_mem _)
    rw [map_zero, hgr _ hT0]
    rfl
  have hcT : ∀ v, coord v ∈ T := fun v => hbijc.1 (Set.mem_univ v)
  let r : (Fin 2 → ℤ_[p]) →+ (X.toGradedCartierModuleData j hc).NMod :=
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
    exact hbijc.2.1 (Set.mem_univ _) (Set.mem_univ _) this
  · intro z hz
    obtain ⟨v, -, hv⟩ := hbijc.2.2 (hB.mapsTo hz)
    refine ⟨v, Set.mem_univ _, ?_⟩
    rw [hr, hv, hgl z hz]

theorem core_of_ringEquiv (p : ℕ) [Fact p.Prime] {K R : Type} [Field K] [IsAlgClosed K] [CharP K p] [CommRing R]
    (eKR : K ≃+* R) (j : Zp2 p →+* R)
    (X : FormalODModule p R) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) (i : Fin 2) :
    ∃ r : (Fin 2 → ℤ_[p]) →+ (X.toGradedCartierModuleData j hc).NMod,
      Set.BijOn r Set.univ ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i : Set _) := by
  haveI : CharP R p := charP_of_injective_ringHom (f := eKR.toRingHom) (fun a b h => eKR.injective h) p
  letI instF : Field R := (MulEquiv.isField (Field.toIsField K) eKR.symm.toMulEquiv).toField
  haveI : IsAlgClosed R := isAlgClosed_of_ringEquiv eKR
  exact core p j X hX hX4 hc L hL i

end EtaFreeFibre

end

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L') :
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ),
      ∃ r' : (Fin 2 → ℤ_[p]) →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod,
        Set.BijOn r' Set.univ (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0 : Set _) := by
  intro LΦ hLΦ

  haveI hchS : CharP (Rigidified.Baway (1 : K)) p :=
    charP_of_injective_ringHom (f := (IsLocalization.atOne K (Rigidified.Baway (1 : K))).toRingEquiv.toRingHom)
      (fun a b h => (IsLocalization.atOne K (Rigidified.Baway (1 : K))).injective h) p
  have hbot : pIdeal p (Rigidified.Baway (1 : K)) = ⊥ := Ideal.span_singleton_eq_bot.2 (CharP.cast_eq_zero (Rigidified.Baway (1 : K)) p)
  let e : K ≃+* (Rigidified.Baway (1 : K)) ⧸ pIdeal p (Rigidified.Baway (1 : K)) :=
    (IsLocalization.atOne K (Rigidified.Baway (1 : K))).toRingEquiv.trans
      ((RingEquiv.quotientBot (Rigidified.Baway (1 : K))).symm.trans (Ideal.quotEquivOfEq hbot.symm))

  have hXS : (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).IsSpecial (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) :=
    CerednikDrinfeld.FormalODModule.IsSpecial.map _ (reduceMap (p := p) (Rigidified.awayHom (1 : K))) _
      (CerednikDrinfeld.FormalODModule.IsSpecial.map _ (residueMap (p := p) ψ') Φ hΦ)
  have h4a : (Φ.map (residueMap (p := p) ψ')).HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree ((Φ.map (residueMap (p := p) ψ')).act (p : Zp2 p)) (p ^ 4)
    rw [FormalODModule.map_act]
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (residueMap (p := p) ψ') _ (Φ.isLawHom_act _).1 hΦ4
  have hX4S : (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree (((Φ.map (residueMap (p := p) ψ')).map (reduceMap (p := p) (Rigidified.awayHom (1 : K)))).act (p : Zp2 p)) (p ^ 4)
    rw [FormalODModule.map_act]
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (reduceMap (p := p) (Rigidified.awayHom (1 : K))) _
      ((Φ.map (residueMap (p := p) ψ')).isLawHom_act _).1 h4a
  exact EtaFreeFibre.core_of_ringEquiv p e (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K)))
    (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) hXS hX4S hcΦ1 LΦ hLΦ 0

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_bijOn_etaPiece_zero_phibarS_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_bijOn_etaPiece_zero_phibarS_of_isAlgClosed (solution)
