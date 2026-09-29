-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/14625515-8e81-557e-bbe9-6b43647aa5e5

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierLMapFibre
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld

noncomputable section

namespace PointOnto

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] (j : Zp2 p →+* K)
  (X : FormalODModule p K) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))

theorem toLieQuot_nMk (a b : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).toLieQuot ((X.toGradedCartierModuleData j hc).nMk (a, b)) = (X.toGradedCartierModuleData j hc).vRange.mkQ a := rfl

def S (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) (i : Fin 2) :
    Set (CartierModule p X.F) :=
  {a | ∃ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i, (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ a}

theorem mem_S_of_nMk_mem (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) (i : Fin 2)
    (a b : CartierModule p X.F) (h : (X.toGradedCartierModuleData j hc).nMk (a, b) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i) :
    a ∈ S j X hc L hL i :=
  ⟨_, h, toLieQuot_nMk j X hc a b⟩

theorem tangent_mem_span (T : Set (CartierModule p X.F)) (e : Fin 2 → CartierModule p X.F)
    (he : ∀ r, e r ∈ T) (w : Fin 2 → WittVector p K) (m g : CartierModule p X.F)
    (hm : m = (∑ r, w r • e r) + verschiebungInt g) :
    tangent m ∈ Submodule.span K (tangent '' T) := by
  rw [hm, map_add, tangent_verschiebungInt, add_zero, map_sum]
  refine Submodule.sum_mem _ fun r _ => ?_
  rw [tangent_smul_witt]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e r, he r, rfl⟩)

theorem nMk_mem_etaPiece (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) (i : Fin 2)
    (hi : CritChart.IsCritical X j (i : ℕ)) (e : CartierModule p X.F)
    (he : e ∈ CritChart.invariants X j (i : ℕ)) :
    (X.toGradedCartierModuleData j hc).nMk (e, 0) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i := by
  have hi' : ∀ m ∈ X.gradedPiece j (i : ℕ), ∃ g : CartierModule p X.F,
      verschiebungInt g = endAct X.varpiEnd m := by
    intro m hm
    obtain ⟨g, hg⟩ := hi m hm
    exact ⟨g, by rw [verschiebungInt_apply_eq_verschiebung]; exact hg⟩
  have hLe : L e = (X.toGradedCartierModuleData j hc).nMk (e, 0) :=
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL (i : ℕ) hi' e e he.1
      (by rw [verschiebungInt_apply_eq_verschiebung]; exact he.2.symm)
  refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_eta_iff, phi_nMk, hLe, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  · exact AddSubgroup.mem_map.2 ⟨(e, 0), AddSubgroup.mem_prod.2 ⟨he.1, zero_mem _⟩, rfl⟩

include hc in

theorem exists_tangent_eq (hX : X.IsSpecial j) :
    (∀ τ ∈ X.lieZero j, ∃ m ∈ X.gradedPiece j 0, tangent m = τ) ∧
    (∀ τ ∈ X.lieOne j, ∃ m ∈ X.gradedPiece j 1, tangent m = τ) := by
  have hp : IsNilpotent (p : K) := ⟨1, by rw [pow_one]; exact CharP.cast_eq_zero K p⟩
  obtain ⟨hT0, hT1⟩ :=
    CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p j hp X
  have hdis := hX.1.disjoint
  rw [Submodule.disjoint_def] at hdis
  have split : ∀ τ : X.Lie, ∃ m₀ ∈ X.gradedPiece j 0, ∃ m₁ ∈ X.gradedPiece j 1,
      tangent m₀ + tangent m₁ = τ := by
    intro τ
    obtain ⟨m, rfl⟩ := MvFormalGroup.CartierModule.tangent_surjective p X.F τ
    have hm : m ∈ X.gradedPiece j 0 ⊔ X.gradedPiece j 1 := by
      rw [hc.sup_eq_top]; exact AddSubgroup.mem_top m
    obtain ⟨m₀, hm₀, m₁, hm₁, rfl⟩ := AddSubgroup.mem_sup.1 hm
    exact ⟨m₀, hm₀, m₁, hm₁, (map_add _ _ _).symm⟩
  constructor
  · intro τ hτ
    obtain ⟨m₀, hm₀, m₁, hm₁, hsum⟩ := split τ
    have h1 : tangent m₁ ∈ X.lieZero j := by
      have : tangent m₁ = τ - tangent m₀ := by rw [← hsum]; abel
      rw [this]; exact Submodule.sub_mem _ hτ (hT0 m₀ hm₀)
    have hz : tangent m₁ = 0 := hdis _ h1 (hT1 m₁ hm₁)
    exact ⟨m₀, hm₀, by rw [← hsum, hz, add_zero]⟩
  · intro τ hτ
    obtain ⟨m₀, hm₀, m₁, hm₁, hsum⟩ := split τ
    have h0 : tangent m₀ ∈ X.lieOne j := by
      have : tangent m₀ = τ - tangent m₁ := by rw [← hsum]; abel
      rw [this]; exact Submodule.sub_mem _ hτ (hT1 m₁ hm₁)
    have hz : tangent m₀ = 0 := hdis _ (hT0 m₀ hm₀) h0
    exact ⟨m₁, hm₁, by rw [← hsum, hz, zero_add]⟩

theorem key [IsAlgClosed K] (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) (i : Fin 2)
    (m₀ : CartierModule p X.F) (hm₀ : m₀ ∈ X.gradedPiece j (i : ℕ)) :
    tangent m₀ ∈ Submodule.span K (tangent '' S j X hc L hL i) := by
  classical
  let Φs : SpecialFormalODModule p j := ⟨X, hX, hX4⟩
  obtain ⟨hdich, hcrit01⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field p j Φs
  by_cases hcrit : CritChart.IsCritical X j (i : ℕ)
  ·
    obtain ⟨e, he, hbasis, -, -, -⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
        p j Φs (i : ℕ) hcrit
    obtain ⟨w, hw, -⟩ := hbasis m₀ hm₀
    refine tangent_mem_span X _ e (fun r => ?_) w m₀ 0 (by rw [map_zero, add_zero]; exact hw)
    exact mem_S_of_nMk_mem j X hc L hL i (e r) 0 (nMk_mem_etaPiece j X hc L hL i hcrit (e r) (he r))
  ·
    have hbij : X.IsPiBijective j (i : ℕ) := (hdich (i : ℕ)).resolve_left hcrit
    have hcrit' : CritChart.IsCritical X j ((i + 1 : Fin 2) : ℕ) := by
      fin_cases i
      · exact hcrit01.resolve_left hcrit
      · exact hcrit01.resolve_right hcrit
    obtain ⟨e, he, hbasis, -, -, -⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
        p j Φs ((i + 1 : Fin 2) : ℕ) hcrit'

    have hsurj : ∀ z ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ), ∃ m ∈ X.gradedPiece j (i : ℕ),
        ∃ m' : CartierModule p X.F, z = endAct X.varpiEnd m + verschiebungInt m' := by
      intro z hz
      rw [gradedPiece_fin_add_one] at hz
      obtain ⟨f, hf, g, hg⟩ := hbij.2 z hz
      exact ⟨f, hf, g, by rw [verschiebungInt_apply_eq_verschiebung]; exact hg⟩
    have hinj : ∀ m ∈ X.gradedPiece j (i : ℕ),
        (∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m) →
          ∃ g' : CartierModule p X.F, verschiebungInt g' = m := by
      rintro m hm ⟨g, hg⟩
      obtain ⟨g', hg'⟩ := hbij.1 m hm ⟨g, by rw [← verschiebungInt_apply_eq_verschiebung]; exact hg⟩
      exact ⟨g', by rw [verschiebungInt_apply_eq_verschiebung]; exact hg'⟩
    have hBij := CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
      p j X hc L hL i hsurj hinj

    have hz : ∀ r : Fin 2, ∃ a ∈ X.gradedPiece j (i : ℕ), ∃ b : CartierModule p X.F,
        (X.toGradedCartierModuleData j hc).nMk (a, b) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i ∧
        e r = endAct X.varpiEnd a + verschiebungInt b := by
      intro r
      have her : e r ∈ {m : CartierModule p X.F | m ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ) ∧
          endAct X.varpiEnd m = verschiebungInt m} :=
        ⟨(he r).1, by rw [verschiebungInt_apply_eq_verschiebung]; exact (he r).2⟩
      obtain ⟨z, hzη, hzl⟩ := hBij.surjOn her
      obtain ⟨x, hx, hxz⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_inf.1 hzη).2
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_prod.1 hx
      refine ⟨x.1, hx1, x.2, ?_, ?_⟩
      · have : (X.toGradedCartierModuleData j hc).nMk (x.1, x.2) = z := hxz
        rw [this]; exact hzη
      · have : (X.toGradedCartierModuleData j hc).nMk (x.1, x.2) = z := hxz
        rw [← hzl, ← this, lambda_nMk]
        rfl
    choose a ha b hη hab using hz

    have hPi : endAct X.varpiEnd m₀ ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ) :=
      (X.toGradedCartierModuleData j hc).varpi_mem i m₀ hm₀
    obtain ⟨w, hw, -⟩ := hbasis _ hPi

    set m₁ : CartierModule p X.F := m₀ - ∑ r, w r • a r with hm₁
    have hm₁mem : m₁ ∈ X.gradedPiece j (i : ℕ) := by
      refine (X.gradedPiece j (i : ℕ)).sub_mem hm₀ ?_
      refine AddSubgroup.sum_mem _ fun r _ => smul_mem_gradedPiece X j _ (w r) (a r) (ha r)
    have hPim : ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m₁ := by
      refine ⟨∑ r, WittVector.frobenius (w r) • b r, ?_⟩
      rw [hm₁, map_sub, hw, map_sum, map_sum]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [endAct_smul_witt, hab, smul_add, smul_verschiebungInt, add_sub_cancel_left]
    obtain ⟨g', hg'⟩ := hinj m₁ hm₁mem hPim
    refine tangent_mem_span X _ a (fun r => mem_S_of_nMk_mem j X hc L hL i (a r) (b r) (hη r))
      w m₀ g' ?_
    rw [hg', hm₁]; abel

end PointOnto

end

open PointOnto in

theorem solution
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K] [CharP K p] (j : Zp2 p →+* K)
    (X : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    X.lieZero j ≤ Submodule.span K (MvFormalGroup.CartierModule.tangent ''
        {a : MvFormalGroup.CartierModule p X.F |
          ∃ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0,
            (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ a}) ∧
    X.lieOne j ≤ Submodule.span K (MvFormalGroup.CartierModule.tangent ''
        {a : MvFormalGroup.CartierModule p X.F |
          ∃ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1,
            (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ a}) := by
  obtain ⟨h0, h1⟩ := PointOnto.exists_tangent_eq j X hc hX
  constructor
  · intro τ hτ
    obtain ⟨m, hm, rfl⟩ := h0 τ hτ
    exact PointOnto.key j X hc hX hX4 L hL 0 m hm
  · intro τ hτ
    obtain ⟨m, hm, rfl⟩ := h1 τ hτ
    exact PointOnto.key j X hc hX hX4 L hL 1 m hm

end S_CerednikDrinfeld_FormalODModule_lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed (solution)
