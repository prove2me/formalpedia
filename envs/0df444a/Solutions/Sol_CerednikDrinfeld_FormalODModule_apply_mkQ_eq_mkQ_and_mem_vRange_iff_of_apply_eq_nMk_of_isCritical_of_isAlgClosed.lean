-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2a79e8fb-a39e-55c8-a67c-7d5d099bc25a

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
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule CerednikDrinfeld.GradedCartierModuleData

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hX' : X'.IsSpecial j) (hX'4 : X'.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (hc' : IsCompl (X'.gradedPiece j 0) (X'.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (L' : (X'.toGradedCartierModuleData j hc').M →+ (X'.toGradedCartierModuleData j hc').NMod) (hL' : (X'.toGradedCartierModuleData j hc').IsCanonicalLMap L')
    (i : Fin 2)
    (hi : ∀ m ∈ X.gradedPiece j (i : ℕ), ∃ y : MvFormalGroup.CartierModule p X.F,
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (θη : (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
    (τ : (X.toGradedCartierModuleData j hc).LieQuot →ₗ[WittVector p K] (X'.toGradedCartierModuleData j hc').LieQuot) (hτ : Function.Injective τ)
    (hcompat : ∀ (m : (X.toGradedCartierModuleData j hc).M) (m' : (X'.toGradedCartierModuleData j hc').M) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (m', 0) →
        τ ((X.toGradedCartierModuleData j hc).vRange.mkQ m) = (X'.toGradedCartierModuleData j hc').vRange.mkQ m')
    (Θ : MvFormalGroup.CartierModule p X.F →ₗ[WittVector p K] MvFormalGroup.CartierModule p X'.F)
    (hΘ : ∀ (m : (X.toGradedCartierModuleData j hc).M) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (Θ m, 0)) :
    ∀ x ∈ X.gradedPiece j (i : ℕ),
      τ ((X.toGradedCartierModuleData j hc).vRange.mkQ x) = (X'.toGradedCartierModuleData j hc').vRange.mkQ (Θ x) ∧
      ((∃ y : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt y = x) ↔
        (∃ y' : MvFormalGroup.CartierModule p X'.F, MvFormalGroup.CartierModule.verschiebungInt y' = Θ x)) := by
  classical
  intro x hx
  have hV : ∀ f : CartierModule p X.F, verschiebungInt f = verschiebung f :=
    fun f => verschiebungInt_apply_eq_verschiebung f
  let Xs : SpecialFormalODModule p j := ⟨X, hX, hX4⟩
  have htors : ∀ m : CartierModule p X.F, endAct X.varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p j X hX hX4
  have hcrit : CritChart.IsCritical X j (i : ℕ) := by
    intro m hm; obtain ⟨g, hg⟩ := hi m hm; exact ⟨g, by rw [← hV]; exact hg⟩
  have hLi : ∀ x y : CartierModule p X.F, x ∈ X.gradedPiece j (i : ℕ) →
      verschiebungInt y = endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0) := fun x y hx hy =>
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL (i : ℕ) hi x y hx hy
  obtain ⟨hmem, -⟩ :=
    CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
      p j X hc L hL htors i hi hLi

  obtain ⟨e, he_inv, he_basis, -, -, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
      p j Xs (i : ℕ) hcrit

  have he_eta : ∀ r, (X.toGradedCartierModuleData j hc).nMk (e r, 0) ∈
      (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i := fun r =>
    (hmem _).2 ⟨e r, (he_inv r).1, by rw [hV]; exact (he_inv r).2, rfl⟩

  have he_tau : ∀ r, τ ((X.toGradedCartierModuleData j hc).vRange.mkQ (e r)) =
      (X'.toGradedCartierModuleData j hc').vRange.mkQ (Θ (e r)) := fun r =>
    hcompat (e r) (Θ (e r)) (he_eta r) (hΘ (e r) (he_eta r))

  obtain ⟨w, hw, -⟩ := he_basis x hx
  have h1 : τ ((X.toGradedCartierModuleData j hc).vRange.mkQ x) =
      (X'.toGradedCartierModuleData j hc').vRange.mkQ (Θ x) := by
    have hxM : (x : (X.toGradedCartierModuleData j hc).M) = ∑ r, w r • e r := hw
    have hlin : ((τ ∘ₗ (X.toGradedCartierModuleData j hc).vRange.mkQ) : (X.toGradedCartierModuleData j hc).M →ₗ[WittVector p K] _) =
        (X'.toGradedCartierModuleData j hc').vRange.mkQ ∘ₗ Θ → True := fun _ => trivial
    let f₁ : (X.toGradedCartierModuleData j hc).M →ₗ[WittVector p K] (X'.toGradedCartierModuleData j hc').LieQuot :=
      τ ∘ₗ (X.toGradedCartierModuleData j hc).vRange.mkQ
    let f₂ : (X.toGradedCartierModuleData j hc).M →ₗ[WittVector p K] (X'.toGradedCartierModuleData j hc').LieQuot :=
      (X'.toGradedCartierModuleData j hc').vRange.mkQ ∘ₗ Θ
    have hf : ∀ r, f₁ (e r) = f₂ (e r) := fun r => he_tau r
    show f₁ x = f₂ x
    have e1 : f₁ x = ∑ r, w r • f₁ (e r) := by
      rw [hxM]
      exact (map_sum f₁ (fun r => w r • e r) Finset.univ).trans
        (Finset.sum_congr rfl fun r _ => map_smul f₁ (w r) (e r))
    have e2 : f₂ x = ∑ r, w r • f₂ (e r) := by
      rw [hxM]
      exact (map_sum f₂ (fun r => w r • e r) Finset.univ).trans
        (Finset.sum_congr rfl fun r _ => map_smul f₂ (w r) (e r))
    rw [e1, e2]
    exact Finset.sum_congr rfl fun r _ => by rw [hf]
  refine ⟨h1, ?_⟩

  constructor
  · rintro ⟨y, hy⟩
    have h0 : (X.toGradedCartierModuleData j hc).vRange.mkQ x = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ((mem_vRange_iff _ _).2 ⟨y, hy⟩)
    have h0' : (X'.toGradedCartierModuleData j hc').vRange.mkQ (Θ x) = 0 := by rw [← h1, h0, map_zero]
    exact (mem_vRange_iff _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0')
  · rintro ⟨y', hy'⟩
    have h0' : (X'.toGradedCartierModuleData j hc').vRange.mkQ (Θ x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ((mem_vRange_iff _ _).2 ⟨y', hy'⟩)
    have h0 : (X.toGradedCartierModuleData j hc).vRange.mkQ x = 0 := by
      apply hτ
      rw [h1, h0', map_zero]
    exact (mem_vRange_iff _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)

end S_CerednikDrinfeld_FormalODModule_apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed (solution)
