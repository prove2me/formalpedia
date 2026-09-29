-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFormalCompletionAlong.id_and_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/82e447d4-cf13-5401-af5f-d0ec6d2f196d

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp.CerednikDrinfeld.QM"
open MvPowerSeries

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "tree QM.IsFormalCompletionAlong"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt IsFormalCompletionAlong"
namespace FormalCompletionFunctoriality
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

theorem isAdicComplete_of_pow_eq_bot {C : Type*} [CommRing C] (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) :
    IsAdicComplete J C := by
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx N
    rw [hN] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f N, fun m => by
    by_cases hm : m ≤ N
    · exact hf hm
    · push Not at hm
      have h1 : f N ≡ f m [SMOD (J ^ N • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = N + (m - N) by omega, pow_add, hN, Ideal.bot_mul]; simp
      have h3 : (J ^ N • ⊤ : Submodule C C) = ⊥ := by rw [hN]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem nilEval_mem {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ)
    (φ : MvPowerSeries σ B) (hφ : MvPowerSeries.constantCoeff φ = 0) (s : σ → B') (hs : ∀ i, s i ∈ J) :
    MvFormalGroup.nilEval n φ s ∈ J := by
  classical
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    have : MvPolynomial.coeff 0 (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) φ) = 0 := by
      rw [MvPowerSeries.coeff_trunc', if_pos (show (0 : σ →₀ ℕ) ≤ Finsupp.equivFunOnFinite.symm (fun _ => n) from bot_le),
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
    rw [this, map_zero, zero_mul]
    exact Ideal.zero_mem _
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hd (Finsupp.ext hcon)
    have hmem : i ∈ d.support := Finsupp.mem_support_iff.mpr hi
    refine Ideal.mul_mem_left _ _ ?_
    rw [← Finset.mul_prod_erase _ _ hmem]
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.pow_mem_of_mem J (hs i) _ (Nat.pos_of_ne_zero hi)

end CerednikDrinfeld.QM.FormalCompletionFunctoriality

open CerednikDrinfeld.QM.FormalCompletionFunctoriality in
theorem solution
    {B : Type} [CommRing B] {A A' A'' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {f'' : A'' ⟶ Spec (CommRingCat.of B)}
    {g g' g'' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (θ'' : RelativeGroupLaw.FormalCoordinates f'' g'') :
    IsFormalCompletionAlong θ θ (𝟙 A) (Category.id_comp f) (fun i => MvPowerSeries.X i) ∧
    ∀ (h : A ⟶ A') (hh : h ≫ f' = f) (h' : A' ⟶ A'') (hh' : h' ≫ f'' = f') (hhh' : (h ≫ h') ≫ f'' = f)
      (φ : Fin g' → MvPowerSeries (Fin g) B) (φ' : Fin g'' → MvPowerSeries (Fin g') B),
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
      IsFormalCompletionAlong θ θ' h hh φ → IsFormalCompletionAlong θ' θ'' h' hh' φ' →
      IsFormalCompletionAlong θ θ'' (h ≫ h') hhh' (fun i => MvPowerSeries.subst φ (φ' i)) := by
  classical
  refine ⟨?_, ?_⟩
  ·
    intro B' _ _ J n hJ s hs
    have hval : (fun i => MvFormalGroup.nilEval n (MvPowerSeries.X i : MvPowerSeries (Fin g) B) s) = s := by
      funext i
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs, MvFormalGroup.adicEval_X]
    rw [hval]
    apply Subtype.ext
    show (θ B' s).1 = (θ B' s).1 ≫ 𝟙 A
    rw [Category.comp_id]
  ·
    intro h hh h' hh' hhh' φ φ' hφ H H' B' _ _ J n hJ s hs
    haveI : IsAdicComplete J B' := isAdicComplete_of_pow_eq_bot J hJ
    have hsrad : ∀ j, s j ∈ J.radical := fun j => Ideal.le_radical (hs j)

    set t : Fin g' → B' := fun j => MvFormalGroup.nilEval n (φ j) s with ht
    have htmem : ∀ j, t j ∈ J := fun j => nilEval_mem J n (φ j) (hφ j) s hs

    have hval : (fun i => MvFormalGroup.nilEval n (MvPowerSeries.subst φ (φ' i)) s) =
        fun i => MvFormalGroup.nilEval n (φ' i) t := by
      funext i
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs,
        MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ t htmem,
        MvFormalGroup.adicEval_subst J hsrad (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ)]
      congr 1
      funext j
      show _ = MvFormalGroup.nilEval n (φ j) s
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs]
    rw [hval, H' B' J n hJ t htmem, show θ' B' t = mapPt h hh (θ B' s) from H B' J n hJ s hs]
    apply Subtype.ext
    show ((θ B' s).1 ≫ h) ≫ h' = (θ B' s).1 ≫ (h ≫ h')
    rw [Category.assoc]

end S_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp (solution)
