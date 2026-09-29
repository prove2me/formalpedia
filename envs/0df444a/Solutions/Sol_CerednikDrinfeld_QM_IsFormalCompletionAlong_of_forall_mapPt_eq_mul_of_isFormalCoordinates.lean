-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c8bab30d-d522-572e-ae84-b6b12913fe57

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

namespace P2MW.S_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates.CerednikDrinfeld.QM"
open MvPowerSeries

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "tree QM.IsFormalCompletionAlong"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt IsFormalCompletionAlong"
namespace FormalCompletionAdditivity
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

end CerednikDrinfeld.QM.FormalCompletionAdditivity

open CerednikDrinfeld.QM.FormalCompletionAdditivity in
theorem solution
    {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (L' : RelativeGroupLaw B f') (F' : MvFormalGroup g' B) (hθ' : L'.IsFormalCoordinates F' θ')
    (h₁ h₂ h₃ : A ⟶ A') (hh₁ : h₁ ≫ f' = f) (hh₂ : h₂ ≫ f' = f) (hh₃ : h₃ ≫ f' = f)
    (hmul : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
      mapPt h₃ hh₃ P = L'.mul (Scheme.specOver (𝒪 := B) B') (mapPt h₁ hh₁ P) (mapPt h₂ hh₂ P))
    (φ₁ φ₂ : Fin g' → MvPowerSeries (Fin g) B)
    (hφ₁ : ∀ i, MvPowerSeries.constantCoeff (φ₁ i) = 0) (hφ₂ : ∀ i, MvPowerSeries.constantCoeff (φ₂ i) = 0)
    (H₁ : IsFormalCompletionAlong θ θ' h₁ hh₁ φ₁) (H₂ : IsFormalCompletionAlong θ θ' h₂ hh₂ φ₂) :
    IsFormalCompletionAlong θ θ' h₃ hh₃
      (fun i => MvPowerSeries.subst (Sum.elim φ₁ φ₂) (F'.toPowerSeries i)) := by
  classical
  intro B' _ _ J n hJ s hs
  haveI : IsAdicComplete J B' := isAdicComplete_of_pow_eq_bot J hJ
  have hsrad : ∀ j, s j ∈ J.radical := fun j => Ideal.le_radical (hs j)

  set t₁ : Fin g' → B' := fun j => MvFormalGroup.nilEval n (φ₁ j) s with ht₁
  set t₂ : Fin g' → B' := fun j => MvFormalGroup.nilEval n (φ₂ j) s with ht₂
  have ht₁mem : ∀ j, t₁ j ∈ J := fun j => nilEval_mem J n (φ₁ j) (hφ₁ j) s hs
  have ht₂mem : ∀ j, t₂ j ∈ J := fun j => nilEval_mem J n (φ₂ j) (hφ₂ j) s hs
  have htmem : ∀ c, Sum.elim t₁ t₂ c ∈ J := by
    rintro (j | j)
    · exact ht₁mem j
    · exact ht₂mem j

  have hval : (fun i => MvFormalGroup.nilEval n (MvPowerSeries.subst (Sum.elim φ₁ φ₂) (F'.toPowerSeries i)) s) =
      F'.nilMul n t₁ t₂ := by
    funext i
    rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs,
      MvFormalGroup.adicEval_subst_elim F' J hsrad hφ₁ hφ₂ i]
    show _ = MvFormalGroup.nilEval n (F'.toPowerSeries i) (Sum.elim t₁ t₂)
    rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ (Sum.elim t₁ t₂) htmem]
    congr 1
    funext c
    rcases c with j | j
    · show MvFormalGroup.adicEval J s (φ₁ j) = MvFormalGroup.nilEval n (φ₁ j) s
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs]
    · show MvFormalGroup.adicEval J s (φ₂ j) = MvFormalGroup.nilEval n (φ₂ j) s
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs]
  rw [hval, (hθ'.2 B' J n hJ).2.2.2 t₁ t₂ ht₁mem ht₂mem,
    show θ' B' t₁ = mapPt h₁ hh₁ (θ B' s) from H₁ B' J n hJ s hs,
    show θ' B' t₂ = mapPt h₂ hh₂ (θ B' s) from H₂ B' J n hJ s hs, hmul]

end S_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates (solution)
