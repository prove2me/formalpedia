-- Prove2me | solution 1 for ExactParallelSampling.QuasiUniform.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:38:14.507317+00:00
-- url     : https://prove2.me/submissions/ac6b771e-be35-4353-97a6-e1856795c72a

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions

noncomputable section
open Classical

namespace EPSLemma41Aux
open ExactParallelSampling.QuasiUniform

variable {E α : Type*} [Fintype E] [Fintype α]

theorem count_nonneg (p : (E → α) → ℝ) (hp : IsDist p) (S : Finset E) (y : E → α) :
    0 ≤ count p S y :=
  Finset.sum_nonneg fun x _ => hp.1 x

theorem count_congr (p : (E → α) → ℝ) (S : Finset E) (y y' : E → α)
    (h : ∀ j ∈ S, y j = y' j) : count p S y = count p S y' := by
  unfold count
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  exact ⟨fun hx j hj => (hx j hj).trans (h j hj), fun hx j hj => (hx j hj).trans (h j hj).symm⟩

theorem count_mono (p : (E → α) → ℝ) (hp : IsDist p) (S S' : Finset E) (hS : S' ⊆ S)
    (y : E → α) : count p S y ≤ count p S' y := by
  unfold count
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hp.1 x)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact fun j hj => hx j (hS hj)

theorem count_eq_marg (p : (E → α) → ℝ) (S : Finset E) (y : E → α) :
    count p S y = marg p S (S.restrict y) := by
  unfold count marg
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  constructor
  · intro h; funext ⟨j, hj⟩; exact h j hj
  · intro h j hj; exact congrFun h ⟨j, hj⟩

theorem marg_le_count (p : (E → α) → ℝ) (hp : IsDist p) (S : Finset E) (w : ↥S → α)
    (j : E) (hj : j ∈ S) : marg p S w ≤ count p {j} (fun _ => w ⟨j, hj⟩) := by
  unfold count marg
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hp.1 x)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hx ⊢
  intro i hi; subst hi; rw [← hx]; rfl

theorem marg_singleton (p : (E → α) → ℝ) (j : E) (w : ↥({j} : Finset E) → α) :
    marg p {j} w = count p {j} (fun _ => w ⟨j, Finset.mem_singleton_self j⟩) := by
  unfold count marg
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  constructor
  · intro h i hi
    rw [Finset.mem_singleton] at hi; subst hi
    rw [← h]; rfl
  · intro h
    funext ⟨i, hi⟩
    have := Finset.mem_singleton.1 hi; subst this
    exact h i (Finset.mem_singleton_self i)

theorem suppCard_singleton (p : (E → α) → ℝ) (j : E) : suppCard p {j} = s p j := by
  unfold suppCard s supp singleSupp
  refine Finset.card_bij' (fun w _ => w ⟨j, Finset.mem_singleton_self j⟩) (fun a _ => fun _ => a)
    ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rwa [marg_singleton] at hw
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rwa [marg_singleton]
  · intro w _
    funext ⟨i, hi⟩
    have := Finset.mem_singleton.1 hi; subst this; rfl
  · intro a _; rfl

theorem count_pos_eq (p : (E → α) → ℝ) (hp : IsQuasiUniform p) (S : Finset E) (y : E → α)
    (h : 0 < count p S y) : count p S y = 1 / (suppCard p S : ℝ) := by
  rw [count_eq_marg] at h ⊢
  exact hp.2 S _ (by simp [supp, h])

theorem count_singleton_eq (p : (E → α) → ℝ) (hp : IsQuasiUniform p) (j : E) (y : E → α)
    (hy : y j ∈ singleSupp p j) : count p {j} y = 1 / (s p j : ℝ) := by
  have hpos : 0 < count p {j} y := by
    simp only [singleSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rwa [count_congr p {j} y (fun _ => y j) (fun i hi => by rw [Finset.mem_singleton.1 hi])]
  rw [count_pos_eq p hp _ _ hpos, suppCard_singleton]

end EPSLemma41Aux

namespace ExactParallelSampling.QuasiUniform
open EPSLemma41Aux

theorem solution_aux {E α : Type*} [Fintype E] [Fintype α] (p : (E → α) → ℝ)
    (hp : IsQuasiUniform p) (F : Finset E) (z : E → α) (hz : ∀ j ∈ F, z j ∈ singleSupp p j) :
    (IsIndep p F ↔ count p F z = ∏ j ∈ F, 1 / (s p j : ℝ)) := by
  constructor
  · intro hI
    rw [hI z]
    exact Finset.prod_congr rfl fun j hj => count_singleton_eq p hp j z (hz j hj)
  · intro h y
    have hs : ∀ j ∈ F, 0 < s p j := fun j hj => Finset.card_pos.2 ⟨_, hz j hj⟩
    have hprodpos : 0 < ∏ j ∈ F, 1 / (s p j : ℝ) :=
      Finset.prod_pos fun j hj => by have := hs j hj; positivity
    have hcz := count_pos_eq p hp F z (h ▸ hprodpos)
    -- |Ω_F| = ∏ s_j
    have hcard : suppCard p F = ∏ j ∈ F, s p j := by
      have h1 : (1 : ℝ) / (suppCard p F : ℝ) = 1 / ((∏ j ∈ F, s p j : ℕ) : ℝ) := by
        rw [← hcz, h, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]
      have h2 := h1
      simp only [one_div, inv_inj] at h2
      exact_mod_cast h2
    -- Ω_F is the full product of the singleton supports
    set Pi := Fintype.piFinset (fun i : ↥F => singleSupp p i) with hPi
    have hsub : supp p F ⊆ Pi := by
      intro w hw
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [Fintype.mem_piFinset]
      intro ⟨j, hj⟩
      simp only [singleSupp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_lt_of_le hw (marg_le_count p hp.1 F w j hj)
    have hPicard : Pi.card = ∏ j ∈ F, s p j := by
      rw [hPi, Fintype.card_piFinset]
      exact Finset.prod_coe_sort F (fun j => s p j)
    have heq : supp p F = Pi :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hPicard, ← hcard]; rfl)
    by_cases hy : ∀ j ∈ F, y j ∈ singleSupp p j
    · have hmem : F.restrict y ∈ supp p F := by
        rw [heq, Fintype.mem_piFinset]
        intro ⟨j, hj⟩; exact hy j hj
      rw [count_eq_marg p F y, hp.2 F _ hmem, Finset.prod_congr rfl
        (fun j hj => count_singleton_eq p hp j y (hy j hj)), ← h, hcz]
    · push_neg at hy
      obtain ⟨j, hj, hyj⟩ := hy
      have h0 : count p {j} y = 0 := by
        have hn := count_nonneg p hp.1 {j} y
        refine le_antisymm (not_lt.1 fun hlt => hyj ?_) hn
        simp only [singleSupp, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [count_congr p {j} (fun _ => y j) y (fun i hi => by rw [Finset.mem_singleton.1 hi])]
      rw [Finset.prod_eq_zero hj h0]
      refine le_antisymm ?_ (count_nonneg p hp.1 F y)
      rw [← h0]
      exact count_mono p hp.1 F {j} (Finset.singleton_subset_iff.2 hj) y

end ExactParallelSampling.QuasiUniform

open ExactParallelSampling.QuasiUniform

theorem solution {E α : Type*} [Fintype E] [Fintype α] (p : (E → α) → ℝ)
    (hp : IsQuasiUniform p) (F : Finset E) (z : E → α) (hz : ∀ j ∈ F, z j ∈ singleSupp p j) :
    (IsIndep p F ↔ count p F z = ∏ j ∈ F, 1 / (s p j : ℝ)) ∧
    (singletonQueries (E := E) (α := α)).card ≤ Fintype.card E * Fintype.card α ∧
    (∀ ans : (Finset E × (E → α)) → ℝ,
      (∀ Q ∈ singletonQueries (E := E) (α := α), ans Q = count p Q.1 Q.2) →
      ∀ j, supportsFromAnswers ans j = singleSupp p j) := by
  refine ⟨solution_aux p hp F z hz, ?_, ?_⟩
  · unfold singletonQueries
    refine (Finset.card_image_le).trans ?_
    simp [Finset.card_univ, Fintype.card_prod]
  · intro ans hans j
    unfold supportsFromAnswers singleSupp
    refine Finset.filter_congr fun a _ => ?_
    have hQ : (({j}, fun _ => a) : Finset E × (E → α)) ∈ singletonQueries (E := E) (α := α) := by
      unfold singletonQueries
      exact Finset.mem_image.2 ⟨(j, a), Finset.mem_univ _, rfl⟩
    rw [hans _ hQ]
