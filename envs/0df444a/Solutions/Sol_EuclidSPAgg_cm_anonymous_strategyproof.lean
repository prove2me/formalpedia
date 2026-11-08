-- Prove2me | solution 1 for EuclidSPAgg.cm_anonymous_strategyproof
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:32:44.886194+00:00
-- url     : https://prove2.me/submissions/c271e029-6d97-4f6e-acef-02f8bcf7ed7f

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_CM
open RBMSensitivity (E)

namespace Aux_CMSP
open EuclidSPAgg ImpactInvesting.Portfolio

theorem os_mem_iff {N : ℕ} (x : Fin N → ℝ) (k : Fin N) (s : Set ℝ) [DecidablePred fun j => x j ∈ s] (hs : IsLowerSet s) :
    orderStat x k ∈ s ↔ (k : ℕ) < (Finset.univ.filter (fun j => x j ∈ s)).card := by
  set σ := Tuple.sort x
  have hmono : Monotone (x ∘ σ) := Tuple.monotone_sort x
  have hcard : (Finset.univ.filter (fun j => x j ∈ s)).card =
      (Finset.univ.filter (fun p => x (σ p) ∈ s)).card := by
    apply Finset.card_bij (fun j _ => σ.symm j)
    · intro j hj; simpa using hj
    · intro a _ b _ h; simpa using h
    · intro p hp; exact ⟨σ p, by simpa using hp, by simp⟩
  rw [hcard]
  unfold orderStat
  constructor
  · intro hk
    have : Finset.Iic k ⊆ Finset.univ.filter (fun p => x (σ p) ∈ s) := by
      intro p hp
      rw [Finset.mem_Iic] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs (hmono hp) hk
    have h2 := Finset.card_le_card this
    rw [Fin.card_Iic] at h2
    omega
  · intro hk
    by_contra hk'
    have : Finset.univ.filter (fun p => x (σ p) ∈ s) ⊆ Finset.Iio k := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [Finset.mem_Iio]
      by_contra hpk
      push_neg at hpk
      exact hk' (hs (hmono hpk) hp)
    have h2 := Finset.card_le_card this
    rw [Fin.card_Iio] at h2
    omega

theorem os_perm {N : ℕ} (x : Fin N → ℝ) (π : Equiv.Perm (Fin N)) (k : Fin N) :
    orderStat (x ∘ π) k = orderStat x k := by
  classical
  have hc : ∀ m : ℝ, (Finset.univ.filter (fun j => (x ∘ π) j ∈ Set.Iio m)).card =
      (Finset.univ.filter (fun j => x j ∈ Set.Iio m)).card := by
    intro m
    apply Finset.card_bij (fun j _ => π j)
    · intro j hj; simpa using hj
    · intro a _ b _ h; simpa using h
    · intro p hp; exact ⟨π.symm p, by simpa using hp, by simp⟩
  have key : ∀ m : ℝ, orderStat (x ∘ π) k < m ↔ orderStat x k < m := by
    intro m
    have h1 := os_mem_iff (x ∘ π) k (Set.Iio m) (isLowerSet_Iio _)
    have h2 := os_mem_iff x k (Set.Iio m) (isLowerSet_Iio _)
    rw [hc] at h1
    exact h1.trans h2.symm
  apply le_antisymm
  · by_contra h; push_neg at h
    exact lt_irrefl _ ((key _).mpr h)
  · by_contra h; push_neg at h
    exact lt_irrefl _ ((key _).mp h)

theorem os_sp {N : ℕ} (x : Fin N → ℝ) (k i : Fin N) (a b : ℝ) :
    |a - orderStat (Function.update x i a) k| ≤ |a - orderStat (Function.update x i b) k| := by
  classical
  set m := orderStat (Function.update x i a) k with hm
  set m' := orderStat (Function.update x i b) k with hm'
  rcases lt_trichotomy a m with h | h | h
  · have : m ≤ m' := by
      by_contra hc; push_neg at hc
      have h1 := (os_mem_iff (Function.update x i b) k (Set.Iio m) (isLowerSet_Iio _)).mp hc
      have h2 : ¬ (m ∈ Set.Iio m) := lt_irrefl m
      rw [hm, os_mem_iff _ k _ (isLowerSet_Iio _), ← hm] at h2
      apply h2
      refine lt_of_lt_of_le h1 (Finset.card_le_card ?_)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iio] at hj ⊢
      by_cases hji : j = i
      · subst hji; simpa using h
      · simpa [hji] using hj
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
  · rw [← h]; simp
  · have : m' ≤ m := by
      by_contra hc; push_neg at hc
      have h1 : m ∈ Set.Iic m := le_refl m
      rw [hm, os_mem_iff _ k _ (isLowerSet_Iic _), ← hm] at h1
      have h2 : ¬ (m' ∈ Set.Iic m) := not_le.mpr hc
      rw [hm', os_mem_iff _ k _ (isLowerSet_Iic _)] at h2
      apply h2
      refine lt_of_lt_of_le h1 (Finset.card_le_card ?_)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iic] at hj ⊢
      by_cases hji : j = i
      · subst hji; simp at hj; linarith
      · simpa [hji] using hj
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith

theorem cm_apply (n d : ℕ) (hn : 0 < n) (x : Fin n → E d) (j : Fin d) :
    CM n d x j = orderStat (fun i => x i j) ⟨(n - 1) / 2, by omega⟩ := by
  simp only [CM, dif_pos hn, Q]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, Pi.single_apply]

end Aux_CMSP

open EuclidSPAgg ImpactInvesting.Portfolio Aux_CMSP in
theorem solution (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) :
    IsStrategyproof (CM n d) ∧ IsAnonymous (CM n d) := by
  have hn0 : 0 < n := by omega
  constructor
  · intro i x a b
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    simp only [PiLp.sub_apply, cm_apply n d hn0, Real.norm_eq_abs]
    have e : ∀ c : E d, (fun i' => (Function.update x i c) i' j) =
        Function.update (fun i' => x i' j) i (c j) := by
      intro c; funext i'
      by_cases h : i' = i
      · subst h; simp
      · simp [h]
    rw [e a, e b]
    exact pow_le_pow_left₀ (abs_nonneg _) (os_sp _ _ i _ _) 2
  · intro π x
    ext j
    rw [cm_apply n d hn0, cm_apply n d hn0]
    exact os_perm (fun i => x i j) π _
