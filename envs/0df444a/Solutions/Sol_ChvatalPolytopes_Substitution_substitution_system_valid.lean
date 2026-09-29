-- Prove2me | solution 1 for ChvatalPolytopes.Substitution.substitution_system_valid
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:02:59.017485+00:00
-- url     : https://prove2.me/submissions/f2acd170-c127-48a6-99ab-10531aa554b0

import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Substitution_substitute

namespace ChvatalPolytopes.Substitution

theorem aux_ssv_mem {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {J : Type*} (a : J → V → ℝ) (b : J → ℝ)
    (h : {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i} = Shared.stablePolytope G)
    (t : Finset V) (ht : G.IsIndepSet (t : Set V)) (i : J) :
    ∑ u, a i u * Shared.incidenceVector t u ≤ b i := by
  have hm : Shared.incidenceVector t ∈ Shared.stablePolytope G :=
    subset_convexHull ℝ _ ⟨t, ht, rfl⟩
  rw [← h] at hm
  exact hm.2 i

end ChvatalPolytopes.Substitution

open ChvatalPolytopes.Substitution

theorem solution {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype V₂] [DecidableEq V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → V₁ → ℝ) (b₁ : J₁ → ℝ) (a₂ : J₂ → V₂ → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : V₁ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} = ChvatalPolytopes.Shared.stablePolytope G₁)
    (h₂ : {x : V₂ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ j, ∑ u, a₂ j u * x u ≤ b₂ j} = ChvatalPolytopes.Shared.stablePolytope G₂)
    (v : V₁) :
    ∀ x ∈ ChvatalPolytopes.Shared.stableVectors (substitute G₁ v G₂),
      (∀ u, 0 ≤ x u) ∧
      ∀ i j, max (a₁ i v) 0 * ∑ u : V₂, a₂ j u * x (.inr u)
          + b₂ j * ∑ w : {u : V₁ // u ≠ v}, a₁ i w * x (.inl w) ≤ b₁ i * b₂ j := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨fun u => by
    unfold ChvatalPolytopes.Shared.incidenceVector; split_ifs <;> norm_num, fun i j => ?_⟩
  set S2 : Finset V₂ := Finset.univ.filter (fun u => Sum.inr u ∈ s) with hS2
  set T : Finset V₁ := Finset.univ.filter (fun w => ∃ h : w ≠ v, Sum.inl ⟨w, h⟩ ∈ s) with hT
  have hA : ∑ u : V₂, a₂ j u * ChvatalPolytopes.Shared.incidenceVector s (.inr u)
      = ∑ u, a₂ j u * ChvatalPolytopes.Shared.incidenceVector S2 u := by
    apply Finset.sum_congr rfl
    intro u _
    simp [ChvatalPolytopes.Shared.incidenceVector, S2]
  have hbj : 0 ≤ b₂ j := by
    have := aux_ssv_mem G₂ a₂ b₂ h₂ ∅ (by simp) j
    simpa [ChvatalPolytopes.Shared.incidenceVector] using this
  have hS2ind : G₂.IsIndepSet (S2 : Set V₂) := by
    intro p hp q hq hpq
    simp only [S2, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    have := hs hp hq (by simpa using hpq)
    simpa using this
  have hAle := aux_ssv_mem G₂ a₂ b₂ h₂ S2 hS2ind j
  have hTind : G₁.IsIndepSet (T : Set V₁) := by
    intro p hp q hq hpq
    simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hq1, hq2⟩ := hq
    have := hs hp2 hq2 (by simpa [Subtype.ext_iff] using hpq)
    simpa using this
  have hB : ∑ u, a₁ i u * ChvatalPolytopes.Shared.incidenceVector T u
      = ∑ w : {u : V₁ // u ≠ v}, a₁ i w * ChvatalPolytopes.Shared.incidenceVector s (.inl w) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ v]
    have hv : v ∉ T := by simp [T]
    rw [show ChvatalPolytopes.Shared.incidenceVector T v = 0 by
      simp [ChvatalPolytopes.Shared.incidenceVector, hv]]
    simp only [mul_zero, zero_add]
    apply Finset.sum_congr rfl
    rintro ⟨w, hw⟩ _
    simp [ChvatalPolytopes.Shared.incidenceVector, T, hw]
  have hBle := aux_ssv_mem G₁ a₁ b₁ h₁ T hTind i
  rw [hB] at hBle
  rw [hA]
  set A := ∑ u, a₂ j u * ChvatalPolytopes.Shared.incidenceVector S2 u
  set B := ∑ w : {u : V₁ // u ≠ v}, a₁ i w * ChvatalPolytopes.Shared.incidenceVector s (.inl w)
  rcases le_or_gt (a₁ i v) 0 with hav | hav
  · rw [max_eq_right hav, zero_mul, zero_add, mul_comm (b₁ i)]
    exact mul_le_mul_of_nonneg_left hBle hbj
  rw [max_eq_left hav.le]
  rcases S2.eq_empty_or_nonempty with hE | ⟨u0, hu0⟩
  · have hA0 : A = 0 := by
      simp [A, hE, ChvatalPolytopes.Shared.incidenceVector]
    rw [hA0, mul_zero, zero_add, mul_comm (b₁ i)]
    exact mul_le_mul_of_nonneg_left hBle hbj
  · -- insert v into T
    have hu0' : Sum.inr u0 ∈ s := by simpa [S2] using hu0
    have hTvind : G₁.IsIndepSet ((insert v T : Finset V₁) : Set V₁) := by
      rw [Finset.coe_insert]
      refine hTind.insert ?_
      intro w hw hne
      simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
      obtain ⟨hw1, hw2⟩ := hw
      have := hs hu0' hw2 (by simp)
      simp at this
      exact ⟨fun h => this (G₁.adj_symm h), this⟩
    have hB2 := aux_ssv_mem G₁ a₁ b₁ h₁ (insert v T) hTvind i
    have hB2' : ∑ u, a₁ i u * ChvatalPolytopes.Shared.incidenceVector (insert v T) u
        = a₁ i v + B := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ v]
      congr 1
      · simp [ChvatalPolytopes.Shared.incidenceVector]
      · apply Finset.sum_congr rfl
        rintro ⟨w, hw⟩ _
        simp [ChvatalPolytopes.Shared.incidenceVector, T, hw]
    rw [hB2'] at hB2
    nlinarith [mul_le_mul_of_nonneg_left hAle hav.le, mul_le_mul_of_nonneg_left hB2 hbj]
