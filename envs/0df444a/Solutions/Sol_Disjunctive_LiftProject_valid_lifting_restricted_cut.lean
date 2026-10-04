-- Prove2me | solution 1 for Disjunctive.LiftProject.valid_lifting_restricted_cut
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:17:47.855015+00:00
-- url     : https://prove2.me/submissions/9e701cb7-5bbc-482d-87b5-c283a3f40974

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic

set_option autoImplicit false

open Disjunctive.LiftProject in
theorem solution {n : ℕ} {M : Type*} [Fintype M]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (MR : Finset M) (R : Finset (Fin n))
    (j : Fin n) (hj : j ∈ R) (αR : Fin n → ℝ) (uR vR : M → ℝ) (u0R v0R β : ℝ)
    (hFeas : IsCGLPRFeasible Atil btil MR R j αR uR u0R vR v0R β) :
    ∃ α : Fin n → ℝ, ∃ u v : M ⊕ Fin n → ℝ,
      (∀ i ∈ R, α i = αR i) ∧
        (∀ i ∉ R, α i = max (Alpha1 Atil uR MR i) (Alpha2 Atil vR MR i)) ∧
        IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α u u0R v v0R β := by
  classical
  obtain ⟨h1, h2, h3, h4, hu, hv⟩ := hFeas
  have key : ∀ (w : M → ℝ) (c : M → ℝ),
      ∑ ρ, (if ρ ∈ MR then w ρ else 0) * c ρ = ∑ ρ ∈ MR, w ρ * c ρ := by
    intro w c
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  let α : Fin n → ℝ := fun i =>
    if i ∈ R then αR i else max (Alpha1 Atil uR MR i) (Alpha2 Atil vR MR i)
  refine ⟨α,
    Sum.elim (fun ρ => if ρ ∈ MR then uR ρ else 0)
      (fun k => α k - Alpha1 Atil uR MR k + (if k = j then u0R else 0)),
    Sum.elim (fun ρ => if ρ ∈ MR then vR ρ else 0)
      (fun k => α k - Alpha2 Atil vR MR k - (if k = j then v0R else 0)), ?_, ?_, ?_⟩
  · intro i hi
    simp [α, hi]
  · intro i hi
    simp [α, hi]
  have hAl : ∀ (ρ : M) (i : Fin n), AtilExt Atil (Sum.inl ρ) i = Atil ρ i := fun _ _ => rfl
  have hAr : ∀ (k i : Fin n), AtilExt Atil (Sum.inr k) i = if k = i then (1 : ℝ) else 0 :=
    fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [Fintype.sum_sum_type]
    simp only [hAl, hAr, Sum.elim_inl, Sum.elim_inr, key]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    unfold Alpha1
    ring
  · intro i
    rw [Fintype.sum_sum_type]
    simp only [hAl, hAr, Sum.elim_inl, Sum.elim_inr, key]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    unfold Alpha2
    ring
  · rw [Fintype.sum_sum_type]
    simp only [BtilExt, Sum.elim_inl, Sum.elim_inr, key, mul_zero, Finset.sum_const_zero,
      add_zero]
    exact h3
  · rw [Fintype.sum_sum_type]
    simp only [BtilExt, Sum.elim_inl, Sum.elim_inr, key, mul_zero, Finset.sum_const_zero,
      add_zero]
    exact h4
  · intro x
    rcases x with ρ | k
    · simp only [Sum.elim_inl, Pi.zero_apply]
      split_ifs
      · exact hu ρ
      · exact le_rfl
    · simp only [Sum.elim_inr, Pi.zero_apply]
      by_cases hk : k ∈ R
      · have e := h1 k hk
        have : α k = αR k := by simp [α, hk]
        rw [this]
        unfold Alpha1
        linarith
      · have hkj : k ≠ j := fun h => hk (h ▸ hj)
        have : α k = max (Alpha1 Atil uR MR k) (Alpha2 Atil vR MR k) := by simp [α, hk]
        rw [this, if_neg hkj]
        have := le_max_left (Alpha1 Atil uR MR k) (Alpha2 Atil vR MR k)
        linarith
  · intro x
    rcases x with ρ | k
    · simp only [Sum.elim_inl, Pi.zero_apply]
      split_ifs
      · exact hv ρ
      · exact le_rfl
    · simp only [Sum.elim_inr, Pi.zero_apply]
      by_cases hk : k ∈ R
      · have e := h2 k hk
        have : α k = αR k := by simp [α, hk]
        rw [this]
        unfold Alpha2
        linarith
      · have hkj : k ≠ j := fun h => hk (h ▸ hj)
        have : α k = max (Alpha1 Atil uR MR k) (Alpha2 Atil vR MR k) := by simp [α, hk]
        rw [this, if_neg hkj]
        have := le_max_right (Alpha1 Atil uR MR k) (Alpha2 Atil vR MR k)
        linarith
