-- Prove2me | solution 1 for BoydADMM.Prox.prox_indicator_eq_projection
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:24:02.267105+00:00
-- url     : https://prove2.me/submissions/ca691196-55f0-499c-bcfb-15ac3b0ae471

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix


namespace BoydADMM.Prox

theorem proj_iInf_of {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (v z : EuclideanSpace ℝ (Fin n)) (h : IsProjection C v z) :
    ‖v - z‖ = ⨅ w : C, ‖v - w‖ := by
  obtain ⟨hz, hmin⟩ := h
  have : Nonempty C := ⟨⟨z, hz⟩⟩
  apply le_antisymm
  · exact le_ciInf fun w => hmin w w.2
  · exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨z, hz⟩ : C)

theorem indicator_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_ne : C.Nonempty)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∃! x, IsProjection C v x) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ x, IsProx C (fun _ => 0) ρ v x ↔ IsProjection C v x := by
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz, hzeq⟩ := exists_norm_eq_iInf_of_complete_convex hC_ne hC_closed.isComplete
      hC_convex v
    refine ⟨z, ⟨hz, fun w hw => ?_⟩, ?_⟩
    · rw [hzeq]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨w, hw⟩ : C)
    · intro y hy
      have h1 := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hy.1).1 (proj_iInf_of C v y hy) z hz
      have h2 := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hz).1 hzeq y hy.1
      have h3 : ‖y - z‖ ^ 2 = inner ℝ (v - y) (z - y) + inner ℝ (v - z) (y - z) := by
        have ea : y - z = (v - z) - (v - y) := by abel
        have eb : z - y = (v - y) - (v - z) := by abel
        rw [ea, eb]
        generalize v - y = a
        generalize v - z = b
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right]
        linarith [real_inner_comm a b]
      have : ‖y - z‖ ^ 2 ≤ 0 := by linarith
      have : ‖y - z‖ = 0 := by nlinarith [norm_nonneg (y - z)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · intro ρ hρ x
    unfold IsProx
    simp only [zero_add]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun w hw => ?_⟩
      have := h w hw
      have h2 : ‖x - v‖ ^ 2 ≤ ‖w - v‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left this (le_of_lt (div_pos two_pos hρ))
        field_simp at this; nlinarith
      rw [norm_sub_rev v x, norm_sub_rev v w]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun w hw => ?_⟩
      have := h w hw
      rw [norm_sub_rev v x, norm_sub_rev v w] at this
      have : ‖x - v‖ ^ 2 ≤ ‖w - v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith

theorem orthant_core {n : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    IsProx (nonnegOrthant n) (fun _ => 0) ρ v x ↔ x = posPartVec v := by
  have nsq : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
    intro y; rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  set S := posPartVec v with hS
  have hSi : ∀ i, S i = max (v i) 0 := fun i => rfl
  have hSmem : S ∈ nonnegOrthant n := fun i => by rw [hSi]; exact le_max_right _ _
  have strong : ∀ y ∈ nonnegOrthant n, ‖S - v‖ ^ 2 + ‖y - S‖ ^ 2 ≤ ‖y - v‖ ^ 2 := by
    intro y hy
    simp only [nsq, PiLp.sub_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [hSi]
    have := hy i
    rcases le_total 0 (v i) with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith
  unfold IsProx
  simp only [zero_add]
  constructor
  · rintro ⟨hx, h⟩
    have h1 := h S hSmem
    have h2 := strong x hx
    have : (ρ / 2) * ‖x - S‖ ^ 2 ≤ 0 := by nlinarith
    have h3 : ‖x - S‖ ^ 2 ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have : ‖x - S‖ = 0 := by nlinarith [norm_nonneg (x - S)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · rintro rfl
    refine ⟨hSmem, fun y hy => ?_⟩
    have := strong y hy
    nlinarith [sq_nonneg ‖y - S‖]

end BoydADMM.Prox

open BoydADMM.Prox


theorem solution {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_ne : C.Nonempty)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∃! x, IsProjection C v x) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ x, IsProx C (fun _ => 0) ρ v x ↔ IsProjection C v x := by
  exact indicator_core C hC_closed hC_convex hC_ne v
