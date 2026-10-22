-- Prove2me | solution 1 for CompOT.Metric.prop_2_2_gluing
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:21:33.868881+00:00
-- url     : https://prove2.me/submissions/adae845c-4446-4670-a8c0-4e968e928473

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

set_option autoImplicit false
open Matrix CompOT.Metric

theorem solution {n : ℕ} (a b c : Fin n → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n))
    (hc : c ∈ stdSimplex ℝ (Fin n))
    (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b)
    (hQ : Q ∈ CompOT.Assignment.couplings b c) :
    glue b P Q ∈ CompOT.Assignment.couplings a c := by
  obtain ⟨hP0, hPr, hPc⟩ := hP
  obtain ⟨hQ0, hQr, hQc⟩ := hQ
  have hbt : ∀ j, 0 < btilde b j := by
    intro j; unfold btilde; split_ifs with h
    · exact h
    · exact one_pos
  have hb0 : ∀ j, 0 ≤ b j := fun j => hb.1 j
  have hPz : ∀ i j, b j = 0 → P i j = 0 := by
    intro i j hj
    have : P i j ≤ ∑ i', P i' j :=
      Finset.single_le_sum (fun i' _ => hP0 i' j) (Finset.mem_univ i)
    rw [hPc j, hj] at this
    exact le_antisymm this (hP0 i j)
  have hQz : ∀ j k, b j = 0 → Q j k = 0 := by
    intro j k hj
    have : Q j k ≤ ∑ k', Q j k' :=
      Finset.single_le_sum (fun k' _ => hQ0 j k') (Finset.mem_univ k)
    rw [hQr j, hj] at this
    exact le_antisymm this (hQ0 j k)
  have hfac : ∀ i j, P i j * (1 / btilde b j) * b j = P i j := by
    intro i j
    by_cases h : 0 < b j
    · have : btilde b j = b j := by simp [btilde, h]
      rw [this]; field_simp
    · have h0 : b j = 0 := le_antisymm (not_lt.1 h) (hb0 j)
      simp [hPz i j h0]
  have hfac2 : ∀ j k, b j * (1 / btilde b j) * Q j k = Q j k := by
    intro j k
    by_cases h : 0 < b j
    · have : btilde b j = b j := by simp [btilde, h]
      rw [this]; field_simp
    · have h0 : b j = 0 := le_antisymm (not_lt.1 h) (hb0 j)
      simp [hQz j k h0]
  have hS : ∀ i k, glue b P Q i k = ∑ j, P i j * (1 / btilde b j) * Q j k := by
    intro i k
    rw [glue, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  refine ⟨fun i k => ?_, fun i => ?_, fun k => ?_⟩
  · rw [hS]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hP0 i j) (one_div_pos.2 (hbt j)).le) (hQ0 j k)
  · simp_rw [hS]
    rw [Finset.sum_comm]
    calc ∑ j, ∑ k, P i j * (1 / btilde b j) * Q j k
        = ∑ j, P i j * (1 / btilde b j) * b j :=
          Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, hQr j]
      _ = ∑ j, P i j := Finset.sum_congr rfl fun j _ => hfac i j
      _ = a i := hPr i
  · simp_rw [hS]
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, P i j * (1 / btilde b j) * Q j k
        = ∑ j, b j * (1 / btilde b j) * Q j k :=
          Finset.sum_congr rfl fun j _ => by
            rw [← Finset.sum_mul, ← Finset.sum_mul, ← hPc j, Finset.sum_mul]
      _ = ∑ j, Q j k := Finset.sum_congr rfl fun j _ => hfac2 j k
      _ = c k := hQc k
