-- Prove2me | solution 1 for DynFairDiv.Uniform.lemma_E_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:02:44.780007+00:00
-- url     : https://prove2.me/submissions/2110593f-a392-4332-bf97-6cdab00f9347

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

open DynFairDiv.Uniform

private def P (d : ℕ) (σ : ℝ) (ℓ i : ℕ) : Prop :=
  ffa (uniformCV d) σ (ℓ * (d + 1) + i) =
      List.replicate i (σ / ((ℓ * d + i : ℕ) : ℝ)) ++
      (List.range ℓ).flatMap
        (fun k => List.replicate (d + 1) (σ / ((ℓ * d + i + k + 1 : ℕ) : ℝ)))

private lemma step_i (d : ℕ) (σ : ℝ) (ℓ i : ℕ) (hi : i < d) (h : P d σ ℓ i) :
    P d σ ℓ (i + 1) := by
  unfold P at *
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · rw [show 0 * (d + 1) + (i + 1) = (0 * (d + 1) + i) + 1 by ring, ffa, h]
    simp only [uniformCV]
    simp only [List.range_zero, List.flatMap_nil, List.append_nil, zero_mul, zero_add]
    rw [List.drop_eq_nil_of_le (by simp; omega), List.nil_append, min_eq_right hi.le]
  · obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons] at h
    rw [show (m + 1) * (d + 1) + (i + 1) = ((m + 1) * (d + 1) + i) + 1 by ring, ffa, h]
    simp only [uniformCV]
    rw [min_eq_left (by nlinarith)]
    rw [← List.append_assoc,
      List.drop_append_of_le_length (by simp; omega)]
    rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append,
      List.length_replicate, List.drop_replicate]
    rw [List.range_succ, List.flatMap_append, List.flatMap_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    have e1 : d + 1 - (d - i) = i + 1 := by omega
    rw [e1]
    refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ ?_)
    · congr 2 <;> push_cast <;> ring
    · apply List.flatMap_congr
      intro k _
      congr 2 <;> push_cast <;> ring
    · congr 2 <;> push_cast <;> ring

private lemma step_l (d : ℕ) (σ : ℝ) (ℓ : ℕ) (h : P d σ ℓ d) : P d σ (ℓ + 1) 0 := by
  unfold P at *
  rw [show (ℓ + 1) * (d + 1) + 0 = (ℓ * (d + 1) + d) + 1 by ring, ffa, h]
  simp only [uniformCV]
  rw [min_eq_left (by nlinarith), List.drop_append_of_le_length (by simp),
    List.drop_replicate, Nat.sub_self, List.replicate_zero, List.nil_append,
    List.replicate_zero, List.nil_append, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  congr 1
  · apply List.flatMap_congr
    intro k _
    congr 2 <;> push_cast <;> ring
  · congr 2 <;> push_cast <;> ring

theorem solution (d : ℕ) (_hd : 1 ≤ d) (σ : ℝ) (ℓ i : ℕ) (hi : i ≤ d) :
    ffa (uniformCV d) σ (ℓ * (d + 1) + i) =
      List.replicate i (σ / ((ℓ * d + i : ℕ) : ℝ)) ++
      (List.range ℓ).flatMap
        (fun k => List.replicate (d + 1) (σ / ((ℓ * d + i + k + 1 : ℕ) : ℝ))) := by
  have key : ∀ ℓ, ∀ i ≤ d, P d σ ℓ i := by
    intro ℓ
    induction ℓ with
    | zero =>
      intro i hi
      induction i with
      | zero => simp [P, ffa]
      | succ i ih => exact step_i d σ 0 i (by omega) (ih (by omega))
    | succ ℓ ihl =>
      intro i hi
      induction i with
      | zero => exact step_l d σ ℓ (ihl d le_rfl)
      | succ i ih => exact step_i d σ (ℓ + 1) i (by omega) (ih (by omega))
  exact key ℓ i hi
