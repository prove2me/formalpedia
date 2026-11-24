-- Prove2me | solution 1 for ConformalBeyondExchangeability.strange_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T15:19:20.296321+00:00
-- url     : https://prove2.me/submissions/931bfc1f-8938-4ae2-818d-6f85fa6900af

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory
namespace ConformalBeyondExchangeability


theorem strange_weight_le {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → ℝ) :
    ∑ i ∈ strangeSet (normWeights w) α r, normWeights w i ≤ α := by
  classical
  set p := normWeights w with hpdef
  have hD : 0 < ∑ j, w j + 1 := by
    have : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => (hw j).1
    linarith
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    simp only [hpdef, normWeights]
    apply div_nonneg _ hD.le
    split_ifs
    · exact (hw _).1
    · exact zero_le_one
  have hp1 : ∑ i, p i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hpdef, normWeights, Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl,
      dif_neg, not_false_eq_true]
    rw [← Finset.sum_div, ← add_div, div_self hD.ne']
  set S := strangeSet p α r with hS
  by_contra hcon
  push_neg at hcon
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hcon
    linarith
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image S r hne
  have hmemS : ∀ i, i ∈ S ↔ wQuantile p (fun j => (r j : EReal)) (1 - α) < (r i : EReal) := by
    intro i
    simp [hS, strangeSet]
  have hQ : (r i0 : EReal) ≤ wQuantile p (fun j => (r j : EReal)) (1 - α) := by
    unfold wQuantile
    refine le_sInf fun q hq => ?_
    simp only [Set.mem_setOf_eq] at hq
    by_contra hlt
    push_neg at hlt
    have hzero : ∑ i ∈ S, (if (r i : EReal) ≤ q then p i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : (r i0 : EReal) ≤ r i := EReal.coe_le_coe_iff.mpr (hmin i hi)
      rw [if_neg]
      intro hle
      exact absurd (lt_of_le_of_lt (le_trans this hle) hlt) (lt_irrefl _)
    have hcomp : ∑ i ∈ Sᶜ, (if (r i : EReal) ≤ q then p i else 0) ≤ ∑ i ∈ Sᶜ, p i := by
      refine Finset.sum_le_sum fun i _ => ?_
      split_ifs
      · exact le_refl _
      · exact hp i
    have htot : ∑ i ∈ S, p i + ∑ i ∈ Sᶜ, p i = 1 := by rw [Finset.sum_add_sum_compl, hp1]
    rw [← Finset.sum_add_sum_compl S, hzero, zero_add] at hq
    linarith
  have := (hmemS i0).mp hi0
  exact absurd (lt_of_le_of_lt hQ this) (lt_irrefl _)


end ConformalBeyondExchangeability

open ConformalBeyondExchangeability in
theorem solution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → ℝ) :
    ∑ i ∈ strangeSet (normWeights w) α r, normWeights w i ≤ α := by
  classical
  set p := normWeights w with hpdef
  have hD : 0 < ∑ j, w j + 1 := by
    have : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => (hw j).1
    linarith
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    simp only [hpdef, normWeights]
    apply div_nonneg _ hD.le
    split_ifs
    · exact (hw _).1
    · exact zero_le_one
  have hp1 : ∑ i, p i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hpdef, normWeights, Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl,
      dif_neg, not_false_eq_true]
    rw [← Finset.sum_div, ← add_div, div_self hD.ne']
  set S := strangeSet p α r with hS
  by_contra hcon
  push_neg at hcon
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hcon
    linarith
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image S r hne
  have hmemS : ∀ i, i ∈ S ↔ wQuantile p (fun j => (r j : EReal)) (1 - α) < (r i : EReal) := by
    intro i
    simp [hS, strangeSet]
  have hQ : (r i0 : EReal) ≤ wQuantile p (fun j => (r j : EReal)) (1 - α) := by
    unfold wQuantile
    refine le_sInf fun q hq => ?_
    simp only [Set.mem_setOf_eq] at hq
    by_contra hlt
    push_neg at hlt
    have hzero : ∑ i ∈ S, (if (r i : EReal) ≤ q then p i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : (r i0 : EReal) ≤ r i := EReal.coe_le_coe_iff.mpr (hmin i hi)
      rw [if_neg]
      intro hle
      exact absurd (lt_of_le_of_lt (le_trans this hle) hlt) (lt_irrefl _)
    have hcomp : ∑ i ∈ Sᶜ, (if (r i : EReal) ≤ q then p i else 0) ≤ ∑ i ∈ Sᶜ, p i := by
      refine Finset.sum_le_sum fun i _ => ?_
      split_ifs
      · exact le_refl _
      · exact hp i
    have htot : ∑ i ∈ S, p i + ∑ i ∈ Sᶜ, p i = 1 := by rw [Finset.sum_add_sum_compl, hp1]
    rw [← Finset.sum_add_sum_compl S, hzero, zero_add] at hq
    linarith
  have := (hmemS i0).mp hi0
  exact absurd (lt_of_le_of_lt hQ this) (lt_irrefl _)

