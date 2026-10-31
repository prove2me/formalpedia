-- Prove2me | solution 1 for BudgetFeasSubmod.Main.lemma_3_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:40:58.142879+00:00
-- url     : https://prove2.me/submissions/b8107572-bf24-4bce-8a72-52bff5c72b18

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

open BudgetFeasSubmod.Main Finset

namespace BFSDisproof33

def w : Fin 2 → ℝ := ![1, 5]

noncomputable def v (S : Finset (Fin 2)) : ℝ := ∑ a ∈ S, w a

def alg2 (X : Finset (Fin 2)) : Finset (Fin 2) := if X = ∅ then {0} else {1}

def tb (U : Finset (Fin 2)) (S : Fin 2 → Finset (Fin 2)) : Fin 2 × Fin 2 :=
  if 1 ∈ U ∧ 1 ∉ S 0 then (1, 0)
  else if 1 ∈ U ∧ 1 ∉ S 1 then (1, 1)
  else if 0 ∈ U ∧ 0 ∉ S 0 then (0, 0)
  else if 0 ∈ U ∧ 0 ∉ S 1 then (0, 1)
  else if 1 ∈ U then (1, 0) else (0, 0)

lemma marg_eq (a : Fin 2) (X : Finset (Fin 2)) :
    marg v a X = if a ∈ X then 0 else w a := by
  unfold marg v
  split_ifs with h
  · rw [Finset.insert_eq_of_mem h]; ring
  · rw [Finset.sum_insert h]; ring

lemma hv : IsValuation v := by
  refine ⟨by simp [v], fun S => ?_, fun S T => ?_⟩
  · unfold v
    apply Finset.sum_nonneg
    intro a _
    fin_cases a <;> simp [w]
  · unfold v
    rw [Finset.sum_union_inter]

lemma w0 : w 0 = 1 := by simp [w]
lemma w1 : w 1 = 5 := by simp [w]

lemma marg_le (a : Fin 2) (X : Finset (Fin 2)) : marg v a X ≤ w a := by
  rw [marg_eq]; split_ifs
  · fin_cases a <;> simp [w]
  · exact le_refl _

lemma key (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

lemma htb : IsArgmaxRule v tb := by
  intro U S h
  obtain ⟨i0, hi0, j0, hpos⟩ := h
  unfold tb
  split_ifs with c1 c2 c3 c4 c5
  · refine ⟨c1.1, fun i _ j => ?_⟩
    rw [marg_eq 1 (S 0), if_neg c1.2, w1]
    have := marg_le i (S j); rcases key i with rfl | rfl <;> simp_all [w0, w1] <;> linarith
  · refine ⟨c2.1, fun i _ j => ?_⟩
    rw [marg_eq 1 (S 1), if_neg c2.2, w1]
    have := marg_le i (S j); rcases key i with rfl | rfl <;> simp_all [w0, w1] <;> linarith
  · refine ⟨c3.1, fun i hi j => ?_⟩
    simp only
    rw [marg_eq 0 (S 0), if_neg c3.2, w0]
    rcases key i with rfl | rfl
    · have := marg_le 0 (S j); rw [w0] at this; exact this
    · have h0 : (1 : Fin 2) ∈ S 0 := by by_contra hh; exact c1 ⟨hi, hh⟩
      have h1 : (1 : Fin 2) ∈ S 1 := by by_contra hh; exact c2 ⟨hi, hh⟩
      rcases key j with rfl | rfl
      · rw [marg_eq, if_pos h0]; norm_num
      · rw [marg_eq, if_pos h1]; norm_num
  · refine ⟨c4.1, fun i hi j => ?_⟩
    simp only
    rw [marg_eq 0 (S 1), if_neg c4.2, w0]
    rcases key i with rfl | rfl
    · have := marg_le 0 (S j); rw [w0] at this; exact this
    · have h0 : (1 : Fin 2) ∈ S 0 := by by_contra hh; exact c1 ⟨hi, hh⟩
      have h1 : (1 : Fin 2) ∈ S 1 := by by_contra hh; exact c2 ⟨hi, hh⟩
      rcases key j with rfl | rfl
      · rw [marg_eq, if_pos h0]; norm_num
      · rw [marg_eq, if_pos h1]; norm_num
  all_goals exfalso
  all_goals
    have hin : i0 ∈ S j0 := by
      rcases key i0 with rfl | rfl <;> rcases key j0 with rfl | rfl <;>
        by_contra hh <;> simp_all
    rw [marg_eq, if_pos hin] at hpos
    exact lt_irrefl 0 hpos

end BFSDisproof33

open BFSDisproof33 in
theorem solution : ¬ (∀ {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ)
    (alg2 : Finset A → Finset A) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2)
    (β B x : ℝ) (D : Finset A),
    IsValuation v → IsArgmaxRule v tb → 0 < β → 0 < B →
    IsMonotoneRule (simGreedy v alg2 tb β B x D) B ∧
      IsTruthful (simGreedy v alg2 tb β B x D) B ∧
      IsIR (simGreedy v alg2 tb β B x D) B) := by
  intro H
  have hmono := (H (A := Fin 2) v alg2 tb 1 1 2 {0} hv htb one_pos one_pos).1
  have hdom : InDomain (1 : ℝ) (fun _ : Fin 2 => (1 : ℝ)) := fun _ => ⟨zero_le_one, le_refl _⟩
  have hpos : ∃ i ∈ (sgInit ({0} : Finset (Fin 2)) (1 : ℝ)).U, ∃ j : Fin 2,
      0 < marg v i ((sgInit ({0} : Finset (Fin 2)) (1 : ℝ)).S j) :=
    ⟨0, by simp [sgInit], 0, by simp [marg_eq, sgInit, w0]⟩
  have htb0 : tb {0} (fun _ => ∅) = (0, 0) := by simp [tb]
  have hprice : price v 1 1 2 0 ∅ = 1 / 2 := by
    simp [price, marg_eq, w0]
  -- truthful bid 1: agent 0 is rejected, output is alg2 ∅ = {0}
  have hwin : (0 : Fin 2) ∈ simGreedy v alg2 tb 1 1 2 {0} (fun _ => 1) := by
    unfold simGreedy sgRun
    simp only [Finset.card_singleton, Function.iterate_one]
    unfold sgStep
    rw [if_pos hpos]
    simp only [sgInit, htb0, hprice]
    norm_num [better, alg2, v, w0]
  have hlose : (0 : Fin 2) ∉ simGreedy v alg2 tb 1 1 2 {0}
      (Function.update (fun _ => 1) 0 0) := by
    unfold simGreedy sgRun
    simp only [Finset.card_singleton, Function.iterate_one]
    unfold sgStep
    rw [if_pos hpos]
    simp only [sgInit, htb0, hprice]
    norm_num [better, alg2, v, w0, w1]
  exact hlose (hmono (fun _ => 1) 0 0 hdom (le_refl 0) (by norm_num) hwin)
