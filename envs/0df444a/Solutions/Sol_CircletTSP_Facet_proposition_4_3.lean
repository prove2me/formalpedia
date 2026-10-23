-- Prove2me | solution 1 for CircletTSP.Facet.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:26:23.186445+00:00
-- url     : https://prove2.me/submissions/d03b0d5d-796f-4e13-8060-9937a1dfb4f1

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet.Cost43

lemma int_abs_cases (x : ℤ) : |x| = if 0 ≤ x then x else -x := by
  split_ifs with h
  · exact abs_of_nonneg h
  · exact abs_of_neg (lt_of_not_ge h)

lemma kept_bounds {n s : ℕ} (hs : s ∈ keptLabels n) :
    (3 ≤ s ∧ s ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ s ≤ n) := by
  simp only [keptLabels, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hs
  omega

lemma labLen_odd {n s t : ℕ} (h4 : 4 ∣ n) :
    labLen n s t % 2 = 1 ↔ s % 2 ≠ t % 2 := by
  have hmod := Nat.mod_eq_zero_of_dvd h4
  simp only [labLen, int_abs_cases, min_def]
  split_ifs <;> omega

lemma length_change {n s t : ℕ} (h4 : 4 ∣ n)
    (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n) :
    conLen n (relabel n s) (relabel n t) =
      if (3 ≤ s ∧ s ≤ n / 2 ∧ 3 ≤ t ∧ t ≤ n / 2) ∨
          (n / 2 + 3 ≤ s ∧ s ≤ n ∧ n / 2 + 3 ≤ t ∧ t ≤ n)
      then labLen n s t else labLen n s t - 2 := by
  have hs' := kept_bounds hs
  have ht' := kept_bounds ht
  have hmod := Nat.mod_eq_zero_of_dvd h4
  rcases hs' with hs' | hs' <;> rcases ht' with ht' | ht'
  all_goals
    simp (disch := omega) only [relabel, if_pos, if_neg]
    simp only [conLen, labLen, int_abs_cases, min_def]
    split_ifs <;> omega


lemma cost_change {n s t : ℕ} (h4 : 4 ∣ n)
    (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n) :
    conCost n (relabel n s) (relabel n t) =
      (if ((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) ∧ s % 2 ≠ t % 2 then
          labCost n s t
        else if ((s ≤ n / 2 ∧ n / 2 + 3 ≤ t) ∨ (t ≤ n / 2 ∧ n / 2 + 3 ≤ s)) ∧
            s % 2 = t % 2 then
          labCost n s t
        else labCost n s t - 2) := by
  have hs' := kept_bounds hs
  have ht' := kept_bounds ht
  have hl := length_change h4 hs ht
  have hp := labLen_odd (s := s) (t := t) h4
  have hsame : ((3 ≤ s ∧ s ≤ n / 2 ∧ 3 ≤ t ∧ t ≤ n / 2) ∨
      (n / 2 + 3 ≤ s ∧ s ≤ n ∧ n / 2 + 3 ≤ t ∧ t ≤ n)) ↔
      ((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) := by
    clear hl hp
    omega
  have hcross : ((s ≤ n / 2 ∧ n / 2 + 3 ≤ t) ∨ (t ≤ n / 2 ∧ n / 2 + 3 ≤ s)) ↔
      ¬((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) := by
    clear hl hp hsame
    omega
  simp only [hsame] at hl
  clear hs ht hs' ht' hsame
  simp only [conCost, labCost, hp, hl, hcross]
  by_cases hg : (s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t) <;>
    by_cases he : s % 2 = t % 2 <;> simp [hg, he] <;> omega

end CircletTSP.Facet.Cost43

open CircletTSP.Facet

theorem solution (n : ℕ) (_hn : 0 < n) (h4 : 4 ∣ n) (s t : ℕ)
    (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n) (_hst : s ≠ t) :
    conLen n (relabel n s) (relabel n t) =
        (if (3 ≤ s ∧ s ≤ n / 2 ∧ 3 ≤ t ∧ t ≤ n / 2) ∨
            (n / 2 + 3 ≤ s ∧ s ≤ n ∧ n / 2 + 3 ≤ t ∧ t ≤ n)
          then labLen n s t else labLen n s t - 2) ∧
      conCost n (relabel n s) (relabel n t) =
        (if ((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) ∧ s % 2 ≠ t % 2 then
            labCost n s t
          else if ((s ≤ n / 2 ∧ n / 2 + 3 ≤ t) ∨ (t ≤ n / 2 ∧ n / 2 + 3 ≤ s)) ∧
              s % 2 = t % 2 then
            labCost n s t
          else labCost n s t - 2) ∧
      conCost n (relabel n s) (relabel n t) ≤ labCost n s t := by
  clear _hn _hst
  have hl := Cost43.length_change h4 hs ht
  have hc := Cost43.cost_change h4 hs ht
  refine ⟨hl, hc, ?_⟩
  clear hs ht h4 hl
  split_ifs at hc <;> omega
