-- Prove2me | solution 1 for CircletTSP.Facet.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:26:24.172547+00:00
-- url     : https://prove2.me/submissions/86678a02-7e51-4387-a3d0-c43c50715459

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


end CircletTSP.Facet.Cost43

namespace CircletTSP.Facet.Cost44
open Cost43

lemma fixed_costs {n : ℕ} (hn : 0 < n) (h4 : 4 ∣ n) :
    labCost n 1 2 + labCost n 2 (n / 2 + 2) +
      labCost n (n / 2 + 2) (n / 2 + 1) = 2 := by
  have hmod := Nat.mod_eq_zero_of_dvd h4
  have h12 : labLen n 1 2 = 1 := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have h2d : labLen n 2 (n / 2 + 2) = (n / 2 : ℕ) := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have hdd : labLen n (n / 2 + 2) (n / 2 + 1) = 1 := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have hdmod : ((n / 2 : ℕ) : ℤ) % 2 = 0 := by omega
  simp only [labCost, h12, h2d, hdd, hdmod]
  norm_num

lemma endpoint_lengths {n s : ℕ} (h4 : 4 ∣ n) (hs : s ∈ keptLabels n) :
    labLen n s 1 = (if s ≤ n / 2 then (s : ℤ) - 1 else n - s + 1) ∧
    labLen n (n / 2 + 1) s =
      (if s ≤ n / 2 then (n / 2 : ℕ) + 1 - (s : ℤ) else s - (n / 2 : ℕ) - 1) := by
  have hs' := kept_bounds hs
  have hmod := Nat.mod_eq_zero_of_dvd h4
  rcases hs' with hs' | hs'
  all_goals
    constructor <;> simp only [labLen, int_abs_cases, min_def] <;> split_ifs <;> omega

set_option maxHeartbeats 1000000 in
lemma endpoint_bound {n j k : ℕ} (h4 : 4 ∣ n)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) :
    2 ≤ labCost n j 1 + labCost n (n / 2 + 1) k -
      conCost n (relabel n j) (relabel n k) := by
  have hj' := kept_bounds hj
  have hk' := kept_bounds hk
  have hmod := Nat.mod_eq_zero_of_dvd h4
  have hl := length_change h4 hj hk
  have hp := labLen_odd (s := j) (t := k) h4
  have hcp : conLen n (relabel n j) (relabel n k) % 2 = 1 ↔ j % 2 ≠ k % 2 := by
    clear hj hk hj' hk'
    rw [hl]
    clear hl h4
    split_ifs <;> omega
  have hA := (endpoint_lengths h4 hj).1
  have hB := (endpoint_lengths h4 hk).2
  clear hj hk hp
  simp only [labCost, labLen_odd h4, conCost, hcp]
  rw [hA, hB, hl]
  clear hA hB hl hcp
  rcases hj' with hj' | hj' <;> rcases hk' with hk' | hk'
  all_goals
    by_cases hjp : j % 2 = 0 <;> by_cases hkp : k % 2 = 0
    all_goals
      simp (disch := omega) only [if_pos, if_neg]
      simp only [labLen, int_abs_cases, min_def]
      split_ifs <;> omega

end CircletTSP.Facet.Cost44

open CircletTSP.Facet

theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hjk : j ≠ k) :
    labCost n j 1 + labCost n 1 2 + labCost n 2 (n / 2 + 2) + labCost n (n / 2 + 2) (n / 2 + 1) +
        labCost n (n / 2 + 1) k - conCost n (relabel n j) (relabel n k) ≥ 4 := by
  have _hjk := hjk
  have hfixed := Cost44.fixed_costs hn h4
  have hend := Cost44.endpoint_bound h4 hj hk
  omega
