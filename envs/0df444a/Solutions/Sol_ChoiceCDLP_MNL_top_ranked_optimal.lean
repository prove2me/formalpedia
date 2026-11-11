-- Prove2me | solution 1 for ChoiceCDLP.MNL.top_ranked_optimal
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T06:16:10.631014+00:00
-- url     : https://prove2.me/submissions/55f522d1-48c7-466a-9523-370d88b15f37

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

open ChoiceCDLP.MNL

theorem solution {ι : Type*} [Fintype ι] (v w : ι → ℝ) (v₀ : ℝ)
    (hv : ∀ j, 0 < v j) (hv₀ : 0 ≤ v₀) (hw : ∃ j, 0 ≤ w j) :
    ∃ k : ι, ∀ S : Finset ι, mnlObjective v w v₀ S ≤
      mnlObjective v w v₀ (Finset.univ.filter fun j => w k ≤ w j) := by
  classical
  let F : Finset ι → ℝ := mnlObjective v w v₀
  obtain ⟨S, _, hS⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset ι)) F
    (by simp)
  have hmax (B : Finset ι) : F B ≤ F S := hS B (Finset.mem_univ B)
  let r := F S
  have hr : 0 ≤ r := by
    simpa [r, F, mnlObjective] using hmax ∅
  have den_pos (B : Finset ι) (hB : B.Nonempty) :
      0 < (∑ j ∈ B, v j) + v₀ := by
    exact add_pos_of_pos_of_nonneg (Finset.sum_pos (fun j _ => hv j) hB) hv₀
  have expand (B : Finset ι) :
      (∑ j ∈ B, (w j - r) * v j) =
        (∑ j ∈ B, w j * v j) - r * (∑ j ∈ B, v j) := by
    simp [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  have balance : (∑ j ∈ S, (w j - r) * v j) = r * v₀ := by
    by_cases hSE : S = ∅
    · simp [hSE, r, F, mnlObjective]
    · have hd := den_pos S (Finset.nonempty_iff_ne_empty.mpr hSE)
      have hmul : (∑ j ∈ S, w j * v j) = r * ((∑ j ∈ S, v j) + v₀) := by
        exact (div_eq_iff (ne_of_gt hd)).mp (show mnlObjective v w v₀ S = r from rfl)
      rw [expand]
      nlinarith
  let T := Finset.univ.filter fun j => r ≤ w j
  have hterm (j : ι) :
      (if j ∈ S then (w j - r) * v j else 0) ≤
        (if r ≤ w j then (w j - r) * v j else 0) := by
    split_ifs <;> nlinarith [hv j]
  have hsum : (∑ j ∈ S, (w j - r) * v j) ≤ (∑ j ∈ T, (w j - r) * v j) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
    simpa [← Finset.sum_filter, T] using h
  have hT : T.Nonempty := by
    by_contra hn
    have ht0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hall (j : ι) : w j < r := by
      have hm : j ∉ T := by rw [ht0]; simp
      simpa [T, not_le] using hm
    by_cases hSE : S = ∅
    · have hz : r = 0 := by simp [r, F, mnlObjective, hSE]
      obtain ⟨j, hj⟩ := hw
      have := hall j
      linarith
    · have hneg : (∑ j ∈ S, (w j - r) * v j) < 0 :=
        Finset.sum_neg (fun j _ => mul_neg_of_neg_of_pos (sub_neg.mpr (hall j)) (hv j))
          (Finset.nonempty_iff_ne_empty.mpr hSE)
      rw [balance] at hneg
      have := mul_nonneg hr hv₀
      linarith
  have hFT : r ≤ F T := by
    change r ≤ (∑ j ∈ T, w j * v j) / ((∑ j ∈ T, v j) + v₀)
    apply (le_div_iff₀ (den_pos T hT)).2
    rw [balance, expand] at hsum
    nlinarith
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image T w hT
  have heq : (Finset.univ.filter fun j => w k ≤ w j) = T := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hkr : r ≤ w k := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_trans hkr h⟩
    · intro h
      exact hmin j h
  refine ⟨k, fun B => ?_⟩
  rw [heq]
  exact le_trans (hmax B) hFT

#print axioms solution
