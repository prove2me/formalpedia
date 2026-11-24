-- Prove2me | solution 1 for FairSelling.truncSum_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:04.380518+00:00
-- url     : https://prove2.me/submissions/cd66cd16-f583-46bc-8cc3-abb4c726cec0

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
section
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G] in
private lemma trunc_pointwise (v p : G → ℝ) {a c t : ℝ} (hnb : NoBreak v p a c)
    (hat : a ≤ t) (htc : t ≤ c) (g : G) :
    max (p g) (min (v g) t)
      = (if c ≤ v g ∧ p g ≤ a then t else max (p g) (min (v g) a)) := by
  rcases hnb g with ⟨hv, hp⟩
  by_cases hcase : c ≤ v g ∧ p g ≤ a
  · rw [if_pos hcase]
    rw [min_eq_right (le_trans htc hcase.1), max_eq_right (le_trans hcase.2 hat)]
  · rw [if_neg hcase]
    rcases hv with hv | hv
    · rw [min_eq_left (le_trans hv hat), min_eq_left hv]
    · -- `c ≤ v g`, so by the case assumption `p g > a`, hence `c ≤ p g`
      have hpa : ¬ p g ≤ a := fun h => hcase ⟨hv, h⟩
      have hpc : c ≤ p g := hp.resolve_left hpa
      rw [min_eq_right (le_trans htc hv), max_eq_left (le_trans htc hpc)]
      rcases le_total (v g) a with h | h
      · rw [min_eq_left h, max_eq_left (le_trans (le_trans h hat) (le_trans htc hpc))]
      · rw [min_eq_right h, max_eq_left (le_trans (le_trans hat htc) hpc)]
end FairSelling
end

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) {a c t : ℝ} (hnb : NoBreak v p a c)
    (hat : a ≤ t) (htc : t ≤ c) :
    truncSum n v p t
      = (flatConst v p a c + ((slopeGoods v p a c).card : ℝ) * t) / n := by
  classical
  unfold truncSum flatConst slopeGoods
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g => c ≤ v g ∧ p g ≤ a)
        (fun g => max (p g) (min (v g) t))]
  have h1 : ∑ g ∈ Finset.univ.filter (fun g => c ≤ v g ∧ p g ≤ a), max (p g) (min (v g) t)
      = ((Finset.univ.filter (fun g => c ≤ v g ∧ p g ≤ a)).card : ℝ) * t := by
    rw [Finset.sum_congr rfl (fun g hg => ?_), Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.mem_filter] at hg
    rw [trunc_pointwise v p hnb hat htc g, if_pos hg.2]
  have h2 : ∑ g ∈ Finset.univ.filter (fun g => ¬ (c ≤ v g ∧ p g ≤ a)), max (p g) (min (v g) t)
      = ∑ g ∈ Finset.univ.filter (fun g => ¬ (c ≤ v g ∧ p g ≤ a)), max (p g) (min (v g) a) := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    simp only [Finset.mem_filter] at hg
    rw [trunc_pointwise v p hnb hat htc g, if_neg hg.2]
  rw [h1, h2]; ring
end FairSelling
