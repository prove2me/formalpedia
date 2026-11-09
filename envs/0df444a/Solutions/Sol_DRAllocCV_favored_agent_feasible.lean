-- Prove2me | solution 1 for DRAllocCV.favored_agent_feasible
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:12:40.238837+00:00
-- url     : https://prove2.me/submissions/6e294b9f-2576-4368-8c1b-c6c5ec92f0d9

import Mathlib
import Definitions.Def_DRAllocCV_IsFavoredAgent
import Definitions.Def_DRAllocCV_Feasible

open MeasureTheory

namespace Aux_DRAllocCVFeas
open DRAllocCV

lemma main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tlo thi c : ι → ℝ) (istar : ι) (p q : ι → (ι → ℝ) → ℝ)
    (hmeas : ∀ i, Measurable (p i) ∧ Measurable (q i))
    (Cnd : (ι → ℝ) → Prop)
    (hdep : ∀ t t' : ι → ℝ, (∀ j, j ≠ istar → t j = t' j) → Cnd t → Cnd t')
    (hF : ∀ t ∈ typeSpace tlo thi, Cnd t → FavoredAllocation istar p q t)
    (hA : ∀ t ∈ typeSpace tlo thi, ¬ Cnd t → InspectedArgmaxAllocation c p q t) :
    Feasible tlo thi p q := by
  have hval : ∀ t ∈ typeSpace tlo thi, ∀ i,
      0 ≤ p i t ∧ p i t ≤ 1 ∧ 0 ≤ q i t ∧ q i t ≤ 1 := by
    intro t ht i
    by_cases hC : Cnd t
    · obtain ⟨h1, h2, h3⟩ := hF t ht hC
      by_cases hi : i = istar
      · subst hi; rw [h1, h2]; norm_num
      · rw [(h3 i hi).1, (h3 i hi).2]; norm_num
    · obtain ⟨i', _, h1, h2, h3⟩ := hA t ht hC
      by_cases hi : i = i'
      · subst hi; rw [h1, h2]; norm_num
      · rw [(h3 i hi).1, (h3 i hi).2]; norm_num
  refine ⟨hmeas, hval, fun t ht => ?_, fun i t ht s hs => ?_⟩
  · by_cases hC : Cnd t
    · obtain ⟨h1, h2, h3⟩ := hF t ht hC
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = istar
        · subst hi; rw [h1, h2]; norm_num
        · rw [(h3 i hi).1, (h3 i hi).2]
      · rw [Finset.sum_eq_single istar (fun b _ hb => (h3 b hb).1)
          (fun h => absurd (Finset.mem_univ _) h), h1]
    · obtain ⟨i', _, h1, h2, h3⟩ := hA t ht hC
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = i'
        · subst hi; rw [h1, h2]
        · rw [(h3 i hi).1, (h3 i hi).2]
      · rw [Finset.sum_eq_single i' (fun b _ hb => (h3 b hb).1)
          (fun h => absurd (Finset.mem_univ _) h), h1]
  · have ht' : Function.update t i s ∈ typeSpace tlo thi := by
      unfold typeSpace at ht ⊢
      rw [Set.mem_univ_pi] at ht ⊢
      intro j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact hs
      · rw [Function.update_of_ne hj]; exact ht j
    have hp0 := (hval t ht i).1
    by_cases hC : Cnd (Function.update t i s)
    · obtain ⟨h1, h2, h3⟩ := hF _ ht' hC
      by_cases hi : i = istar
      · subst hi
        have hCt : Cnd t := hdep _ t (fun j hj => Function.update_of_ne hj _ _) hC
        rw [(hF t ht hCt).1, h1, h2]; norm_num
      · rw [(h3 i hi).1, (h3 i hi).2]; linarith
    · obtain ⟨i', _, h1, h2, h3⟩ := hA _ ht' hC
      by_cases hi : i = i'
      · subst hi; rw [h1, h2]; linarith
      · rw [(h3 i hi).1, (h3 i hi).2]; linarith

end Aux_DRAllocCVFeas

open DRAllocCV Aux_DRAllocCVFeas in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (istar : ι) (ν : ℝ) (p q : ι → (ι → ℝ) → ℝ)
    (hmeas : ∀ i, Measurable (p i) ∧ Measurable (q i))
    (hfa : IsFavoredAgent tlo thi c istar ν p q) :
    Feasible tlo thi p q := by
  rcases hfa with h | h
  · refine main tlo thi c istar p q hmeas (fun t => ∀ i, i ≠ istar → t i - c i ≤ ν) ?_
      (fun t ht hC => (h t ht).1 hC) (fun t ht hC => (h t ht).2 ?_)
    · intro t t' htt' hC i hi
      rw [← htt' i hi]; exact hC i hi
    · push_neg at hC; exact hC
  · refine main tlo thi c istar p q hmeas (fun t => ∀ i, i ≠ istar → t i - c i < ν) ?_
      (fun t ht hC => (h t ht).1 hC) (fun t ht hC => (h t ht).2 ?_)
    · intro t t' htt' hC i hi
      rw [← htt' i hi]; exact hC i hi
    · push_neg at hC; exact hC
