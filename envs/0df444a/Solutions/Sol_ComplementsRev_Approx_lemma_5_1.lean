-- Prove2me | solution 1 for ComplementsRev.Approx.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:11:21.449026+00:00
-- url     : https://prove2.me/submissions/90ef114d-2513-4a0a-b353-c5cad4b11c4c

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

open ComplementsRev.Approx

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Population ι) (rk : Finset ι → ℕ)
    (hrk : Function.Injective rk) (t : ℝ) :
    NONFAV P rk ≤ CORE P t + TAIL P rk t := by
  classical
  have hw : ∀ w ∈ P.profiles, ∀ T, 0 ≤ w T := by
    intro w hw T
    exact P.supp_nonneg T (w T) (Fintype.mem_piFinset.mp hw T)
  have hp : ∀ w ∈ P.profiles, 0 ≤ P.prob w := by
    intro w hw'
    unfold Population.prob
    refine Finset.prod_nonneg (fun T _ => ?_)
    exact le_of_lt (P.f_pos T (w T) (Fintype.mem_piFinset.mp hw' T))
  unfold NONFAV CORE TAIL Population.E
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun w hwm => ?_)
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hp w hwm)
  have hw0 := hw w hwm
  refine Finset.sup'_le _ _ (fun S hS => ?_)
  have hc : ∀ T, 0 ≤ (if t < w T ∧ ¬ InRegion rk w T then w T else 0) := by
    intro T; split_ifs <;> simp [hw0 T]
  have h1 : (∑ T ∈ S.powerset, if InRegion rk w T then 0 else w T) ≤
      (∑ T ∈ S.powerset, if w T ≤ t then w T else 0) +
      ∑ T ∈ S.powerset, (if t < w T ∧ ¬ InRegion rk w T then w T else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun T _ => ?_)
    have := hw0 T
    by_cases hR : InRegion rk w T
    · simp only [hR, if_true, not_true_eq_false, and_false, if_false]
      split_ifs <;> linarith
    · simp only [hR, if_false, not_false_eq_true, and_true]
      by_cases ht : w T ≤ t
      · have : ¬ t < w T := not_lt.mpr ht
        simp [ht, this]
      · have : t < w T := lt_of_not_ge ht
        simp [ht, this]
  have h2 : (∑ T ∈ S.powerset, (if t < w T ∧ ¬ InRegion rk w T then w T else 0)) ≤
      ∑ T : Finset ι, (if t < w T ∧ ¬ InRegion rk w T then w T else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun T _ _ => hc T)
  have h3 : (∑ T ∈ S.powerset, if w T ≤ t then w T else 0) ≤
      P.C.sup' ⟨∅, P.empty_mem⟩ (fun S =>
        ∑ T ∈ S.powerset, if w T ≤ t then w T else 0) :=
    Finset.le_sup' (fun S => ∑ T ∈ S.powerset, if w T ≤ t then w T else 0) hS
  linarith
