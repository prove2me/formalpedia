-- Prove2me | solution 1 for FengLiYangMatching.General.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:54:43.115+00:00
-- url     : https://prove2.me/submissions/f391a6c4-74cf-4af3-920d-6852215f98ba

import Theorems.Thm_FengLiYangMatching_General_parameter_analysis
import Theorems.Thm_FengLiYangMatching_General_online_feasibility
import Theorems.Thm_FengLiYangMatching_General_convex_competitive_bound
open MeasureTheory Finset FengLiYangMatching.General
open scoped BigOperators


/-- Theorem 1.1, witnessed by Algorithm 1 with the exact Section 3.2 parameters.
The parameter, scalar and online-feasibility clauses expose obligations rather than assumptions. -/
theorem solution :
    (∃! a : ℝ, Root a) ∧ Root aStar ∧ (1/6 : ℝ) < aStar ∧
    (∀ k : ℕ, 1 ≤ k → L k aStar (3/8) ≥ L 1 aStar (3/8)) ∧
    L 1 aStar (3/8) > (1089/2000 : ℝ) ∧
    (∀ n : ℕ, ∀ l : List (Edge n × ℝ × Bool),
      (l.map (fun o => o.1)).Nodup →
      (l.map (fun o => o.2.1)).Pairwise (· ≤ ·) →
      (∀ o ∈ l, ¬ o.1.IsDiag ∧ o.2.1 ∈ Set.Icc (0 : ℝ) 1) →
      ∀ j ≤ l.length,
        IsMatching (run aStar (3/8) (l.take j)).actual ∧
        (run aStar (3/8) (l.take j)).actual ⊆ ((l.take j).map (fun o => o.1)).toFinset) ∧
    (∀ n : ℕ, ∀ l : List (Edge n × ℝ × Bool),
      ∀ j k : ℕ, j ≤ k → k ≤ l.length →
        (run aStar (3/8) (l.take j)).actual ⊆ (run aStar (3/8) (l.take k)).actual) ∧
    (∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      Integrable (ALG G aStar (3/8)) (sampleLaw G (5/11)) ∧
      (∫ w, ALG G aStar (3/8) w ∂sampleLaw G (5/11)) ≥
        (1089/2000 : ℝ) * (OPT G : ℝ)) := by
  obtain ⟨hunique, hroot, hbound, hall, hval⟩ := parameter_analysis
  refine ⟨hunique, hroot, hbound, hall, hval, ?_, ?_, ?_⟩
  · intro n l hnd hord hvalid j hj
    apply (online_feasibility aStar (3/8) (le_of_lt hroot.2.1)).1 n (l.take j)
    · simpa only [List.map_take] using (hord.take (i := j))
    · intro o ho
      exact (hvalid o (List.mem_of_mem_take ho)).1
  · intro n l j k hjk hk
    exact (online_feasibility aStar (3/8) (le_of_lt hroot.2.1)).2 n l j k hjk
  · apply convex_competitive_bound aStar (le_of_lt hroot.1) hroot.2.1 (1089/2000)
    intro k hk
    exact (le_of_lt hval).trans (hall k hk)



