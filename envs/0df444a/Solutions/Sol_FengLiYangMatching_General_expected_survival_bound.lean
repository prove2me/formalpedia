-- Prove2me | solution 1 for FengLiYangMatching.General.expected_survival_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:46:47.095176+00:00
-- url     : https://prove2.me/submissions/a1596b05-ed82-4cc2-a66b-1d877ab7761e

import Theorems.Thm_FengLiYangMatching_General_expected_accounting
import Theorems.Thm_FengLiYangMatching_General_survival_moments
open MeasureTheory Finset
open scoped BigOperators
namespace FengLiYangMatching.General

theorem expected_survival_reduction {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ (6/11 : ℝ) * OPT G +
      ∑ e ∈ M, ((1/2 : ℝ) * (∫ t in a..(3/8 : ℝ), edgeSurvival G e t) -
        (1-a)/22 * edgeSurvival G e a -
        (1-(3/8 : ℝ))/10 * edgeSurvival G e (3/8)) := by
  have he := expected_accounting G M hMG hM hmax a ha hab
  obtain ⟨hU,hM2i,hM2⟩ := survival_moments G M hMG hM hmax a ha hab
  rw [(hU a ⟨ha,le_of_lt hab⟩).2, (hU (3/8) ⟨by norm_num,le_refl _⟩).2,hM2] at he
  convert he using 1
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

end FengLiYangMatching.General

open FengLiYangMatching.General


theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ (6/11 : ℝ) * OPT G +
      ∑ e ∈ M, ((1/2 : ℝ) * (∫ t in a..(3/8 : ℝ), edgeSurvival G e t) -
        (1-a)/22 * edgeSurvival G e a -
        (1-(3/8 : ℝ))/10 * edgeSurvival G e (3/8)) := by
  exact expected_survival_reduction G M hMG hM hmax a ha hab


