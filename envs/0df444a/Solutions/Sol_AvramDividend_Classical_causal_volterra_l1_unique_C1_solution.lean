-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_l1_unique_C1_solution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:59:58.801689+00:00
-- url     : https://prove2.me/submissions/4cdb803a-bc47-4acf-9533-adae816127ef

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_C1_solution_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ G : ℝ → ℝ,
      ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) ∧
      (∀ V : ℝ → ℝ,
        ContinuousOn V (Ioi (0 : ℝ)) →
        (∀ R : ℝ, 0 < R →
          ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C) →
        (∀ x : ℝ, 0 < x →
          a * V x +
            (∫ s in Ioc (0 : ℝ) x,
              (β + K (x - s)) * V s ∂volume) = x) →
        ∀ x : ℝ, 0 < x → V x = G x) := by
  obtain ⟨G, hGc, hGb, hGe⟩ :=
    causal_volterra_l1_C1_solution_exists K a β ha hK
  refine ⟨G, hGc, hGb, hGe, ?_⟩
  intro V hVc hVb hVe x hx
  exact causal_volterra_l1_continuous_solution_unique
    K a β ha hK V G hVc hGc.continuousOn hVb hGb hVe hGe x hx
