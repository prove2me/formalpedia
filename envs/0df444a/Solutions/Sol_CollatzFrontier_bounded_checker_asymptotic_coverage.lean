-- Prove2me | solution 1 for CollatzFrontier.bounded_checker_asymptotic_coverage
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-05T18:17:50.587848+00:00
-- url     : https://prove2.me/submissions/da833641-f0d0-4b0d-8ba0-af21d858ce4c

import Definitions.Def_collatzFrontierCoverage
import Theorems.Thm_CollatzFrontier_automatic_certificate_failure_bound
import Mathlib.Analysis.SpecificLimits.Basic

open CollatzFrontier Filter Topology

namespace CollatzFrontierAux

theorem geometric_lower_tail_rate : (0 : ℝ) < 16384 / 16875 ∧ (16384 / 16875 : ℝ) < 1 := by
  norm_num

end CollatzFrontierAux

open CollatzFrontierAux

/-- Arbitrarily high asymptotic coverage by a fully specified finite checker family.
The chosen accuracy parameter `m` is fixed before `R` varies; no unbounded existential
certificate-membership predicate is evaluated by the count. Transcribed verbatim from
`CollatzFrontier.bounded_checker_asymptotic_coverage`
(research/executable-coverage-20261002 @ 3835de1), reducing to the imported
`automatic_certificate_failure_bound` platform theorem. -/
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 2 ≤ m ∧ ∀ R : ℕ, 2 ^ (24 * m) ≤ R →
      (automaticCertificateFailureCount R m : ℝ) / R < ε := by
  let bound : ℕ → ℝ := fun m =>
    (81 / 16777216 : ℝ) ^ m + (16384 / 16875 : ℝ) ^ m + (1 / 131072 : ℝ) ^ m
  have hb : Filter.Tendsto bound Filter.atTop (nhds 0) := by
    have hβ := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 81 / 16777216 by norm_num) (show (81 / 16777216 : ℝ) < 1 by norm_num)
    have hα := tendsto_pow_atTop_nhds_zero_of_lt_one geometric_lower_tail_rate.1.le geometric_lower_tail_rate.2
    have hγ := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 131072 by norm_num) (show (1 / 131072 : ℝ) < 1 by norm_num)
    simpa only [zero_add] using (hβ.add hα).add hγ
  intro ε hε
  have hev : ∀ᶠ m in Filter.atTop, bound m < ε := (tendsto_order.mp hb).2 ε hε
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  let m := max M 2
  refine ⟨m, le_max_right _ _, ?_⟩
  intro R hR
  exact lt_of_le_of_lt (CollatzFrontier.automatic_certificate_failure_bound R m (le_max_right _ _) hR)
    (hM m (le_max_left _ _))
