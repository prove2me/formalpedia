-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_signed_neumann_sum_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:37:28.438404+00:00
-- url     : https://prove2.me/submissions/a5e50410-a6be-4569-ab48-29976ee25cfd

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Domination by the positive Gaussian envelope gives L1 of signed Neumann sums. -/
theorem solution
    (P F : ℕ → ℝ → ℝ)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, |P n x| ≤ F n x)
    (hFpoint : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hFmass : Summable (fun n : ℕ =>
      ∫ x in Ioi (0 : ℝ), F n x ∂volume)) :
    IntegrableOn (fun x : ℝ => ∑' n : ℕ, P n x)
      (Ioi (0 : ℝ)) volume := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hG : Integrable (fun x : ℝ => ∑' n : ℕ, F n x) μ :=
    nonnegative_integrable_tsum_of_summable_integrals μ F
      (fun n => hFL1 n) hFpos hFpoint hFmass
  have hPG : ∀ x : ℝ,
      ‖∑' n : ℕ, P n x‖ ≤ ∑' n : ℕ, F n x := by
    intro x
    apply tsum_of_norm_bounded (hFpoint x).hasSum
    intro n
    simpa only [Real.norm_eq_abs] using hDom n x
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ∑' n : ℕ, P n x) μ :=
    (AEMeasurable.tsum (fun n => (hPL1 n).aemeasurable)).aestronglyMeasurable
  exact Integrable.mono' hG hmeas (Filter.Eventually.of_forall hPG)
