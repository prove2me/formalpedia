-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_quadratic_absolute_Young_expected_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:13:24.181501+00:00
-- url     : https://prove2.me/submissions/f1861767-54fa-4936-8c6e-0c83eb29e4c0

import Mathlib
open MeasureTheory Filter
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ)
    (hAbs : Integrable (fun ω => |f ω|) P)
    (hSq : Integrable (fun ω => (f ω) ^ 2) P)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ ω, |f ω| ∂P) ≤
      (∫ ω, (f ω) ^ 2 ∂P) / (2 * ε) + ε / 2 := by
  have hpoint (ω : Ω) :
      |f ω| ≤ (f ω) ^ 2 / (2 * ε) + ε / 2 := by
    have hsq := sq_nonneg (|f ω| - ε)
    have heq : |f ω| ^ 2 = (f ω) ^ 2 := sq_abs _
    have hd : 0 < 2 * ε := by positivity
    calc
      |f ω| ≤ ((f ω) ^ 2 + ε ^ 2) / (2 * ε) := by
        apply (le_div_iff₀ hd).2
        nlinarith
      _ = (f ω) ^ 2 / (2 * ε) + ε / 2 := by
        have hne : ε ≠ 0 := ne_of_gt hε
        field_simp
  have hRight : Integrable
      (fun ω => (f ω) ^ 2 / (2 * ε) + ε / 2) P :=
    (hSq.div_const _).add (integrable_const _)
  calc
    (∫ ω, |f ω| ∂P) ≤
        ∫ ω, ((f ω) ^ 2 / (2 * ε) + ε / 2) ∂P := by
      exact integral_mono_ae hAbs hRight
        (Filter.Eventually.of_forall hpoint)
    _ = (∫ ω, (f ω) ^ 2 ∂P) / (2 * ε) + ε / 2 := by
      simp only [div_eq_mul_inv]
      rw [integral_add (hSq.mul_const _) (integrable_const _)]
      rw [integral_mul_const]
      simp
