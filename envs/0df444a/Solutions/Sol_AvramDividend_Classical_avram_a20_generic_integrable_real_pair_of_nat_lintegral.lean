-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_generic_integrable_real_pair_of_nat_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:16:00.922849+00:00
-- url     : https://prove2.me/submissions/cd05d314-f0ed-4ef1-bf5b-7ce375627703

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (r : ℝ)
    (hmeas : AEMeasurable (fun ω => (K ω : ℝ≥0∞)) P)
    (hmean : (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) =
      ENNReal.ofReal (r ^ 2 / 2)) :
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by
  have hfin : (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) ≠ ⊤ := by
    rw [hmean]
    exact ENNReal.ofReal_ne_top
  have hInt : Integrable (fun ω => ((K ω : ℝ≥0∞)).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hmeas hfin
  have hKfinite : ∀ᵐ ω ∂P, (K ω : ℝ≥0∞) < ⊤ :=
    Filter.Eventually.of_forall (fun ω => by simp)
  have hIntegral :
      (∫ ω, ((K ω : ℝ≥0∞)).toReal ∂P) =
      (∫⁻ ω, (K ω : ℝ≥0∞) ∂P).toReal :=
    integral_toReal hmeas hKfinite
  constructor
  · simpa only [ENNReal.toReal_natCast] using hInt.const_mul 2
  · calc
      (∫ ω, 2 * (K ω : ℝ) ∂P) =
        2 * (∫ ω, ((K ω : ℝ≥0∞)).toReal ∂P) := by
          simp_rw [ENNReal.toReal_natCast]
          rw [integral_const_mul]
      _ = 2 * (ENNReal.ofReal (r ^ 2 / 2)).toReal := by
        rw [hIntegral, hmean]
      _ = r ^ 2 := by
        rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ r ^ 2 / 2)]
        ring
