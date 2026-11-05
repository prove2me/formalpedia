-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f2_void_probability_factorial_integral_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:32:39.213369+00:00
-- url     : https://prove2.me/submissions/879fa0c5-3b13-4eae-bcd6-e57e1fc8e975

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_void_indicator_bonferroni_nat

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- Integrating the Bonferroni sandwich gives an actual void-probability bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hKm : Measurable K)
    (hFirst : Integrable (fun ω => (K ω : ℝ)) P)
    (hFactorial : Integrable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P) :
    (∫ ω, (K ω : ℝ) ∂P) -
        (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) / 2 ≤
      P.real {ω : Ω | K ω ≠ 0} ∧
    P.real {ω : Ω | K ω ≠ 0} ≤
      (∫ ω, (K ω : ℝ) ∂P) := by
  have hzero : MeasurableSet {ω : Ω | K ω = 0} := by
    change MeasurableSet (K ⁻¹' ({0} : Set ℕ))
    exact hKm (measurableSet_singleton 0)
  have hnonzero : MeasurableSet {ω : Ω | K ω ≠ 0} := by
    simpa [Set.compl_setOf] using hzero.compl
  have hif : (fun ω : Ω => if K ω = 0 then (0 : ℝ) else 1) =
      ({ω : Ω | K ω ≠ 0}).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hz : K ω = 0 <;> simp [Set.indicator, hz]
  have hIntIf : Integrable
      (fun ω : Ω => if K ω = 0 then (0 : ℝ) else 1) P := by
    rw [hif]
    exact (integrable_const (1 : ℝ)).indicator hnonzero
  have hifIntegral :
      (∫ ω, (if K ω = 0 then (0 : ℝ) else 1) ∂P) =
        P.real {ω : Ω | K ω ≠ 0} := by
    rw [hif]
    exact integral_indicator_one hnonzero
  have hLower : Integrable
      (fun ω => (K ω : ℝ) -
        ((K ω : ℝ) * ((K ω : ℝ) - 1)) / 2) P :=
    hFirst.sub (hFactorial.div_const 2)
  have hle := integral_mono_ae hLower hIntIf
    (Filter.Eventually.of_forall (fun ω =>
      (avram_p4_f2_void_indicator_bonferroni_nat (K ω)).1))
  have hhi := integral_mono_ae hIntIf hFirst
    (Filter.Eventually.of_forall (fun ω =>
      (avram_p4_f2_void_indicator_bonferroni_nat (K ω)).2))
  constructor
  · rw [integral_sub hFirst (hFactorial.div_const 2),
        integral_div, hifIntegral] at hle
    exact hle
  · rw [← hifIntegral]
    exact hhi
