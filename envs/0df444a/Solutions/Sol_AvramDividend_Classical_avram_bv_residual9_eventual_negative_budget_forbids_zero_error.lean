-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_eventual_negative_budget_forbids_zero_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:06:59.991139+00:00
-- url     : https://prove2.me/submissions/880ef650-f2a9-4ea1-be40-3dc00ce74380

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- An eventually strict negative budget prevents vanishing expected positive error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (a ε : ℝ) (hε : 0 < ε)
    (M B E : ℕ → Ω → ℝ)
    (hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hE : ∀ n, Integrable (E n) P)
    (hBneg : ∀ᶠ n in atTop, (∫ ω, B n ω ∂P) ≤ -a - ε)
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      0 ≤ a + M n ω + B n ω + E n ω) :
    ¬ Tendsto (fun n => ∫ ω, E n ω ∂P) atTop (nhds (0 : ℝ)) := by
  classical
  intro hlim
  have hsmall : ∀ᶠ n in atTop, (∫ ω, E n ω ∂P) < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := (hBneg.and hsmall).exists
  rcases hn with ⟨hBn, hEn⟩
  have hconst : Integrable (fun _ : Ω => a) P := integrable_const a
  have hRhs : Integrable (fun ω => a + M n ω + B n ω + E n ω) P :=
    ((hconst.add (hM n).1).add (hB n)).add (hE n)
  have hnonneg :
      0 ≤ ∫ ω, a + M n ω + B n ω + E n ω ∂P :=
    integral_nonneg_of_ae (hbudget n)
  have hcalc :
      (∫ ω, a + M n ω + B n ω + E n ω ∂P) =
      a + (∫ ω, B n ω ∂P) + (∫ ω, E n ω ∂P) := by
    calc
      (∫ ω, a + M n ω + B n ω + E n ω ∂P) =
          (∫ ω, a + M n ω + B n ω ∂P) +
          (∫ ω, E n ω ∂P) := by
            exact integral_add ((hconst.add (hM n).1).add (hB n)) (hE n)
      _ = ((∫ ω, a + M n ω ∂P) + (∫ ω, B n ω ∂P)) +
          (∫ ω, E n ω ∂P) := by
            exact congrArg (fun z : ℝ => z + (∫ ω, E n ω ∂P))
              (integral_add (hconst.add (hM n).1) (hB n))
      _ = ((∫ ω, (a : ℝ) ∂P) + (∫ ω, M n ω ∂P)) +
          (∫ ω, B n ω ∂P) + (∫ ω, E n ω ∂P) := by
            exact congrArg (fun z : ℝ =>
              (z + (∫ ω, B n ω ∂P)) + (∫ ω, E n ω ∂P))
              (integral_add hconst (hM n).1)
      _ = a + (∫ ω, B n ω ∂P) + (∫ ω, E n ω ∂P) := by
            simp [(hM n).2]
  rw [hcalc] at hnonneg
  linarith
