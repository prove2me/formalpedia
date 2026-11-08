-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_budget_expected_error_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:56:46.640316+00:00
-- url     : https://prove2.me/submissions/bd09ecc1-01f7-452c-8d34-51f8960cd7f4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A strict negative expected budget requires nonvanishing positive error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (a ε : ℝ) (hε : 0 < ε)
    (F M B E : ℕ → Ω → ℝ)
    (hF : ∀ n, Integrable (F n) P ∧ ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hE : ∀ n, Integrable (E n) P)
    (hBneg : ∀ n, (∫ ω, B n ω ∂P) ≤ -a - ε)
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + E n ω) :
    ∀ n, ε ≤ ∫ ω, E n ω ∂P := by
  classical
  intro n
  have h0 : 0 ≤ ∫ ω, F n ω ∂P :=
    integral_nonneg_of_ae (hF n).2
  have hMI := (hM n).1
  have hBI := hB n
  have hEI := hE n
  have hconst : Integrable (fun _ : Ω => a) P := integrable_const a
  have hbudgetInt :
      Integrable (fun ω => a + M n ω + B n ω + E n ω) P :=
    ((hconst.add hMI).add hBI).add hEI
  have hupper :
      (∫ ω, F n ω ∂P) ≤
        (∫ ω, a + M n ω + B n ω + E n ω ∂P) :=
    integral_mono_ae (hF n).1 hbudgetInt (hbudget n)
  have hcalc :
      (∫ ω, a + M n ω + B n ω + E n ω ∂P) =
        a + (∫ ω, B n ω ∂P) + (∫ ω, E n ω ∂P) := by
    calc
      (∫ ω, a + M n ω + B n ω + E n ω ∂P) =
          (∫ ω, a + M n ω + B n ω ∂P) + (∫ ω, E n ω ∂P) := by
            exact integral_add ((hconst.add hMI).add hBI) hEI
      _ = ((∫ ω, a + M n ω ∂P) + (∫ ω, B n ω ∂P)) +
          (∫ ω, E n ω ∂P) := by
            exact congrArg (fun z : ℝ => z + (∫ ω, E n ω ∂P))
              (integral_add (hconst.add hMI) hBI)
      _ = ((∫ ω, (a : ℝ) ∂P) + (∫ ω, M n ω ∂P)) +
          (∫ ω, B n ω ∂P) + (∫ ω, E n ω ∂P) := by
            exact congrArg (fun z : ℝ =>
              (z + (∫ ω, B n ω ∂P)) + (∫ ω, E n ω ∂P))
              (integral_add hconst hMI)
      _ = a + (∫ ω, B n ω ∂P) + (∫ ω, E n ω ∂P) := by
            simp [(hM n).2]
  rw [hcalc] at hupper
  linarith [hBneg n]
