-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_eventual_l2_ae_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:51:03.641202+00:00
-- url     : https://prove2.me/submissions/e34a2221-b53f-472d-b3b6-dc68535d5cc5

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_expectations_direct

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! A finite set of exceptional second-moment indices does not affect convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  have hmShift : ∀ n, AEStronglyMeasurable (Y (n + N)) P := by
    intro n
    exact hm (n + N)
  have hBShift : ∀ n, eLpNorm (Y (n + N)) 2 P ≤ (B : ENNReal) := by
    intro n
    exact hB (n + N) (by omega)
  have haeShift :
      ∀ᵐ ω ∂P, Tendsto (fun n => Y (n + N) ω) atTop (nhds (Z ω)) := by
    filter_upwards [hae] with ω hω
    exact (Filter.tendsto_add_atTop_iff_nat N).2 hω
  have h := avram_p2_j_ui_l2_ae_expectations_direct
    P (fun n ω => Y (n + N) ω) Z B hmShift hBShift haeShift
  refine ⟨h.1, ?_⟩
  exact (Filter.tendsto_add_atTop_iff_nat N).1 h.2
