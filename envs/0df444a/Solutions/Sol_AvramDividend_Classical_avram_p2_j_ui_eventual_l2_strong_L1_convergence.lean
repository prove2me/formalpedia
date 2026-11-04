-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_eventual_l2_strong_L1_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:41:18.498745+00:00
-- url     : https://prove2.me/submissions/d93873c3-ffa1-49c1-a739-53dd3b2da732

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_strong_L1_convergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Finite initial exceptional L² moments preserve strong L¹ convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    MemLp Z 1 P ∧
      Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) := by
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
  have h := avram_p2_j_ui_l2_ae_strong_L1_convergence
    P (fun n ω => Y (n + N) ω) Z B hmShift hBShift haeShift
  refine ⟨h.1, ?_⟩
  exact (Filter.tendsto_add_atTop_iff_nat N).1 h.2
