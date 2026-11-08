-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux20_finite_mark_simple_eapprox_supr
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:57:12.197568+00:00
-- url     : https://prove2.me/submissions/0ee64149-cc3f-4210-84fe-841ccdff832e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux20_monotone_finite_mark_sum_iSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! The finite physical support makes monotone simple approximation exact. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (S : Finset α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (⨆ n : ℕ, ∑ a ∈ S, MeasureTheory.SimpleFunc.eapprox f n a) =
      ∑ a ∈ S, f a := by
  classical
  have hm : ∀ a, Monotone (fun n : ℕ => MeasureTheory.SimpleFunc.eapprox f n a) := by
    intro a i j hij
    exact (MeasureTheory.SimpleFunc.monotone_eapprox f hij) a
  rw [avram_redux20_monotone_finite_mark_sum_iSup
    S (fun n a => MeasureTheory.SimpleFunc.eapprox f n a) hm]
  apply Finset.sum_congr rfl
  intro a ha
  exact MeasureTheory.SimpleFunc.iSup_eapprox_apply hf a
