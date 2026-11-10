-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:07:48.353759+00:00
-- url     : https://prove2.me/submissions/8b71b3b5-1873-41af-8ffe-89edf64408b1

import Mathlib
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_countably_observed_negative_cutoff_first_clock_stopping
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_dense_observed_first_clock_eq_actual_negative_jump_inf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original first negative source jump is observable by the stopped history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω =>
        ⨅ u : ℝ≥0,
          if 0 < u ∧
              X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
          then (u : WithTop ℝ≥0) else ⊤) := by
  classical
  obtain ⟨r, hdense⟩ := TopologicalSpace.exists_dense_seq (ℝ≥0)
  have hr : ∀ u v : ℝ≥0, u < v →
      ∃ k : ℕ, u < r k ∧ r k < v := by
    intro u v huv
    obtain ⟨k, hk⟩ :=
      hdense.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr huv)
    exact ⟨k, hk.1, hk.2⟩
  let pastCount : ℕ → ℕ → Ω → ℝ := fun n k ξ =>
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ξ -
        Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ξ -
          Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u)))
      (Ioc 0 (r k) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
  have hObserved : IsStoppingTime 𝓕.rightCont
      (fun ξ : Ω => ⨅ n : ℕ, ⨅ k : ℕ,
        if 0 < pastCount n k ξ
        then (r k : WithTop ℝ≥0) else ⊤) :=
    avram_bv_zero13_original_countably_observed_negative_cutoff_first_clock_stopping
      X hBV hFinite r
  have hSame :
      (fun ξ : Ω => ⨅ n : ℕ, ⨅ k : ℕ,
        if 0 < pastCount n k ξ
        then (r k : WithTop ℝ≥0) else ⊤) =
      (fun ξ : Ω => ⨅ u : ℝ≥0,
        if 0 < u ∧ X.X u ξ -
            Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u < 0
        then (u : WithTop ℝ≥0) else ⊤) := by
    funext ξ
    exact
      avram_bv_zero13_original_dense_observed_first_clock_eq_actual_negative_jump_inf
        X r hr ξ
  rw [← hSame]
  exact hObserved
