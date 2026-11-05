-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:07:36.485089+00:00
-- url     : https://prove2.me/submissions/81b5ecfd-6ba6-45cd-8378-5786a0ab1522

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_source_HJB_strict_cap_band_open
open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Canonical original strict-cap C1 regularity yields its compact derivative bound. -/
theorem solution
(C : ℝ≥0∞) (w : ℝ → ℝ) (a b : ℝ)
(ha : 0 < a) (hab : a ≤ b) (hbC : ENNReal.ofReal b < C)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
∃ A : ℝ, 0 ≤ A ∧ ∀ y ∈ Set.Icc a b, |deriv w y| ≤ A := by
  obtain ⟨hOpen, hBand⟩ :=
    avram_p3_e_compensator_source_HJB_strict_cap_band_open
      C a b ha hab hbC
  have hhalf : a / 2 ≤ a := by linarith
  have hSub : Set.Icc a b ⊆ Set.Icc (a / 2) b := by
    intro y hy
    exact ⟨le_trans hhalf hy.1, hy.2⟩
  have hDerivCont : ContinuousOn (deriv w) (Set.Icc a b) :=
    (hw_smooth.continuousOn_deriv_of_isOpen hOpen (by norm_num)).mono
      (Set.Subset.trans hSub hBand)
  obtain ⟨A, hA⟩ :=
    (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
      hDerivCont
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro y hy
  have hbound : |deriv w y| ≤ A := by
    simpa only [Real.norm_eq_abs] using hA y hy
  exact le_trans hbound (le_max_left _ _)
