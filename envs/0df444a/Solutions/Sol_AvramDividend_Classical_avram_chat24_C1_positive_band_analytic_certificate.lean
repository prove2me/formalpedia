-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_C1_positive_band_analytic_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:04:31.062316+00:00
-- url     : https://prove2.me/submissions/2df5dd74-a86a-4129-a8b9-5164e2f236c1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (a b d q : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Measurable w ∧ ContinuousOn (fun y => d * deriv w y - q * w y) (Icc a b) ∧
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b, |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by
  have hmeas : Measurable w := by
    have hc : Continuous (fun y : ℝ => w (max y 0)) :=
      hw_cont.comp_continuous (continuous_id.max continuous_const) (fun y => le_max_right y 0)
    have heq : w = (fun y : ℝ => if y < 0 then 0 else w (max y 0)) := by
      funext y
      by_cases hy : y < 0
      · simp [hy, hw_neg y hy]
      · simp [hy, max_eq_left (le_of_not_gt hy)]
    rw [heq]
    exact measurable_const.ite measurableSet_Iio hc.measurable
  have hcont : ContinuousOn (fun y => d * deriv w y - q * w y) (Icc a b) :=
    ((hw.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).const_mul d |>.sub
      (hw.continuousOn.const_mul q)).mono (fun y hy => lt_of_lt_of_le ha hy.1)
  have hs : Icc (a / 2) b ⊆ Ioi (0 : ℝ) := fun y hy => by
    have := hy.1
    change 0 < y
    linarith
  obtain ⟨L, hLip⟩ := (hw.mono hs).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw_cont.mono (show Icc (0 : ℝ) b ⊆ Ici 0 from fun y hy => hy.1))
  refine ⟨hmeas, hcont, L, max R 0, L.coe_nonneg, le_max_right _ _, ?_, ?_⟩
  · intro u hu v hv
    simpa only [Real.dist_eq] using hLip.dist_le_mul u hu v hv
  · intro v hv
    by_cases hv0 : v < 0
    · simp [hw_neg v hv0]
    · have hb : |w v| ≤ R := by
        simpa only [Real.norm_eq_abs] using hR v ⟨le_of_not_gt hv0, hv⟩
      exact hb.trans (le_max_left _ _)
