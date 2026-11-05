-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_C1_open_interior_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:30:30.379894+00:00
-- url     : https://prove2.me/submissions/0aeef383-ffdf-443c-b732-f944e4badd92

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_compact_interior_Lipschitz_of_continuous_derivative
open Set Topology AvramDividend.Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
(w : ℝ → ℝ) (a b : ℝ) (hab : a / 2 ≤ b)
(U : Set ℝ) (hUopen : IsOpen U)
(hw_smooth : ContDiffOn ℝ 1 w U)
(hsub : Set.Icc (a / 2) b ⊆ U) :
∃ L : ℝ, 0 ≤ L ∧
  ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v| := by
  have hdiff : ∀ y ∈ Icc (a / 2) b, DifferentiableAt ℝ w y := by
    intro y hy
    have hyU : y ∈ U := hsub hy
    exact (hw_smooth.differentiableOn_one y hyU).differentiableAt
      (hUopen.mem_nhds hyU)
  have hcontU : ContinuousOn (deriv w) U :=
    hw_smooth.continuousOn_deriv_of_isOpen hUopen (le_refl 1)
  exact avram_p3_e_compensator_compact_interior_Lipschitz_of_continuous_derivative
    w a b hab hdiff (hcontU.mono hsub)
