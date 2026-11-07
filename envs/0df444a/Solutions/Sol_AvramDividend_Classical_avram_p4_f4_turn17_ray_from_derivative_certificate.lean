-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn17_ray_from_derivative_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:35:48.008724+00:00
-- url     : https://prove2.me/submissions/070daad4-abd9-40a9-a91c-3463a64fe1db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_inhomogeneous_first_order_upper
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (rpos rneg : ℝ) (hrpos : 0 < rpos) (hrneg : rneg < 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hODE : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      iteratedDeriv 2 w y - (rpos + rneg) * deriv w y + rpos * rneg * w y ≤ 0)
    (hCert : ∀ y : ℝ, 1 ≤ y →
      deriv w y - rpos * w y ≤
        (deriv w 1 - rpos * w 1) * Real.exp (rneg * (y - 1))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      w y ≤ K * Real.exp (rpos * y) := by
  have hwContOne : ContinuousOn w (Ici (1 : ℝ)) :=
    hw_cont.mono (by
      intro y hy
      exact mem_Ici.mpr (by have := (mem_Ici.mp hy); linarith))
  have hwSmoothOne : ContDiffOn ℝ 2 w (Ioi (1 : ℝ)) :=
    hw_smooth.mono (by
      intro y hy
      change 1 < y at hy
      change 0 < y ∧ ENNReal.ofReal y < C
      refine ⟨by linarith, ?_⟩
      simp [hTop])
  have hwDiffOne : DifferentiableOn ℝ w (Ioi (1 : ℝ)) :=
    hwSmoothOne.differentiableOn (by norm_num)
  let B : ℝ := max 0 (deriv w 1 - rpos * w 1)
  have hB : 0 ≤ B := le_max_left _ _
  have hgB : deriv w 1 - rpos * w 1 ≤ B := le_max_right _ _
  have hDer : ∀ t : ℝ, 1 < t →
      deriv w t ≤ rpos * w t + B * Real.exp (rneg * (t - 1)) := by
    intro t ht
    have hCertT := hCert t (le_of_lt ht)
    have hScale := mul_le_mul_of_nonneg_right hgB
      (le_of_lt (Real.exp_pos (rneg * (t - 1))))
    linarith
  have hBase :=
    AvramDividend.Classical.avram_p4_f4_turn17_inhomogeneous_first_order_upper
      rpos rneg 1 (by linarith : rneg < rpos)
      w hwContOne hwDiffOne B hB hDer
  let A : ℝ := w 1 + B / (rpos - rneg)
  let K : ℝ := max 0 (A * Real.exp (-rpos))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro y hy
  have hBound : w y ≤ A * Real.exp (rpos * (y - 1)) :=
    hBase y hy
  calc
    w y ≤ A * Real.exp (rpos * (y - 1)) := hBound
    _ = (A * Real.exp (-rpos)) * Real.exp (rpos * y) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ ≤ K * Real.exp (rpos * y) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (Real.exp_pos _))
