-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_interior_gradient_one_secant_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:01:38.093834+00:00
-- url     : https://prove2.me/submissions/7d17aaab-18f4-44e8-bace-0793ccab846b

import Mathlib
open Set

/-- An HJB interior derivative at least one yields the exact dividend secant inequality. -/
theorem solution
    (w : ℝ → ℝ) (y z : ℝ) (hyz : y ≤ z)
    (hcont : ContinuousOn w (Icc y z))
    (hdiff : DifferentiableOn ℝ w (Ioo y z))
    (hgrad : ∀ t ∈ Ioo y z, 1 ≤ deriv w t) :
    z - y ≤ w z - w y  := by
  have hMon : MonotoneOn (w - id) (Icc y z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y z)
    · exact hcont.sub continuousOn_id
    · simpa only [interior_Icc] using
        (hdiff.sub differentiableOn_id)
    · intro t ht
      have ht' : t ∈ Ioo y z := by simpa only [interior_Icc] using ht
      have hwd : DifferentiableAt ℝ w t :=
        (hdiff t ht').differentiableAt (isOpen_Ioo.mem_nhds ht')
      have hDer : deriv (w - id) t = deriv w t - 1 := by
        simpa only [deriv_id] using (deriv_sub hwd differentiableAt_id)
      rw [hDer]
      linarith [hgrad t ht']
  have hValue := hMon (left_mem_Icc.mpr hyz)
    (right_mem_Icc.mpr hyz) hyz
  simp only [Pi.sub_apply, id_eq] at hValue
  linarith
