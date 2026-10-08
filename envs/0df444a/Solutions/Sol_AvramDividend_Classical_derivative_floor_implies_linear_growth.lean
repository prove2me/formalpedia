-- Prove2me | solution 1 for AvramDividend.Classical.derivative_floor_implies_linear_growth
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:01:32.602236+00:00
-- url     : https://prove2.me/submissions/f291edc4-2578-4534-a6c6-923ea9a76f11

import Mathlib

open Set

theorem solution
    (w : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hcont : ContinuousOn w (Icc 0 a))
    (hdiff : DifferentiableOn ℝ w (Ioo 0 a))
    (hderiv : ∀ y ∈ Ioo (0 : ℝ) a, 1 ≤ deriv w y)
    (hw0 : 0 ≤ w 0) : a ≤ w a := by
  have hm : MonotoneOn (fun y => w y - y) (Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a)
    · exact hcont.sub continuousOn_id
    · rw [interior_Icc]
      convert! hdiff.sub differentiableOn_id using 1
    · intro y hy
      have hy' : y ∈ Ioo (0 : ℝ) a := by simpa only [interior_Icc] using hy
      have hd := (hdiff.differentiableAt (isOpen_Ioo.mem_nhds hy')).hasDerivAt
      have he := hd.sub (hasDerivAt_id y)
      have he' : HasDerivAt (fun z => w z - z) (deriv w y - 1) y := by
        convert! he using 1
      rw [he'.deriv]
      linarith [hderiv y hy']
  have hh := hm ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  dsimp at hh
  linarith

#print axioms solution
