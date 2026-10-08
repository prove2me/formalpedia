-- Prove2me | solution 1 for AvramDividend.Classical.verification_candidate_lump_sum_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:27:42.589742+00:00
-- url     : https://prove2.me/submissions/0d110ac3-88ea-4728-8578-33efb8e40ecc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (w : ℝ → ℝ) (u δ : ℝ) (hδ : 0 ≤ δ)
    (hcont : ContinuousOn w (Icc (u - δ) u))
    (hdiff : DifferentiableOn ℝ w (Ioo (u - δ) u))
    (hderiv : ∀ y ∈ Ioo (u - δ) u, 1 ≤ deriv w y) :
    δ ≤ w u - w (u - δ) := by
  have hle : u - δ ≤ u := sub_le_self u hδ
  have hm : MonotoneOn (fun y => w y - y) (Icc (u - δ) u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (u - δ) u)
    · exact hcont.sub continuousOn_id
    · rw [interior_Icc]
      convert! hdiff.sub differentiableOn_id using 1
    · intro y hy
      have hy' : y ∈ Ioo (u - δ) u := by
        simpa only [interior_Icc] using hy
      have hd := (hdiff.differentiableAt (isOpen_Ioo.mem_nhds hy')).hasDerivAt
      have he := hd.sub (hasDerivAt_id y)
      have he' : HasDerivAt (fun z => w z - z) (deriv w y - 1) y := by
        convert! he using 1
      rw [he'.deriv]
      linarith [hderiv y hy']
  have hh := hm ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
  dsimp at hh
  linarith
