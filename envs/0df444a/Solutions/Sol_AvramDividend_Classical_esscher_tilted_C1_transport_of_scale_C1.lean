-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilted_C1_transport_of_scale_C1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:35:29.886913+00:00
-- url     : https://prove2.me/submissions/20bd87a9-587f-4888-bad4-0006e4140a5f

import Mathlib

open Set
open scoped NNReal ENNReal
theorem solution
    (W V : ℝ → ℝ) (φ : ℝ)
    (hW : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  have h : ContDiffOn ℝ 1 (fun x => Real.exp (-(φ * x)) * W x) (Ioi (0 : ℝ)) :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg).contDiffOn).mul hW
  exact h.congr (fun x hx => hV x hx)
