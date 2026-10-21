-- Prove2me | solution 1 for BellRegret.Paradoxes.display5_of_ratio_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:44:11.899073+00:00
-- url     : https://prove2.me/submissions/92c50460-be4f-4378-8c3c-dee44d105c6c

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem solution (f : ℝ → ℝ) (p : ℝ)
    (hf : StrictMonoOn (fun x => (f x - f (-x)) / x) (Set.Ioi 0))
    (hp0 : 0 < p) (hp : p < 1 / 2) :
    p * (f (1 - p) - f (p - 1)) > (1 - p) * (f p - f (-p)) := by
  have h := hf (show p ∈ Set.Ioi (0:ℝ) from hp0)
    (show 1 - p ∈ Set.Ioi (0:ℝ) from by simp only [Set.mem_Ioi]; linarith) (by linarith)
  simp only at h
  have e : -(1 - p) = p - 1 := by ring
  rw [e, div_lt_div_iff₀ hp0 (by linarith)] at h
  linarith
