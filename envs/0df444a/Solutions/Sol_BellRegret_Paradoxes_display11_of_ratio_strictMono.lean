-- Prove2me | solution 1 for BellRegret.Paradoxes.display11_of_ratio_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:44:10.90591+00:00
-- url     : https://prove2.me/submissions/00e7da35-96fb-46c6-97ad-7a5e84040449

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem solution (f : ℝ → ℝ) (p : ℝ)
    (hf : StrictMonoOn (fun x => (f x - f (-x)) / x) (Set.Ioi 0)) (hp : 0 < p) :
    f (p / 2) - f (-p / 2) < 1 / 2 * (f p - f (-p)) := by
  have h := hf (show p / 2 ∈ Set.Ioi (0:ℝ) from by simp only [Set.mem_Ioi]; linarith)
    (show p ∈ Set.Ioi (0:ℝ) from hp) (by linarith)
  simp only at h
  have e : -(p / 2) = -p / 2 := by ring
  rw [e, div_lt_div_iff₀ (by linarith) hp] at h
  nlinarith
