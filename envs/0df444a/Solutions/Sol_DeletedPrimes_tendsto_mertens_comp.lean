-- Prove2me | solution 1 for DeletedPrimes.tendsto_mertens_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:55:27.541138+00:00
-- url     : https://prove2.me/submissions/832c69d7-dba0-4e3c-b5d6-eb86d83092fa

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {α m : ℝ} (hM : MertensLaw S α m) {u : ℝ → ℝ} {c : ℝ}
    (hu : Tendsto u atTop atTop)
    (hlog : Tendsto (fun x => Real.log (u x) / Real.log x) atTop (𝓝 c)) :
    Tendsto (fun x => mertensSum S α (u x) / Real.log x) atTop (𝓝 (m * c)) := by
  have h1 : Tendsto (fun x => mertensSum S α (u x) / Real.log (u x)) atTop (𝓝 m) := hM.comp hu
  refine (h1.mul hlog).congr' ?_
  filter_upwards [hu.eventually_gt_atTop 1] with x hx
  have : Real.log (u x) ≠ 0 := (Real.log_pos hx).ne'
  rw [div_mul_div_comm, mul_comm (mertensSum S α (u x)), mul_div_mul_left _ _ this]
end DeletedPrimes
