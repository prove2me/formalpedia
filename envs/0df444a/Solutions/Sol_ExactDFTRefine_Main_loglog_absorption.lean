-- Prove2me | solution 1 for ExactDFTRefine.Main.loglog_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:46:48.54934+00:00
-- url     : https://prove2.me/submissions/9b887956-f553-4caf-84d4-47adfc9f118f

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

open Asymptotics Filter
namespace ExactDFTRefine.Main

theorem _root_.solution :
    0 < beta - delta ∧
    (fun n : ℕ => Real.log (Real.log (n : ℝ)) ^ 2) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ) ^ (beta - delta)) := by
  have hpos : 0 < beta - delta := by
    norm_num [beta, delta]
  refine ⟨hpos, ?_⟩
  have hbase : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop] (fun x : ℝ => x ^ (beta - delta)) :=
    isLittleO_log_rpow_rpow_atTop 2 hpos
  have hinner : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcomp := hbase.comp_tendsto hinner
  -- hcomp : (fun n => log (log n)^(2:ℝ)) =o (fun n => (log n) ^ (beta - delta))
  -- convert nat power to rpow: log(log n)^2 = log(log n)^(2:ℝ)
  have hcongr : (fun n : ℕ => Real.log (Real.log (n : ℝ)) ^ 2)
      = (fun n : ℕ => Real.log (Real.log (n : ℝ)) ^ (2 : ℝ)) := by
    funext n
    norm_num
  rw [hcongr]
  exact hcomp

end ExactDFTRefine.Main
