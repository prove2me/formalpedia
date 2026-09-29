-- Prove2me | solution 1 for BraidsLinksMCG.adjacent_pairConfig_configIncl_coords_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T18:43:05.020484+00:00
-- url     : https://prove2.me/submissions/0838797a-61f8-4c29-9b9a-37d1e508fea0

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
open BraidsLinksMCG

theorem solution (n : ℕ) (z : PuncturedPlane (n + 1)) :
    (configIncl (n + 1) z).1 =
      Fin.snoc (Fin.snoc (fun k : Fin n => ((k : ℕ) + 1 : ℂ))
        (((n : ℝ) + 1 : ℝ) : ℂ)) z.1 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [configIncl, Fin.snoc_last]
  | cast j =>
      induction j using Fin.lastCases with
      | last => simp [configIncl, Fin.snoc_castSucc, Fin.snoc_last]
      | cast k => simp [configIncl, Fin.snoc_castSucc]
