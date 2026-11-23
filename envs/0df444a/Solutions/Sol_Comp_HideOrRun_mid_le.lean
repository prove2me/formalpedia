-- Prove2me | solution 1 for Comp.HideOrRun.mid_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:50:31.047662+00:00
-- url     : https://prove2.me/submissions/182f0c17-9cd7-4916-aec2-b689fa8d1161

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_hr_LW
import Theorems.Thm_Comp_HideOrRun_lpre1F_eq_lpre1C
import Theorems.Thm_Comp_CsgQ_le_lfInner_of_step


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution (b y : Finset HR) (m : ℕ) :
    (↑((midStep b y)^[m] ∅) : Set HR) ≤ ((game.toCSG game_wf).LFInner ↑b ↑y).lfp := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      set x := (midStep b y)^[m] ∅ with hx
      refine CsgQ.le_lfInner_of_step game game_wf b y x (midStep b y x)
        (fun s => lwC x y s) (fun s => hr_LW x y s) ih ?_
      unfold midStep
      rw [lpre1F_eq_lpre1C]
end Comp.HideOrRun
