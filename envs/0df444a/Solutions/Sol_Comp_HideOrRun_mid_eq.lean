-- Prove2me | solution 1 for Comp.HideOrRun.mid_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:55.268683+00:00
-- url     : https://prove2.me/submissions/ce610677-2a56-4763-96dd-fc8d9589e98f

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_hr_LW
import Theorems.Thm_Comp_HideOrRun_lpre1F_eq_lpre1C
import Theorems.Thm_Comp_HideOrRun_mid_le
import Theorems.Thm_Comp_CsgQ_lfInner_eq_coe_of_fixed


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution (b y c : Finset HR) (m : ℕ) (hiter : (midStep b y)^[m] ∅ = c)
    (hfix : midStep b y c = c) :
    ((game.toCSG game_wf).LFInner ↑b ↑y).lfp = (↑c : Set HR) := by
  have hle : (↑c : Set HR) ≤ ((game.toCSG game_wf).LFInner ↑b ↑y).lfp := by
    have h := mid_le b y m
    rwa [hiter] at h
  refine CsgQ.lfInner_eq_coe_of_fixed game game_wf b y c (fun s => lwC c y s)
    (fun s => hr_LW c y s) ?_ hle
  rw [lpre1F_eq_lpre1C]
  exact hfix.symm
end Comp.HideOrRun
