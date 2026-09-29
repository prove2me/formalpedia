-- Prove2me | solution 1 for Erdos180.flipBooleanColor_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:25:25.645988+00:00
-- url     : https://prove2.me/submissions/767746d0-fe6b-4a43-9010-2f6c55248413

import Definitions.Def_erdos180_core4
import Mathlib.Logic.Function.Basic

open Erdos180
open Finset SimpleGraph
open scoped Classical

@[simp]
theorem solution {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) :
    flipBooleanColor color v v = ! color v := by
  simp [flipBooleanColor]
