-- Prove2me | solution 1 for GDGen3.referenceXi_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:32:22.841272+00:00
-- url     : https://prove2.me/submissions/3115d319-85ea-498e-9764-171de5103413

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) : referenceXi r 0 = 0 := by
  simp [referenceXi]
