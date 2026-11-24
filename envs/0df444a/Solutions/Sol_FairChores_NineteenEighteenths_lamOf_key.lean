-- Prove2me | solution 1 for FairChores.NineteenEighteenths.lamOf_key
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:30:53.173369+00:00
-- url     : https://prove2.me/submissions/239f5c9d-a218-4f63-8407-da2102c524fa

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores


theorem solution {rho : ℝ} (hrho : rho < 19/18) : 720 * rho < lamOf rho * (380 - 360 * rho) := by
  have h : 0 < 380-360*rho := by linarith
  have he : lamOf rho * (380-360*rho) = 2*(380-360*rho)+720*|rho| := by
    unfold lamOf; field_simp <;> ring
  rw [he]; linarith [le_abs_self rho]
