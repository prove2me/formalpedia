-- Prove2me | solution 1 for FairChores.NineteenEighteenths.lamOf_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:06.803849+00:00
-- url     : https://prove2.me/submissions/2c6be79e-f07f-470b-9d61-270bc6fdeac5

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores
namespace FairChores.NineteenEighteenths
theorem _root_.solution {rho : ℝ} (hrho : rho < 19/18) : 2 ≤ lamOf rho := by
  have hden : 0 < 380 - 360 * rho := by linarith
  have : 0 ≤ 720 * |rho| / (380 - 360 * rho) :=
    div_nonneg (by positivity) hden.le
  simp only [lamOf]; linarith
end FairChores.NineteenEighteenths
