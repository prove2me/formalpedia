-- Prove2me | solution 1 for FairChores.NineteenEighteenths.instP_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:59.350932+00:00
-- url     : https://prove2.me/submissions/73a275a8-d36f-4021-97fa-1c42b806f3a9

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
import Theorems.Thm_FairChores_NineteenEighteenths_cast_sum_eq
import Theorems.Thm_FairChores_FeigeNorkinChores_fcU_total


set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores
namespace FairChores.NineteenEighteenths
theorem _root_.solution (lam : ℝ) : (∑ t, instP lam t) = 1080 * lam := by
  have h : (∑ t, instP lam t) = lam * ∑ t, (fcU t : ℝ) := by
    rw [Finset.mul_sum]; rfl
  rw [h, cast_sum_eq Finset.univ fcU 1080 fcU_total]
  ring
end FairChores.NineteenEighteenths
