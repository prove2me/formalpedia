-- Prove2me | solution 1 for FairChores.NineteenEighteenths.R_le_instP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:13.382799+00:00
-- url     : https://prove2.me/submissions/4c0cbdb9-fb5a-49f4-9c40-16bb14291c98

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
import Theorems.Thm_FairChores_FeigeNorkinChores_two_fcU_dominates
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores
namespace FairChores.NineteenEighteenths
theorem _root_.solution {lam : ℝ} (hlam : 2 ≤ lam) (t : Fin 8) : (fcR t : ℝ) ≤ instP lam t := by
  have h1 : (fcR t : ℝ) ≤ 2 * (fcU t : ℝ) := by
    have := (two_fcU_dominates t).1
    exact_mod_cast this
  have h2 : 2 * (fcU t : ℝ) ≤ lam * (fcU t : ℝ) :=
    mul_le_mul_of_nonneg_right hlam (by positivity)
  simpa [instP] using h1.trans h2
end FairChores.NineteenEighteenths
