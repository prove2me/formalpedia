-- Prove2me | solution 1 for FairChores.NineteenEighteenths.C_le_instP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:29:13.248359+00:00
-- url     : https://prove2.me/submissions/1328c304-ee8b-4120-b06d-cd6e57e41780

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
theorem _root_.solution {lam : ℝ} (hlam : 2 ≤ lam) (t : Fin 8) : (fcC t : ℝ) ≤ instP lam t := by
  have h1 : (fcC t : ℝ) ≤ 2 * (fcU t : ℝ) := by
    have := (two_fcU_dominates t).2
    exact_mod_cast this
  have h2 : 2 * (fcU t : ℝ) ≤ lam * (fcU t : ℝ) :=
    mul_le_mul_of_nonneg_right hlam (by positivity)
  simpa [instP] using h1.trans h2
end FairChores.NineteenEighteenths
