-- Prove2me | solution 2 for FairChores.NineteenEighteenths.lamOf_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:29:13.744248+00:00
-- url     : https://prove2.me/submissions/b976c8e3-3bde-4269-b565-d7b9829070ac

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
theorem _root_.solution {rho : ℝ} (hrho : rho < 19/18) : 720 * rho < lamOf rho * (380 - 360 * rho) := by
  have hden : 0 < 380 - 360 * rho := by linarith
  have hfrac : 720 * |rho| / (380 - 360 * rho) * (380 - 360 * rho) = 720 * |rho| := by
    field_simp
  have habs : rho ≤ |rho| := le_abs_self rho
  have hexp : lamOf rho * (380 - 360 * rho)
      = 2 * (380 - 360 * rho) + 720 * |rho| := by
    simp only [lamOf, add_mul, hfrac]
  rw [hexp]
  nlinarith [habs, hden]
end FairChores.NineteenEighteenths
