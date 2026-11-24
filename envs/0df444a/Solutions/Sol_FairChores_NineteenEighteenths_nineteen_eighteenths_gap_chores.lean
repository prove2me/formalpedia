-- Prove2me | solution 1 for FairChores.NineteenEighteenths.nineteen_eighteenths_gap_chores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:35:04.86367+00:00
-- url     : https://prove2.me/submissions/bb42345f-0a2c-4eac-b255-4a62ece30f22

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
import Theorems.Thm_FairChores_NineteenEighteenths_instP_nonneg
import Theorems.Thm_FairChores_NineteenEighteenths_instC_nonneg
import Theorems.Thm_FairChores_NineteenEighteenths_lamOf_ge_two
import Theorems.Thm_FairChores_NineteenEighteenths_no_rho_MMS_chores_three_eight

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores
namespace FairChores.NineteenEighteenths
theorem _root_.solution {rho : ℝ} (hrho : rho < 19/18) :
    ∃ (c : Fin 3 → Fin 8 → ℝ) (p : Fin 8 → ℝ),
      (∀ i t, 0 ≤ c i t) ∧ (∀ t, 0 ≤ p t) ∧
      ∀ o : Outcome (Fin 8) 3, o.Valid p →
        ∃ i, rho * MMS 3 (c i) p < cost (c i) o i := by
  have hlam2 : 2 ≤ lamOf rho := lamOf_ge_two hrho
  have hlam0 : (0:ℝ) ≤ lamOf rho := by linarith
  exact ⟨instC (lamOf rho), instP (lamOf rho), instC_nonneg hlam0, instP_nonneg hlam0,
    no_rho_MMS_chores_three_eight hrho⟩
end FairChores.NineteenEighteenths
