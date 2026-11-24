-- Prove2me | solution 1 for FairChores.NineteenEighteenths.no_MMS_approx_below_nineteen_eighteenths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:50.888416+00:00
-- url     : https://prove2.me/submissions/33c75705-d930-49a9-b741-d3049b1bfa85

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
import Theorems.Thm_FairChores_NineteenEighteenths_nineteen_eighteenths_gap_chores

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores
namespace FairChores.NineteenEighteenths
theorem _root_.solution {eps : ℝ} (heps : 0 < eps) :
    ∃ (c : Fin 3 → Fin 8 → ℝ) (p : Fin 8 → ℝ),
      (∀ i t, 0 ≤ c i t) ∧ (∀ t, 0 ≤ p t) ∧
      ∀ o : Outcome (Fin 8) 3, o.Valid p →
        ∃ i, (19/18 - eps) * MMS 3 (c i) p < cost (c i) o i :=
  nineteen_eighteenths_gap_chores (by linarith)
end FairChores.NineteenEighteenths
