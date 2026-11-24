-- Prove2me | solution 1 for FairChores.NineteenEighteenths.cast_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:48:22.908742+00:00
-- url     : https://prove2.me/submissions/de01995c-b39b-4ebd-80cc-d11088ea0ad6

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
namespace FairChores.NineteenEighteenths
theorem _root_.solution (s : Finset (Fin 8)) (w : Fin 8 → ℕ) (m : ℕ) (h : ∑ t ∈ s, w t = m) :
    ∑ t ∈ s, (w t : ℝ) = m := by
  rw [← Nat.cast_sum, h]
end FairChores.NineteenEighteenths
