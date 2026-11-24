-- Prove2me | solution 1 for FairChores.NineteenEighteenths.instP_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:46.211691+00:00
-- url     : https://prove2.me/submissions/08889859-5643-4405-ac4e-f26b8aa59efe

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
theorem _root_.solution {lam : ℝ} (hlam : 0 ≤ lam) : ∀ t, 0 ≤ instP lam t :=
  fun t => mul_nonneg hlam (by positivity)
end FairChores.NineteenEighteenths
