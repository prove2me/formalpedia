-- Prove2me | solution 1 for FairSelling.RelaxEx.p_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:32.022155+00:00
-- url     : https://prove2.me/submissions/f6263c6c-763a-413a-a8f9-d73b62370fbc

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx
namespace FairSelling.RelaxEx
theorem _root_.solution : ∀ g, 0 ≤ p g := by
  intro g; fin_cases g <;> norm_num [p]
end FairSelling.RelaxEx
