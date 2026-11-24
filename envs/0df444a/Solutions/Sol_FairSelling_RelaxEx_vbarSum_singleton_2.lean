-- Prove2me | solution 2 for FairSelling.RelaxEx.vbarSum_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:32.496806+00:00
-- url     : https://prove2.me/submissions/e8dda70b-29e8-4ecc-9659-02f784ef4ff0

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx
namespace FairSelling.RelaxEx
theorem _root_.solution (i : Fin 2) : vbarSum (v i) p {0} = 1 := by
  fin_cases i <;> simp [vbarSum, vbar, p, v]
end FairSelling.RelaxEx
