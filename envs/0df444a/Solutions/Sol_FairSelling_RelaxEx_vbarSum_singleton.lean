-- Prove2me | solution 1 for FairSelling.RelaxEx.vbarSum_singleton
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:23:20.894866+00:00
-- url     : https://prove2.me/submissions/cc7a86f7-74ab-4e65-b712-d73b89db7d30

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx


theorem solution (i : Fin 2) : vbarSum (v i) p {0} = 1 := by
  fin_cases i <;> norm_num [vbarSum,vbar,v,p]
