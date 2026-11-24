-- Prove2me | solution 1 for FairSelling.Examples.PS_example
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:23:35.70984+00:00
-- url     : https://prove2.me/submissions/5c502594-00d5-428c-8c0a-4a6530f962e8

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples


theorem solution : PS 2 vex pex = 2 := by
  norm_num [PS, vex,pex, Fin.sum_univ_two]
