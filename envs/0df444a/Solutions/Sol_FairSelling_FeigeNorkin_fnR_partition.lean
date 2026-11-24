-- Prove2me | solution 1 for FairSelling.FeigeNorkin.fnR_partition
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:27:54.499796+00:00
-- url     : https://prove2.me/submissions/19c30c74-b299-4efb-bef3-d6097b1f31a6

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin


theorem solution :
    (∑ j ∈ ({2, 3, 4} : Finset (Fin 8)), fnR j) = 36 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 8)), fnR j) = 36 ∧
    (∑ j ∈ ({5, 6, 7} : Finset (Fin 8)), fnR j) = 36 := by
  decide +kernel
