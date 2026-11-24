-- Prove2me | solution 1 for FairSelling.FeigeNorkin.fnC_partition
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:27:43.575584+00:00
-- url     : https://prove2.me/submissions/301f42f2-36e5-4c9d-9bb4-9d99e26c3f04

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin


theorem solution :
    (∑ j ∈ ({2, 5} : Finset (Fin 8)), fnC j) = 36 ∧
    (∑ j ∈ ({0, 3, 6} : Finset (Fin 8)), fnC j) = 36 ∧
    (∑ j ∈ ({1, 4, 7} : Finset (Fin 8)), fnC j) = 36 := by
  decide +kernel
