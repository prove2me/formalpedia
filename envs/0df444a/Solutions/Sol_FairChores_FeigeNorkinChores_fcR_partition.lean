-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.fcR_partition
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:35:22.326123+00:00
-- url     : https://prove2.me/submissions/6ac56ac1-9042-4bcb-8e48-fd439f268dd8

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores


theorem solution :
    (∑ j ∈ ({2, 3, 4} : Finset (Fin 8)), fcR j) = 360 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 8)), fcR j) = 360 ∧
    (∑ j ∈ ({5, 6, 7} : Finset (Fin 8)), fcR j) = 360 := by
  decide +kernel
