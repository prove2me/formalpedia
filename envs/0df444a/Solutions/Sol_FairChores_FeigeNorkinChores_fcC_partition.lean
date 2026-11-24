-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.fcC_partition
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:35:33.458476+00:00
-- url     : https://prove2.me/submissions/33bb9105-f99c-492c-aa9e-43b0f6a02138

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores


theorem solution :
    (∑ j ∈ ({2, 5} : Finset (Fin 8)), fcC j) = 360 ∧
    (∑ j ∈ ({0, 3, 6} : Finset (Fin 8)), fcC j) = 360 ∧
    (∑ j ∈ ({1, 4, 7} : Finset (Fin 8)), fcC j) = 360 := by
  decide +kernel
