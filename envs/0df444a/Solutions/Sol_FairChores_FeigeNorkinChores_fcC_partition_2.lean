-- Prove2me | solution 2 for FairChores.FeigeNorkinChores.fcC_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:49.838911+00:00
-- url     : https://prove2.me/submissions/c326accd-2ccf-4d05-a4b1-af4cbabe888c

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
namespace FairChores.FeigeNorkinChores
theorem _root_.solution :
    (∑ j ∈ ({2, 5} : Finset (Fin 8)), fcC j) = 360 ∧
    (∑ j ∈ ({0, 3, 6} : Finset (Fin 8)), fcC j) = 360 ∧
    (∑ j ∈ ({1, 4, 7} : Finset (Fin 8)), fcC j) = 360 := by
  refine ⟨by decide, by decide, by decide⟩
end FairChores.FeigeNorkinChores
