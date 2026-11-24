-- Prove2me | solution 2 for FairChores.FeigeNorkinChores.fcR_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:30.75723+00:00
-- url     : https://prove2.me/submissions/d7650a4e-8269-440f-912c-c34218afa89b

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
namespace FairChores.FeigeNorkinChores
theorem _root_.solution :
    (∑ j ∈ ({2, 3, 4} : Finset (Fin 8)), fcR j) = 360 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 8)), fcR j) = 360 ∧
    (∑ j ∈ ({5, 6, 7} : Finset (Fin 8)), fcR j) = 360 := by
  refine ⟨by decide, by decide, by decide⟩
end FairChores.FeigeNorkinChores
