-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.two_fcU_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:45.701085+00:00
-- url     : https://prove2.me/submissions/0abe1a1c-a9dd-4cba-9a1e-018409add96a

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
namespace FairChores.FeigeNorkinChores
theorem _root_.solution : ∀ j : Fin 8, fcR j ≤ 2 * fcU j ∧ fcC j ≤ 2 * fcU j := by decide
end FairChores.FeigeNorkinChores
