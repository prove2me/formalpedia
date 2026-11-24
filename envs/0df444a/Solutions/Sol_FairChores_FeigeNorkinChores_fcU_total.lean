-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.fcU_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:27:50.493904+00:00
-- url     : https://prove2.me/submissions/83c7bc41-950e-4fae-a462-301018a8d4f2

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
namespace FairChores.FeigeNorkinChores
theorem _root_.solution : (∑ j, fcU j) = 1080 := by decide
end FairChores.FeigeNorkinChores
