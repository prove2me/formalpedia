-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.fcR_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:05.30483+00:00
-- url     : https://prove2.me/submissions/d0ab379b-56c5-4662-b261-b622b44635ec

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
namespace FairChores.FeigeNorkinChores
theorem _root_.solution : (∑ j, fcR j) = 1080 := by decide
end FairChores.FeigeNorkinChores
