-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.fcC_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:05.935096+00:00
-- url     : https://prove2.me/submissions/e127bd54-b15c-4861-b5b3-5f20ab0dac1a

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
namespace FairChores.FeigeNorkinChores
theorem _root_.solution : (∑ j, fcC j) = 1080 := by decide
end FairChores.FeigeNorkinChores
