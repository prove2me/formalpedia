-- Prove2me | solution 1 for FairSelling.FeigeNorkin.fnR_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:58.542805+00:00
-- url     : https://prove2.me/submissions/e7f68873-e9d4-43ec-a399-0a60de8f564c

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
namespace FairSelling.FeigeNorkin
theorem _root_.solution : (∑ j, fnR j) = 108 := by decide
end FairSelling.FeigeNorkin
