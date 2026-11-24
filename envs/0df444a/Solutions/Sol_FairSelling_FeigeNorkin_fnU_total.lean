-- Prove2me | solution 1 for FairSelling.FeigeNorkin.fnU_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:01.969646+00:00
-- url     : https://prove2.me/submissions/e36e69bf-d1a8-4cb9-ad40-325bd34ccf1a

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
namespace FairSelling.FeigeNorkin
theorem _root_.solution : (∑ j, fnU j) = 108 := by decide
end FairSelling.FeigeNorkin
