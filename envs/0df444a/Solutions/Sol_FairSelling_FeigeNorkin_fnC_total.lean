-- Prove2me | solution 1 for FairSelling.FeigeNorkin.fnC_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:02.5423+00:00
-- url     : https://prove2.me/submissions/ec1b4f48-467c-483a-8f44-ed0d134a0d82

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
namespace FairSelling.FeigeNorkin
theorem _root_.solution : (∑ j, fnC j) = 108 := by decide
end FairSelling.FeigeNorkin
