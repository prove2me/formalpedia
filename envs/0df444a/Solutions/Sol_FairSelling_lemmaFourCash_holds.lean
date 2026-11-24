-- Prove2me | solution 1 for FairSelling.lemmaFourCash_holds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:47:44.850429+00:00
-- url     : https://prove2.me/submissions/8d6fb7bb-3a61-4b3e-b1dd-69be0a4126e9

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
import Theorems.Thm_FairSelling_lemmaFourCashSold_holds
import Theorems.Thm_FairSelling_lemmaFourCash_of_sold


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution : LemmaFourCash G := lemmaFourCash_of_sold lemmaFourCashSold_holds
end FairSelling
