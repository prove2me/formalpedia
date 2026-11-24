-- Prove2me | solution 1 for FairSelling.lemmaFourCashSold_holds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:09:00.262621+00:00
-- url     : https://prove2.me/submissions/79e1e1de-a2fd-4eb9-a887-539acc154cad

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
import Theorems.Thm_FairSelling_lemmaFour_singleton

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution : LemmaFourCashSold G := by
  intro w p hw hp hnobig K f m hfK hm0 hmf hKcard hprice hrej
  exact lemmaFour_singleton w p hw hp hnobig K f m hfK hm0 hmf hKcard hprice hrej
end FairSelling
