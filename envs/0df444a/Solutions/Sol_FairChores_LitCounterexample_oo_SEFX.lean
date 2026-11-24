-- Prove2me | solution 1 for FairChores.LitCounterexample.oo_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:53:43.635911+00:00
-- url     : https://prove2.me/submissions/9ed0dcb6-031f-4795-b6fc-91d900dd0cfc

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_SEFX_of_EF
import Theorems.Thm_FairChores_LitCounterexample_oo_EF

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample
namespace FairChores.LitCounterexample
theorem _root_.solution : SEFX cc pp oo := SEFX_of_EF oo_EF
end FairChores.LitCounterexample
