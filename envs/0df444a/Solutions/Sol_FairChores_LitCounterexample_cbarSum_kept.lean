-- Prove2me | solution 1 for FairChores.LitCounterexample.cbarSum_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:39.103025+00:00
-- url     : https://prove2.me/submissions/4332547c-2621-4327-b675-cc24469c52f0

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_LitCounterexample_cbarSum_single

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample
namespace FairChores.LitCounterexample
theorem _root_.solution (i j : Fin 2) : cbarSum (cc i) pp (oo.kept j) = 1 :=
  cbarSum_single i j
end FairChores.LitCounterexample
