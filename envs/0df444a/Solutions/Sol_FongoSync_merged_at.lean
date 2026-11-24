-- Prove2me | solution 1 for FongoSync.merged_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:14.383664+00:00
-- url     : https://prove2.me/submissions/b2c9db82-d6ec-44f6-aea3-eb0c939903a6

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_foldl_state_apply

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
namespace FongoSync
theorem _root_.solution (σ : String → String → Strategy) (cs : List (Change V)) (k : Key) :
    merged σ cs k = (entriesAt cs k).foldl (apply (strategyAt σ k)) none :=
  foldl_state_apply σ cs State.empty k
end FongoSync
