-- Prove2me | solution 1 for FairSelling.SEFXu_of_SEFXs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:19.488172+00:00
-- url     : https://prove2.me/submissions/5efa3453-f067-4c17-b17a-d923c9623610

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Theorems.Thm_FairSelling_SEFXu_of_SEFX
import Theorems.Thm_FairSelling_SEFX_of_SEFXs

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution (hvalid : o.Valid p) (ho : SEFXs v p o) : SEFXu v p o :=
  SEFXu_of_SEFX hvalid (SEFX_of_SEFXs hvalid ho)
end FairSelling
