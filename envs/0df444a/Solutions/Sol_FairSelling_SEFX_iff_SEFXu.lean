-- Prove2me | solution 1 for FairSelling.SEFX_iff_SEFXu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:00.258702+00:00
-- url     : https://prove2.me/submissions/0bd7ea61-bb87-442e-9f0b-77b35ecb1fec

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Theorems.Thm_FairSelling_SEFXu_of_SEFX
import Theorems.Thm_FairSelling_SEFX_of_SEFXu

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution (hvalid : o.Valid p) : SEFX v p o ↔ SEFXu v p o :=
  ⟨SEFXu_of_SEFX hvalid, SEFX_of_SEFXu⟩
end FairSelling
