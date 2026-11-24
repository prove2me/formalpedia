-- Prove2me | solution 2 for FairSelling.epsSEFXlit_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:38:10.747339+00:00
-- url     : https://prove2.me/submissions/fa5f756c-32fc-4512-848d-63d5e64f8312

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution : epsSEFXlit v p 0 o ↔ SEFXlit v p o := by
  unfold epsSEFXlit SEFXlit
  simp
end FairSelling
