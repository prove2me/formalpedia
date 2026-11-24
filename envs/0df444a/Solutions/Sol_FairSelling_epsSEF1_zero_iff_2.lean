-- Prove2me | solution 2 for FairSelling.epsSEF1_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:51.543317+00:00
-- url     : https://prove2.me/submissions/b9db85ba-2501-436d-974c-dd8f927a5033

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution : epsSEF1 v p 0 o ↔ SEF1 v p o := by
  unfold epsSEF1 SEF1
  simp
end FairSelling
