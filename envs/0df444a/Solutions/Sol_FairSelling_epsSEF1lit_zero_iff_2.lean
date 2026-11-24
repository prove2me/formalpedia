-- Prove2me | solution 2 for FairSelling.epsSEF1lit_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:38:01.264954+00:00
-- url     : https://prove2.me/submissions/f82e1117-c612-4a4b-ad68-b72169b39ec4

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution : epsSEF1lit v p 0 o ↔ SEF1lit v p o := by
  unfold epsSEF1lit SEF1lit
  simp
end FairSelling
