-- Prove2me | solution 1 for FairSelling.p_le_vbar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:59.239408+00:00
-- url     : https://prove2.me/submissions/be80d3ee-3bf2-49ee-b22f-99b227189acb

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution {vi p : G → ℝ} (g : G) : p g ≤ vbar vi p g := le_max_left _ _
end FairSelling
