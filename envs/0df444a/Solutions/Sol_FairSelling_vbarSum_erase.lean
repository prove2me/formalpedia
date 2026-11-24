-- Prove2me | solution 1 for FairSelling.vbarSum_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:58.358802+00:00
-- url     : https://prove2.me/submissions/a662cee7-3855-4063-92b7-d032ff4a2cd5

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Theorems.Thm_FairSelling_vbarSum_sdiff_singleton


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution {vi p : G → ℝ} {A : Finset G} {g : G} (hg : g ∈ A) :
    vbarSum vi p A = vbarSum vi p (A \ {g}) + vbar vi p g :=
  vbarSum_sdiff_singleton hg
end FairSelling
