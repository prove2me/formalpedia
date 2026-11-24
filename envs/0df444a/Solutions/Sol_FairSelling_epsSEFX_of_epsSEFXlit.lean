-- Prove2me | solution 1 for FairSelling.epsSEFX_of_epsSEFXlit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:38:48.688266+00:00
-- url     : https://prove2.me/submissions/4cf35518-cc07-462e-9b9b-83362d7aae60

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution {eps : ℝ} (hvalid : o.Valid p) (ho : epsSEFXlit v p eps o) :
    epsSEFX v p eps o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => Or.inr fun g hg => ?_⟩
  have := (ho i j).2 hj g hg
  have hmi := hvalid.2.2.1 i
  linarith
end FairSelling
