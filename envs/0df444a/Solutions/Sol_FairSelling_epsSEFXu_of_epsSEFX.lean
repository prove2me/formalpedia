-- Prove2me | solution 1 for FairSelling.epsSEFXu_of_epsSEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:03.140933+00:00
-- url     : https://prove2.me/submissions/144bd384-f6a0-4ba4-a69c-28631f022783

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Theorems.Thm_FairSelling_vbarSum_erase
import Theorems.Thm_FairSelling_p_le_vbar

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution {eps : ℝ} (heps : 0 ≤ eps) (hvalid : o.Valid p)
    (ho : epsSEFX v p eps o) : epsSEFXu v p eps o := by
  intro i j
  refine ⟨fun hj => by have := (ho i j).1 hj; linarith, fun g hg => ?_⟩
  have hsplit := vbarSum_erase (vi := v i) (p := p) hg
  have hpg : p g ≤ vbar (v i) p g := p_le_vbar g
  rcases lt_or_eq_of_le (hvalid.2.2.1 j) with hj | hj
  · have hEF := (ho i j).1 hj
    linarith
  · have hj0 : o.money j = 0 := hj.symm
    rw [hj0]
    rcases (ho i j).2 hj0 with hEF | hall
    · linarith
    · have := hall g hg
      linarith
end FairSelling
