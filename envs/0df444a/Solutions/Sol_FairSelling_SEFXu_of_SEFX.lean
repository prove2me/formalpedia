-- Prove2me | solution 1 for FairSelling.SEFXu_of_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:31.521122+00:00
-- url     : https://prove2.me/submissions/8c0d41e2-0734-432f-9234-6c2f775a9995

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
theorem _root_.solution (hvalid : o.Valid p) (ho : SEFX v p o) : SEFXu v p o := by
  intro i j
  refine ⟨(ho i j).1, fun g hg => ?_⟩
  have hsplit := vbarSum_erase (vi := v i) (p := p) hg
  have hpg : p g ≤ vbar (v i) p g := p_le_vbar g
  rcases lt_or_eq_of_le (hvalid.2.2.1 j) with hj | hj
  · -- `j` holds money: use the envy-free condition and drop the good `g`.
    have hEF := (ho i j).1 hj
    linarith
  · have hj0 : o.money j = 0 := hj.symm
    rw [hj0]
    rcases (ho i j).2 hj0 with hEF | hall
    · linarith
    · have := hall g hg
      linarith
end FairSelling
