-- Prove2me | solution 1 for Eden.commonIndexLocalDimension_eq_target_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:13:35.828308+00:00
-- url     : https://prove2.me/submissions/4b9ed7ff-363b-4cc9-b9c9-db4186cc48cd

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
import Theorems.Thm_Eden_commonIndexLocalDimension_eq
import Theorems.Thm_Eden_exponentSum_four_eq_iff


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    commonIndexLocalDimension c p = 4 + 4 / c ↔ p ∈ torus := by
  rw [commonIndexLocalDimension_eq hc, add_right_inj,
    div_left_inj' (show c ≠ 0 by linarith), exponentSum_four_eq_iff hc hp]
end Eden
