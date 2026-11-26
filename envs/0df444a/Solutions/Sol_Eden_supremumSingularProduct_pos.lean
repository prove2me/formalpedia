-- Prove2me | solution 1 for Eden.supremumSingularProduct_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:37.9188+00:00
-- url     : https://prove2.me/submissions/fee6c67d-51f3-4591-ac88-56d78146ec78

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_supremumSingularProduct_bounds

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : 0 < supremumSingularProduct c k t :=
  (Real.exp_pos _).trans_le (supremumSingularProduct_bounds hk hc ht).1
end Eden
