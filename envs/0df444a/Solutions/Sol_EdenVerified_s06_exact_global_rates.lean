-- Prove2me | solution 1 for EdenVerified.s06_exact_global_rates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:49.785824+00:00
-- url     : https://prove2.me/submissions/a078f60d-b7ce-40b8-b2b2-332c1f96dcb9

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_globalGrowthRate_five
import Theorems.Thm_Eden_globalGrowthRate_five_neg
import Theorems.Thm_Eden_globalGrowthRate_four
import Theorems.Thm_Eden_globalGrowthRate_nonneg
import Theorems.Thm_Eden_globalGrowthRate_zero
import Theorems.Thm_Eden_globalLogGrowth_five
import Theorems.Thm_Eden_globalLogGrowth_four


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    (∀ t : ℝ, 0 ≤ t → globalLogGrowth c 4 t = 4*t ∧
      globalLogGrowth c 5 t = (4-c)*t) ∧
    globalGrowthRate c 0 = 0 ∧
    (∀ k : ℕ, k ≤ 4 → 0 ≤ globalGrowthRate c k) ∧
    globalGrowthRate c 4 = 4 ∧ globalGrowthRate c 5 = 4-c ∧ globalGrowthRate c 5 < 0 :=
  ⟨fun t ht => ⟨globalLogGrowth_four hc.le ht, globalLogGrowth_five hc.le ht⟩,
    globalGrowthRate_zero hc.le, fun k hk => globalGrowthRate_nonneg hk hc.le,
    globalGrowthRate_four hc.le, globalGrowthRate_five hc.le, globalGrowthRate_five_neg hc⟩
end EdenVerified
