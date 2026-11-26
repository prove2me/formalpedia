-- Prove2me | solution 1 for EdenVerified.s04_global_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:30.957485+00:00
-- url     : https://prove2.me/submissions/698c90eb-d3ce-46b5-8a74-889707da6fd3

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_abs_globalLogGrowth_le
import Theorems.Thm_Eden_globalLogGrowth_subadditive
import Theorems.Thm_Eden_globalLogGrowth_zero
import Theorems.Thm_Eden_integerGrowthValues_bddAbove
import Theorems.Thm_Eden_integerGrowthValues_nonempty
import Theorems.Thm_Eden_supremumSingularProduct_pos


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (k : ℕ) (hk : k ≤ 5) :
    (∀ t : ℝ, 0 ≤ t → (integerGrowthValues c k t).Nonempty ∧
      BddAbove (integerGrowthValues c k t) ∧ 0 < supremumSingularProduct c k t) ∧
    globalLogGrowth c k 0 = 0 ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      globalLogGrowth c k (s+t) ≤ globalLogGrowth c k s + globalLogGrowth c k t) ∧
    0 ≤ (k : ℝ) * c ∧
    (∀ t : ℝ, 0 ≤ t → |globalLogGrowth c k t| ≤ ((k : ℝ) * c) * t) := by
  refine ⟨?_, globalLogGrowth_zero hk hc.le, ?_, ?_, ?_⟩
  · exact fun t ht => ⟨integerGrowthValues_nonempty c k t,
      integerGrowthValues_bddAbove hk hc.le ht, supremumSingularProduct_pos hk hc.le ht⟩
  · exact fun s t hs ht => globalLogGrowth_subadditive hk hc.le hs ht
  · positivity
  · exact fun t ht => abs_globalLogGrowth_le hk hc.le ht
end EdenVerified
