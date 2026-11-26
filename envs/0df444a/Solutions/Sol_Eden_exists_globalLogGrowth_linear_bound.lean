-- Prove2me | solution 1 for Eden.exists_globalLogGrowth_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:22.380321+00:00
-- url     : https://prove2.me/submissions/6e527e69-820f-49f9-a5c8-c4927218aed4

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_abs_globalLogGrowth_le

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |globalLogGrowth c k t| ≤ C * t := by
  exact ⟨(k : ℝ) * c, mul_nonneg (Nat.cast_nonneg _) (by linarith),
    fun t ht => abs_globalLogGrowth_le hk hc ht⟩
end Eden
