-- Prove2me | solution 1 for Eden.supremumSingularProduct_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:42.818948+00:00
-- url     : https://prove2.me/submissions/f0569177-f662-46f0-bc6a-3539c08ff25e

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_integerGrowthValues_nonempty
import Theorems.Thm_Eden_supremumSingularProduct_pos
import Theorems.Thm_Eden_singularValueFunction_le_supremum
import Theorems.Thm_Eden_evolution_mem_attractor
import Theorems.Thm_Eden_singularValueFunction_evolution_add_le
import Theorems.Thm_Eden_singularValueFunction_integer_evolution_pos


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c s t : ℝ}
    (hc : 4 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    supremumSingularProduct c k (s + t) ≤ supremumSingularProduct c k s * supremumSingularProduct c k t := by
  apply csSup_le (integerGrowthValues_nonempty c k (s + t))
  rintro x ⟨p, hp, rfl⟩
  apply (singularValueFunction_evolution_add_le hk c hs ht p).trans
  calc
    _ ≤ supremumSingularProduct c k t * supremumSingularProduct c k s := by
      exact mul_le_mul
        (singularValueFunction_le_supremum hk hc ht (evolution_mem_attractor c hs hp))
        (singularValueFunction_le_supremum hk hc hs hp)
        (singularValueFunction_integer_evolution_pos hk c hs p).le
        (supremumSingularProduct_pos hk hc ht).le
    _ = _ := mul_comm _ _
end Eden
