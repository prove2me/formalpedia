-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_stage_palette_packing_binomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/e6ffee58-5823-4b17-bb45-eb0bdb7501d2

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_separated_palette_packing
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_stage_palette_numerator_bound
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_palette_binomial_sum_le

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (j t s : ℕ)
    (hs : 0 < s) (hj : 0 < j) (hhalf : 2 * s ≤ t) :
    ∃ family : Finset (Finset (Fin (j * t))),
      family ⊆ (Finset.univ : Finset (Fin (j * t))).powersetCard t ∧
      IsPaletteSeparated s family ∧
      j ^ t ≤ family.card *
        (s * t.choose s * (j * t).choose s) := by
  obtain ⟨family, hfamily, hseparated, hpacking⟩ :=
    exists_separated_palette_packing (j * t) t s hs
  refine ⟨family, hfamily, hseparated,
    (stage_palette_numerator_bound j t).trans (hpacking.trans ?_)⟩
  exact Nat.mul_le_mul_left _
    (palette_binomial_sum_le (j * t) t s hhalf
      (Nat.le_mul_of_pos_left t hj))
end ErdosProblems.MulticolourTriangleRamsey
