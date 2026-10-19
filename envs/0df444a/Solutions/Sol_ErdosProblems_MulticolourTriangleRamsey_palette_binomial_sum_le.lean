-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.palette_binomial_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/ed79df07-967e-46e7-822a-a9a90d30a352

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_choose_le_choose_of_le_half

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (N t s : ℕ)
    (hhalf : 2 * s ≤ t) (htN : t ≤ N) :
    (∑ d ∈ Finset.range s,
      t.choose d * (N - t).choose d) ≤
        s * t.choose s * N.choose s := by
  have hNhalf : 2 * s ≤ N := hhalf.trans htN
  calc
    (∑ d ∈ Finset.range s,
      t.choose d * (N - t).choose d) ≤
        ∑ _d ∈ Finset.range s, t.choose s * N.choose s := by
      apply Finset.sum_le_sum
      intro d hd
      have hds : d ≤ s := by
        have := Finset.mem_range.mp hd
        omega
      apply Nat.mul_le_mul
      · exact choose_le_choose_of_le_half hds hhalf
      · exact (Nat.choose_le_choose d (Nat.sub_le N t)).trans
          (choose_le_choose_of_le_half hds hNhalf)
    _ = s * t.choose s * N.choose s := by simp [mul_assoc]
end ErdosProblems.MulticolourTriangleRamsey
