-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_factorial_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/999f6b34-034b-426d-8767-ef0451553f36

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_forcesMonochromaticTriangle_zero
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_succ_le

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (k : ℕ) :
    triangleRamseyNumber k ≤ 4 * k.factorial := by
  have hzero : triangleRamseyNumber 0 ≤ 2 := by
    apply Nat.sInf_le
    exact forcesMonochromaticTriangle_zero
  have hone : triangleRamseyNumber 1 + 1 ≤ 4 := by
    have hrec := triangleRamseyNumber_succ_le 0
    norm_num at hrec ⊢
    omega
  have hstrict : ∀ k : ℕ, 1 ≤ k →
      triangleRamseyNumber k + 1 ≤ 4 * k.factorial := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hzeroj : j = 0
        · subst j
          exact hone
        · have hjpos : 1 ≤ j := by omega
          have hprev := ih hjpos
          have hrec := triangleRamseyNumber_succ_le j
          rw [Nat.factorial_succ]
          nlinarith
  by_cases hk : k = 0
  · subst k
    norm_num
    omega
  · have hbound := hstrict k (by omega)
    omega
end ErdosProblems.MulticolourTriangleRamsey
