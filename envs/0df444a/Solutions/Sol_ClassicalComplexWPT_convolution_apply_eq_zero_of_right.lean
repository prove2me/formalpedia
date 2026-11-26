-- Prove2me | solution 1 for ClassicalComplexWPT.convolution_apply_eq_zero_of_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:10.10786+00:00
-- url     : https://prove2.me/submissions/2ecadccb-2047-4d91-bbba-0c34cba0e919

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {q p : OriginSeq} {n : ℕ}
    (hp : ∀ k ≤ n, p k = 0) : convolution q p n = 0 := by
  rw [convolution_apply]
  apply Finset.sum_eq_zero
  intro ij hij
  have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [hp ij.2 (by omega), mul_zero]
end ClassicalComplexWPT
