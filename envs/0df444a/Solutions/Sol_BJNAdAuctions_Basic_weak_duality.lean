-- Prove2me | solution 1 for BJNAdAuctions.Basic.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:03:55.100973+00:00
-- url     : https://prove2.me/submissions/4ee09d1f-6e89-4ae9-9a80-1e8166eafee6

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance

set_option autoImplicit false

open BJNAdAuctions.Basic in
theorem solution {I : Type*} [Fintype I] {m : ℕ} (inst : Instance I m)
    (y : I → Fin m → ℝ) (hy : PackingFeasible inst y)
    (x : I → ℝ) (z : Fin m → ℝ) (hxz : CoveringFeasible inst x z) :
    packingValue inst y ≤ coveringValue inst x z := by
  obtain ⟨hy0, hy1, hyB⟩ := hy
  obtain ⟨hc, hx0, hz0⟩ := hxz
  unfold packingValue coveringValue
  calc ∑ j, ∑ i, inst.b i j * y i j
      ≤ ∑ j, ∑ i, (inst.b i j * x i + z j) * y i j := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_right (hc i j) (hy0 i j)
    _ = ∑ i, x i * ∑ j, inst.b i j * y i j + ∑ j, z j * ∑ i, y i j := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          ring
    _ ≤ ∑ i, inst.B i * x i + ∑ j, z j := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro i _
          rw [mul_comm (inst.B i)]
          exact mul_le_mul_of_nonneg_left (hyB i) (hx0 i)
        · apply Finset.sum_le_sum; intro j _
          calc z j * ∑ i, y i j ≤ z j * 1 := mul_le_mul_of_nonneg_left (hy1 j) (hz0 j)
            _ = z j := mul_one _
