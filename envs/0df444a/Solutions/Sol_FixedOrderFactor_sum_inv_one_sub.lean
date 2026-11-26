-- Prove2me | solution 1 for FixedOrderFactor.sum_inv_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:21.02219+00:00
-- url     : https://prove2.me/submissions/c533f9b8-47fe-4b00-9dce-e45ed325c043

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
public import Theorems.Thm_FixedOrderFactor_rootOfUnity_pow_r
public import Theorems.Thm_FixedOrderFactor_sum_rootOfUnity_pow
public import Theorems.Thm_FixedOrderFactor_one_sub_mul_ne_zero

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) {x : ℂ} (hx : x ^ r ≠ 1) :
    ∑ j ∈ range r, 1 / (1 - rootOfUnity r j * x) = r / (1 - x ^ r) := by
  have hxr : 1 - x ^ r ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hterm : ∀ j ∈ range r, 1 / (1 - rootOfUnity r j * x) =
      (∑ m ∈ range r, rootOfUnity r j ^ m * x ^ m) / (1 - x ^ r) := by
    intro j _
    have hne := one_sub_mul_ne_zero hr j hx
    have ha : rootOfUnity r j * x ≠ 1 := fun h => hne (by rw [h, sub_self])
    simp_rw [← mul_pow]
    rw [geom_sum_eq ha, mul_pow, rootOfUnity_pow_r hr, one_mul]
    have : rootOfUnity r j * x - 1 ≠ 0 := sub_ne_zero.mpr ha
    field_simp
    ring
  rw [sum_congr rfl hterm, ← sum_div, sum_comm]
  simp_rw [← sum_mul]
  rw [sum_congr rfl (fun m hm => by rw [sum_rootOfUnity_pow hr m (mem_range.mp hm)])]
  rw [sum_eq_single 0]
  · simp
  · intro m _ hm; simp [hm]
  · intro h; exact absurd (mem_range.mpr hr) h
end FixedOrderFactor
