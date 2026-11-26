-- Prove2me | solution 1 for FixedOrderFactor.sum_rootOfUnity_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:01.482807+00:00
-- url     : https://prove2.me/submissions/ceef86d2-6d69-43ef-8d74-e9ae3e936539

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
public import Theorems.Thm_FixedOrderFactor_rootOfUnity_eq

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) (m : ℕ) (hm : m < r) :
    ∑ j ∈ range r, rootOfUnity r j ^ m = if m = 0 then (r : ℂ) else 0 := by
  have hp := Complex.isPrimitiveRoot_exp r hr.ne'
  set ω := Complex.exp (2 * π * I / r)
  simp_rw [rootOfUnity_eq, ← pow_mul, mul_comm _ m, pow_mul]
  split_ifs with h
  · subst h; simp
  · have hne : ω ^ m ≠ 1 := hp.pow_ne_one_of_pos_of_lt h hm
    rw [geom_sum_eq hne, ← pow_mul, mul_comm m r, pow_mul, hp.pow_eq_one, one_pow, sub_self,
      zero_div]
end FixedOrderFactor
