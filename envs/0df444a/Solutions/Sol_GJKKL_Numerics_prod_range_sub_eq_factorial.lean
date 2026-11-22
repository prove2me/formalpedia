-- Prove2me | solution 1 for GJKKL.Numerics.prod_range_sub_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:45.143359+00:00
-- url     : https://prove2.me/submissions/7ed9fac2-ed54-4553-8e03-43e1fb7db8b5

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real
namespace GJKKL.Numerics
theorem _root_.solution (m : ℕ) :
    ∏ i ∈ range m, ((m : ℝ) - i) = m.factorial := by
  rw [← prod_range_reflect, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  refine prod_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring
end GJKKL.Numerics
