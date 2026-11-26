-- Prove2me | solution 1 for FixedNumerator.QuarticData.neg_one_zpow_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:25.780907+00:00
-- url     : https://prove2.me/submissions/d3a40d8f-e235-4f35-9f15-f95fdcce9db5

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (m : ℤ) : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num
end FixedNumerator.QuarticData
