-- Prove2me | solution 1 for FixedNumerator.QuarticData.chi_pow_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:36.972885+00:00
-- url     : https://prove2.me/submissions/dfeb19bd-907e-438c-b41d-5dc9c0eb50e2

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local
public import Theorems.Thm_FixedNumerator_QuarticData_chi_one_left

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (a c : GaussianInt) (n : ℕ) : D.χ (a ^ n) c = D.χ a c ^ n := by
  induction n with
  | zero => simpa using D.chi_one_left c
  | succ n ih => rw [pow_succ, D.chi_mul_left, ih, pow_succ]
end FixedNumerator.QuarticData
