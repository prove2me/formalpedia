-- Prove2me | solution 1 for FixedNumerator.QuarticData.g_mul_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:02.22735+00:00
-- url     : https://prove2.me/submissions/95958f78-e040-4aaf-8e60-601bb25491bf

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local
public import Theorems.Thm_FixedNumerator_QuarticData_chi_pow_left

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (μ : GaussianInt) {π c : GaussianInt} (hc : IsPrimary c)
    (hcop : IsCoprime π c) (j : ℕ) : D.g (μ * π ^ (4 * j)) c = D.g μ c := by
  rw [mul_comm μ, D.g_twist _ _ _ hc hcop.pow_left, D.chi_pow_left, pow_mul,
    D.chi_pow_four π c hcop, one_pow, map_one, one_mul]
end FixedNumerator.QuarticData
