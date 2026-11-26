-- Prove2me | solution 1 for FixedNumerator.QuarticData.chi_one_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:27.823063+00:00
-- url     : https://prove2.me/submissions/81d139cf-5a1b-4abc-8b25-3ca82c16a9ac

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
theorem _root_.solution (c : GaussianInt) : D.χ 1 c = 1 := by
  have h4 := D.chi_pow_four 1 c isCoprime_one_left
  have hm : D.χ 1 c = D.χ 1 c * D.χ 1 c := by
    have := D.chi_mul_left 1 1 c; rwa [mul_one] at this
  have h0 : D.χ 1 c ≠ 0 := by rintro h; rw [h] at h4; norm_num at h4
  exact mul_left_cancel₀ h0 (show D.χ 1 c * D.χ 1 c = D.χ 1 c * 1 by rw [mul_one]; exact hm.symm)
end FixedNumerator.QuarticData
