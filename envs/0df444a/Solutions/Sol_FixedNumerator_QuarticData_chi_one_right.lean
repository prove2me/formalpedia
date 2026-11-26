-- Prove2me | solution 1 for FixedNumerator.QuarticData.chi_one_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:28.76241+00:00
-- url     : https://prove2.me/submissions/90a2e92a-dcfd-495c-8915-10be3fd6334c

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local
public import Theorems.Thm_FixedNumerator_isPrimary_one


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (a : GaussianInt) : D.χ a 1 = 1 := by
  have h4 := D.chi_pow_four a 1 isCoprime_one_right
  have hm : D.χ a 1 = D.χ a 1 * D.χ a 1 := by
    have := D.chi_mul_right a 1 1 isPrimary_one isPrimary_one; rwa [mul_one] at this
  have h0 : D.χ a 1 ≠ 0 := by rintro h; rw [h] at h4; norm_num at h4
  exact mul_left_cancel₀ h0 (show D.χ a 1 * D.χ a 1 = D.χ a 1 * 1 by rw [mul_one]; exact hm.symm)
end FixedNumerator.QuarticData
