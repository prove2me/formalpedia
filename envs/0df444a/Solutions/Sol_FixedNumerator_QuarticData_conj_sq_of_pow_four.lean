-- Prove2me | solution 1 for FixedNumerator.QuarticData.conj_sq_of_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:24.910535+00:00
-- url     : https://prove2.me/submissions/838b01cf-428f-43c7-8eba-36e78994a830

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
theorem _root_.solution {x : ℂ} (hx : x ^ 4 = 1) : starRingEnd ℂ (x ^ 2) = x ^ 2 := by
  have hn : ‖x‖ = 1 := by
    have h := congrArg norm hx
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) (by norm_num)).mp h
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hn
  have hc : starRingEnd ℂ x = x⁻¹ := (Complex.inv_eq_conj hn).symm
  rw [map_pow, hc, inv_pow]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hx)
end FixedNumerator.QuarticData
