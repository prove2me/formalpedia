-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_reduce_num
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:36.486796+00:00
-- url     : https://prove2.me/submissions/dd7340d8-64dd-47c4-9f6c-e77bfbcdbb4f

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_General
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_num_pow_four


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (W : GaussianInt → ℂ) {π γ : GaussianInt} (μ' β : GaussianInt)
    (hβ : IsPrimary β) (e X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X = truncSum D W (π ^ (e % 4) * μ') β (π * γ) X := by
  have h : π ^ e * μ' = π ^ (e % 4) * μ' * π ^ (4 * (e / 4)) := by
    rw [mul_right_comm, ← pow_add, Nat.mod_add_div]
  rw [h, D.truncSum_num_pow_four W _ hβ]
end FixedNumerator.QuarticData
