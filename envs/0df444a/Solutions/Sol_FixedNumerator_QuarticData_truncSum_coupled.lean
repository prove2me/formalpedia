-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_coupled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:04.342902+00:00
-- url     : https://prove2.me/submissions/da21ad71-63aa-4e98-b9cd-e137ee5419be

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_congr_class
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_num_pow_four
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_two_term
public import Theorems.Thm_FixedNumerator_C_sign_congr
public import Theorems.Thm_FixedNumerator_IsPrimary_mul
public import Theorems.Thm_FixedNumerator_pow_two_mul_sub_one


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (X : ℕ) :
    truncSum D W μ' β γ X = truncSum D W μ' β (π * γ) X +
        (-1 : ℂ) ^ C (π * β) π * D.g μ' π * W π *
          truncSum D W (π ^ 2 * μ') (π * β) (π * γ) (X / π.norm.toNat) ∧
      truncSum D W (π ^ 2 * μ') (π * β) γ X = truncSum D W (π ^ 2 * μ') (π * β) (π * γ) X +
        (-1 : ℂ) ^ C β (π ^ 3) * D.g (π ^ 2 * μ') (π ^ 3) * W π ^ 3 *
          truncSum D W μ' β (π * γ) (X / π.norm.toNat ^ 3) := by
  have hsupp0 : ∀ k, k ≠ 0 → k ≠ 1 → D.g μ' (π ^ k) = 0 := by
    intro k hk0 hk1
    by_contra hne
    have := D.g_prime_pow π μ' 0 k hπ hπp hμ' (by simpa using hne)
    omega
  have hsupp2 : ∀ k, k ≠ 0 → k ≠ 3 → D.g (π ^ 2 * μ') (π ^ k) = 0 := by
    intro k hk0 hk3
    by_contra hne
    have := D.g_prime_pow π μ' 2 k hπ hπp hμ' hne
    omega
  have hπβ : IsPrimary (π * β) := hπp.mul hβ
  constructor
  · rw [D.truncSum_two_term W hW1 hW μ' β hπ hπp hπγ hβ one_ne_zero hsupp0 X]
    simp only [pow_one]
    congr 2
    rw [show μ' * π ^ (2 * 1) = π ^ 2 * μ' by ring]
  · rw [D.truncSum_two_term W hW1 hW (π ^ 2 * μ') (π * β) hπ hπp hπγ hπβ (by norm_num) hsupp2 X]
    have hcl : (4 : GaussianInt) ∣ π ^ 3 * (π * β) - β := by
      have : π ^ 3 * (π * β) - β = (π ^ (2 * 2) - 1) * β := by ring
      rw [this]; exact dvd_mul_of_dvd_left (pow_two_mul_sub_one hπp 2) _
    rw [C_sign_congr hβ hcl, D.truncSum_congr_class W _ _ hcl,
      show π ^ 2 * μ' * π ^ (2 * 3) = μ' * π ^ (4 * 2) by ring,
      D.truncSum_num_pow_four W μ' hβ]
end FixedNumerator.QuarticData
