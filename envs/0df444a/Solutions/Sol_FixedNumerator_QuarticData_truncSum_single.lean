-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:43.223444+00:00
-- url     : https://prove2.me/submissions/1a57876e-4391-468b-bdb2-6cdec3768880

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_congr_class
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_num_pow_four
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_two_term
public import Theorems.Thm_FixedNumerator_C_sign_even_pow
public import Theorems.Thm_FixedNumerator_IsPrimary_mul
public import Theorems.Thm_FixedNumerator_IsPrimary_pow
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
    {e : ℕ} (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X = truncSum D W (π ^ e * μ') β (π * γ) X +
      D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1) *
        truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (e + 1)) := by
  have hsupp : ∀ k, k ≠ 0 → k ≠ e + 1 → D.g (π ^ e * μ') (π ^ k) = 0 := by
    intro k hk0 hke
    by_contra hne
    rcases D.g_prime_pow π μ' e k hπ hπp hμ' hne with h | h | ⟨h4, hle⟩
    · exact hk0 h
    · exact hke h
    · rcases he with rfl | rfl <;> omega
  have hev : Even (e + 1) := by rcases he with rfl | rfl <;> decide
  rw [D.truncSum_two_term W hW1 hW _ β hπ hπp hπγ hβ (by omega) hsupp X,
    C_sign_even_pow hπp _ hev, one_mul]
  have h2 : 2 * (e + 1) = 4 * ((e + 1) / 2) := by rcases he with rfl | rfl <;> rfl
  rw [h2, D.truncSum_num_pow_four W _ ((hπp.pow _).mul hβ),
    D.truncSum_congr_class W _ _ (show (4 : GaussianInt) ∣ π ^ (e + 1) * β - β from ?_)]
  obtain ⟨j, hj⟩ := hev
  have : π ^ (e + 1) * β - β = (π ^ (2 * j) - 1) * β := by rw [hj, two_mul]; ring
  rw [this]; exact dvd_mul_of_dvd_left (pow_two_mul_sub_one hπp j) _
end FixedNumerator.QuarticData
