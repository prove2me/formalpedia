-- Prove2me | solution 1 for FixedNumerator.QuarticData.g_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:44:04.201093+00:00
-- url     : https://prove2.me/submissions/f927e688-6db5-4081-b47e-9aaba3ab51a6

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local
public import Theorems.Thm_FixedNumerator_QuarticData_neg_one_zpow_sq
public import Theorems.Thm_FixedNumerator_QuarticData_chi_pow_left
public import Theorems.Thm_FixedNumerator_QuarticData_chi_pow_right
public import Theorems.Thm_FixedNumerator_QuarticData_g_mul_sq
public import Theorems.Thm_FixedNumerator_IsPrimary_pow


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (μ : GaussianInt) {π c' : GaussianInt} (hπ : IsPrimary π) (hc' : IsPrimary c')
    (hcop : IsCoprime π c') (k : ℕ) :
    D.g μ (π ^ k * c') =
      (-1 : ℂ) ^ C c' (π ^ k) * D.g μ (π ^ k) * D.g (μ * π ^ (2 * k)) c' := by
  have hk : IsCoprime (π ^ k) c' := hcop.pow_left
  rw [D.g_mul_sq μ (hπ.pow k) hc' hk]
  have h4 : D.χ π c' ^ 4 = 1 := D.chi_pow_four π c' hcop
  have hrec : D.χ c' π ^ 2 = D.χ π c' ^ 2 := by
    rw [D.reciprocity c' π hc' hπ hcop.symm, mul_pow, neg_one_zpow_sq, one_mul]
  have h1 : D.g (μ * c' ^ 2) (π ^ k) = starRingEnd ℂ ((D.χ π c' ^ 2) ^ k) * D.g μ (π ^ k) := by
    rw [mul_comm μ, D.g_twist _ _ _ (hπ.pow k) hk.symm.pow_left, D.chi_pow_left,
      D.chi_pow_right _ hπ, ← pow_mul, mul_comm k 2, pow_mul, hrec]
  have h2 : D.g (μ * π ^ (2 * k)) c' = starRingEnd ℂ ((D.χ π c' ^ 2) ^ k) * D.g μ c' := by
    rw [mul_comm μ, D.g_twist _ _ _ hc' hcop.pow_left, D.chi_pow_left, pow_mul]
  rw [h1, h2]; ring
end FixedNumerator.QuarticData
