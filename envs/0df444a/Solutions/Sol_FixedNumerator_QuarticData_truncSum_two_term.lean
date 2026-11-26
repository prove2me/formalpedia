-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_two_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:39.399862+00:00
-- url     : https://prove2.me/submissions/18b7036a-25a2-4385-8295-ce767701fc4d

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_zero
public import Theorems.Thm_FixedNumerator_C_one_right
public import Theorems.Thm_FixedNumerator_IsPrimary_mul
public import Theorems.Thm_FixedNumerator_IsPrimary_pow
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_split
public import Theorems.Thm_FixedNumerator_two_le_norm_of_prime


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ : GaussianInt} (μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) {m : ℕ} (hm : m ≠ 0)
    (hsupp : ∀ k, k ≠ 0 → k ≠ m → D.g μ (π ^ k) = 0) (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β (π * γ) X +
      (-1 : ℂ) ^ C (π ^ m * β) (π ^ m) * D.g μ (π ^ m) * W π ^ m *
        truncSum D W (μ * π ^ (2 * m)) (π ^ m * β) (π * γ) (X / π.norm.toNat ^ m) := by
  rw [D.truncSum_split W hW1 hW μ β hπ hπp hπγ hβ X]
  rw [Finset.sum_eq_add 0 m (Ne.symm hm)]
  · simp [C_one_right, D.g_one]
  · intro k _ hk
    rw [hsupp k hk.1 hk.2]; simp
  · intro h; simp at h
  · intro h
    simp only [Finset.mem_range, not_lt] at h
    have hN2 := two_le_norm_of_prime hπ
    have hdiv : X / π.norm.toNat ^ m = 0 := by
      apply Nat.div_eq_of_lt
      have h1 : X < 2 ^ m := lt_trans (show X < m by omega) Nat.lt_two_pow_self
      calc X < 2 ^ m := h1
        _ ≤ π.norm.toNat ^ m := Nat.pow_le_pow_left (by omega) m
    rw [hdiv, D.truncSum_zero W _ _ ((hπp.pow m).mul hβ)]
    simp
end FixedNumerator.QuarticData
