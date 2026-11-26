-- Prove2me | solution 1 for FixedNumerator.two_term_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:10.09867+00:00
-- url     : https://prove2.me/submissions/1e573a37-31ed-4764-b5d5-2dbcf621b389

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_two_term


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (m : ℕ) (hm : m ≠ 0)
    (hsupp : ∀ k, k ≠ 0 → k ≠ m → D.g μ (π ^ k) = 0) (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β (π * γ) X +
      (-1 : ℂ) ^ C (π ^ m * β) (π ^ m) * D.g μ (π ^ m) * W π ^ m *
        truncSum D W (μ * π ^ (2 * m)) (π ^ m * β) (π * γ) (X / π.norm.toNat ^ m) :=
  D.truncSum_two_term W hW1 hW μ β hπ hπp hπγ hβ hm hsupp X
end FixedNumerator
