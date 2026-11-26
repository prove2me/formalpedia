-- Prove2me | solution 1 for FixedNumerator.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:05.216171+00:00
-- url     : https://prove2.me/submissions/4ec0921a-47f8-4074-8edc-4e086fec5cd7

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_split


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
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (X : ℕ) :
    truncSum D W μ β γ X =
      ∑ k ∈ range (X + 1), (-1 : ℂ) ^ C (π ^ k * β) (π ^ k) * D.g μ (π ^ k) * W π ^ k *
        truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) :=
  D.truncSum_split W hW1 hW μ β hπ hπp hπγ hβ X
end FixedNumerator
