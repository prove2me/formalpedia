-- Prove2me | solution 1 for FixedNumerator.corollary_2_3_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:19.271261+00:00
-- url     : https://prove2.me/submissions/13946f43-fabc-4a60-a3ff-d4de2f0e8ebc

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_general


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X =
      ∑ j ∈ range (e / 4 + 1), D.g (π ^ e * μ') (π ^ (4 * j)) * W π ^ (4 * j) *
          truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (4 * j)) +
        (-1 : ℂ) ^ C (π ^ (e + 1) * β) (π ^ (e + 1)) * D.g (π ^ e * μ') (π ^ (e + 1)) *
          W π ^ (e + 1) *
          truncSum D W (π ^ e * μ' * π ^ (2 * (e + 1))) (π ^ (e + 1) * β) (π * γ)
            (X / π.norm.toNat ^ (e + 1)) :=
  D.truncSum_general W hW1 hW β hπ hπp hπγ hβ hμ' e X
end FixedNumerator
