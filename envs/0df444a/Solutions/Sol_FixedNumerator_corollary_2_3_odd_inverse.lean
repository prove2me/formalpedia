-- Prove2me | solution 1 for FixedNumerator.corollary_2_3_odd_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:50:26.818591+00:00
-- url     : https://prove2.me/submissions/4ef3b4d9-9ffd-4a87-b86f-a214f4676fa3

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_single_inv


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
    (e : ℕ) (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X =
      ∑ j ∈ range (X + 1), (-(D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1))) ^ j *
        truncSum D W (π ^ e * μ') β γ (X / (π.norm.toNat ^ (e + 1)) ^ j) :=
  D.truncSum_single_inv W hW1 hW β hπ hπp hπγ hβ hμ' he X
end FixedNumerator
