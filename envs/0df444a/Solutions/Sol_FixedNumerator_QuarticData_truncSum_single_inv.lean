-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_single_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:15.59923+00:00
-- url     : https://prove2.me/submissions/689d5512-c950-4426-8bff-f77f8c4597e4

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_zero
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_single
public import Theorems.Thm_FixedNumerator_QuarticData_invert_two_term
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
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    {e : ℕ} (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X =
      ∑ j ∈ range (X + 1), (-(D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1))) ^ j *
        truncSum D W (π ^ e * μ') β γ (X / (π.norm.toNat ^ (e + 1)) ^ j) := by
  have hN2 := two_le_norm_of_prime hπ
  apply invert_two_term (fun Y => truncSum D W (π ^ e * μ') β γ Y)
    (fun Y => truncSum D W (π ^ e * μ') β (π * γ) Y)
  · calc 2 ≤ π.norm.toNat := by omega
      _ ≤ π.norm.toNat ^ (e + 1) := Nat.le_self_pow (by omega) _
  · exact D.truncSum_zero W _ _ hβ
  · intro Y; exact D.truncSum_single W hW1 hW β hπ hπp hπγ hβ hμ' he Y
  · exact le_refl _
end FixedNumerator.QuarticData
