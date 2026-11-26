-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_num_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:44:03.108007+00:00
-- url     : https://prove2.me/submissions/f25f7415-c37c-4f26-b6f4-6ec43f07ab69

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases
public import Theorems.Thm_FixedNumerator_IsPrimary_of_dvd_sub
public import Theorems.Thm_FixedNumerator_QuarticData_g_mul_pow_four


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (W : GaussianInt → ℂ) (μ : GaussianInt) {π γ β : GaussianInt}
    (hβ : IsPrimary β) (j X : ℕ) :
    truncSum D W (μ * π ^ (4 * j)) β (π * γ) X = truncSum D W μ β (π * γ) X := by
  classical
  unfold truncSum
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Finset.mem_filter] at hc
  have hcp : IsPrimary c := hβ.of_dvd_sub hc.2.1
  have hcop : IsCoprime π c := (IsCoprime.mul_right_iff.mp hc.2.2).1.symm
  rw [D.g_mul_pow_four μ hcp hcop j]
end FixedNumerator.QuarticData
