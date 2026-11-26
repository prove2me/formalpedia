-- Prove2me | solution 1 for FixedNumerator.QuarticData.g_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:00.265956+00:00
-- url     : https://prove2.me/submissions/94d9c3b5-c2d9-48d7-a842-6301893e45ee

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local
public import Theorems.Thm_FixedNumerator_QuarticData_conj_sq_of_pow_four
public import Theorems.Thm_FixedNumerator_QuarticData_chi_pow_left
public import Theorems.Thm_FixedNumerator_C_symm


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (μ : GaussianInt) {c c' : GaussianInt} (hc : IsPrimary c) (hc' : IsPrimary c')
    (hcc : IsCoprime c c') :
    D.g μ (c * c') = (-1 : ℂ) ^ C c' c * D.g (μ * c' ^ 2) c * D.g μ c' := by
  have h4 : D.χ c' c ^ 4 = 1 := D.chi_pow_four c' c hcc.symm
  have htw : D.g (μ * c' ^ 2) c = starRingEnd ℂ (D.χ c' c ^ 2) * D.g μ c := by
    rw [mul_comm μ, D.g_twist _ _ _ hc (hcc.symm.pow_left), D.chi_pow_left]
  rw [D.g_mul μ c c' hc hc' hcc, htw, conj_sq_of_pow_four h4, D.reciprocity c c' hc hc' hcc,
    C_symm c c']
  ring
end FixedNumerator.QuarticData
