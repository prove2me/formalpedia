-- Prove2me | solution 1 for DedekindZeta.ofReal_inv_cpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:46:40.9166+00:00
-- url     : https://prove2.me/submissions/feacca3d-874a-41f4-aff8-ab6b7ed5b567

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta
theorem _root_.solution {r : ℝ} (hr : 0 ≤ r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ s = ((r : ℝ) : ℂ) ^ (-s) := by
  rcases eq_or_lt_of_le hr with rfl | hr'
  · simp only [inv_zero, Complex.ofReal_zero]
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · rw [Complex.zero_cpow hs0, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · have h4 : (r : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr]; exact (Real.pi_ne_zero).symm
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ h4, Complex.cpow_neg]
end DedekindZeta
