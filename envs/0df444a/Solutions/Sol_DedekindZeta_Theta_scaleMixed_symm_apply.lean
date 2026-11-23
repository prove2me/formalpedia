-- Prove2me | solution 1 for DedekindZeta.Theta.scaleMixed_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:47.76968+00:00
-- url     : https://prove2.me/submissions/25e8e4c2-eca3-4dc2-b617-f64be01d054e

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (x : mixedSpace K) :
    (scaleMixed K).symm x = (x.1, (Real.sqrt 2)⁻¹ • x.2) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  symm
  rw [← ContinuousLinearEquiv.symm_apply_eq]
  show (scaleMixed K) (x.1, (Real.sqrt 2)⁻¹ • x.2) = x
  rw [scaleMixed]
  ext i
  · rfl
  · show (sqrtTwo : ℝ) • ((Real.sqrt 2)⁻¹ • x.2) i = x.2 i
    simp only [sqrtTwo, Units.val_mk0, Pi.smul_apply]
    rw [smul_smul, mul_inv_cancel₀ hsqrt, one_smul]
end DedekindZeta.Theta
