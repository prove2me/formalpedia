-- Prove2me | solution 1 for DedekindZeta.Theta.fourier_mixedGaussian_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:21:58.973192+00:00
-- url     : https://prove2.me/submissions/68a7864d-128f-4070-9352-9c481402a698

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_mixedGaussian_eq
import Theorems.Thm_DedekindZeta_Theta_fourier_gaussV
import Theorems.Thm_DedekindZeta_Theta_A_x_det_abs
import Theorems.Thm_DedekindZeta_Theta_A_x_symm_adjoint_gaussV
import Theorems.Thm_DedekindZeta_Theta_fourier_comp_continuousLinearEquiv

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (x : mixedEmbedding.mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) (w : minkowskiSpace K) :
    𝓕 (fun v : minkowskiSpace K =>
        (mixedGaussian K (x * (toMinkowski K).symm v) : ℂ)) w
      = ((|mixedEmbedding.norm x|⁻¹ : ℝ) : ℂ) *
          (mixedGaussian K (x⁻¹ * (toMinkowski K).symm w) : ℂ) := by
  -- Step 1: rewrite the integrand as `gaussV K ∘ A_x`.
  have hint : (fun v : minkowskiSpace K =>
      (mixedGaussian K (x * (toMinkowski K).symm v) : ℂ))
        = fun v : minkowskiSpace K => gaussV K (A_x K hx v) := by
    funext v
    rw [A_x_apply, mixedGaussian_eq]
  rw [hint]
  -- Step 2: apply the general |det|-Jacobian Fourier law.
  rw [fourier_comp_continuousLinearEquiv (A_x K hx) (gaussV K) w]
  -- Step 3: self-duality of `gaussV`.
  rw [fourier_gaussV]
  -- Step 4: rewrite the inverse-adjoint argument and the determinant.
  rw [A_x_symm_adjoint_gaussV, ← mixedGaussian_eq, A_x_det_abs]
  -- Step 5: convert the `•` on `ℂ` into the `*` product.
  rw [smul_eq_mul]
end DedekindZeta.Theta
