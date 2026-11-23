-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedGaussian_radialMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:55.127042+00:00
-- url     : https://prove2.me/submissions/dab69a82-d6f3-4b4e-985b-f87052ff2512

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (r : ℝ) (hr : 0 ≤ r) (σ y : mixedSpace K) :
    Theta.mixedGaussian K (radialMap K r σ * y)
      = (Theta.mixedGaussian K (σ * y)) ^ (r ^ (2 / (finrank ℚ K : ℝ))) := by
  set d : ℝ := (finrank ℚ K : ℝ) with hd
  have hc : (0 : ℝ) ≤ r ^ (d⁻¹) := Real.rpow_nonneg hr _
  -- place-wise scaling of the quadratic-form summand by `(r^{1/d})²`
  have hstep : ∀ w : InfinitePlace K,
      (mult w : ℝ) * normAtPlace w (radialMap K r σ * y) ^ 2
        = (r ^ d⁻¹) ^ 2 * ((mult w : ℝ) * normAtPlace w (σ * y) ^ 2) := by
    intro w
    rw [radialMap, smul_mul_assoc, normAtPlace_smul, abs_of_nonneg hc, mul_pow]
    ring
  rw [Theta.mixedGaussian, Theta.mixedGaussian,
    Finset.sum_congr rfl (fun w _ => hstep w), ← Finset.mul_sum]
  rw [show -Real.pi * ((r ^ d⁻¹) ^ 2 *
        ∑ w : InfinitePlace K, (mult w : ℝ) * normAtPlace w (σ * y) ^ 2)
      = (-Real.pi *
        ∑ w : InfinitePlace K, (mult w : ℝ) * normAtPlace w (σ * y) ^ 2)
        * (r ^ d⁻¹) ^ 2 by ring]
  rw [Real.exp_mul]
  congr 1
  -- `(r^{1/d})² = r^{2/d}`
  rw [← Real.rpow_natCast (r ^ d⁻¹) 2, ← Real.rpow_mul hr]
  congr 1
  push_cast
  rw [div_eq_mul_inv]
  ring
end DedekindZeta.ConeRadialReduction
