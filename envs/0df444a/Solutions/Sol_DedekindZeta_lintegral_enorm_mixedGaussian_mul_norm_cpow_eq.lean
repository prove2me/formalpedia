-- Prove2me | solution 1 for DedekindZeta.lintegral_enorm_mixedGaussian_mul_norm_cpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:21:18.966972+00:00
-- url     : https://prove2.me/submissions/dcc74895-48d2-423b-997a-8973b5b68be8

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_measurable_mul_right_mixedSpace
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
namespace DedekindZeta
theorem _root_.solution
    {a : K} (ha : a ≠ 0) (t : ℂ) :
    ∫⁻ x, ‖(Theta.mixedGaussian K (x * mixedEmbedding K a) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K)
      = ENNReal.ofReal (mixedEmbedding.norm (mixedEmbedding K a) ^ (-t.re))
          * ∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) := by
  -- Mirror `GammaIntegral.mellin_mixedGaussian_mul_eq`, but on `ℝ≥0∞`/`enorm`.
  set c : mixedEmbedding.mixedSpace K := mixedEmbedding K a with hcdef
  have hcne : mixedEmbedding.norm c ≠ 0 := by
    have hn : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
    rw [hcdef, mixedEmbedding.norm_eq_norm]
    simpa using hn
  have hcpos : 0 < mixedEmbedding.norm c :=
    (mixedEmbedding.norm_nonneg c).lt_of_ne (Ne.symm hcne)
  have hcinvpos : 0 < (mixedEmbedding.norm c)⁻¹ := inv_pos.mpr hcpos
  have hcc : c * c⁻¹ = 1 := Theta.mul_inv_cancel_of_norm_ne_zero K hcne
  -- `N(c⁻¹) = (N c)⁻¹` from `N(c)·N(c⁻¹) = N(1) = 1` (the downstream
  -- `mixedEmbedding_norm_inv` is not available at this layer).
  have hNcinv : mixedEmbedding.norm c⁻¹ = (mixedEmbedding.norm c)⁻¹ := by
    have h1 : mixedEmbedding.norm c * mixedEmbedding.norm c⁻¹ = 1 := by
      rw [← map_mul, hcc, map_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  -- The integrand is `F (x·c)` with `F y = g y · N(y·c⁻¹)^t`.
  set F : mixedEmbedding.mixedSpace K → ℂ :=
    fun y => (Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c⁻¹) : ℂ) ^ t
    with hFdef
  have hFmeas : Measurable (fun y => ‖F y‖ₑ) := by
    refine Measurable.enorm ?_
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp ?_
      unfold Theta.mixedGaussian; fun_prop
    · refine (Complex.measurable_ofReal.comp ?_).pow_const t
      exact (mixedEmbedding.continuous_norm K).measurable.comp
        (continuous_id.mul continuous_const).measurable
  -- Base (unshifted) integrand measurability, for `lintegral_mul_const`.
  have hgmeas : Measurable
      (fun y => ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ) := by
    refine Measurable.enorm ?_
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp ?_
      unfold Theta.mixedGaussian; fun_prop
    · exact (Complex.measurable_ofReal.comp
        (mixedEmbedding.continuous_norm K).measurable).pow_const t
  -- Rewrite the LHS integrand as `‖F (x·c)‖ₑ`.
  have hrw : (fun x => ‖(Theta.mixedGaussian K (x * c) : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ)
      = fun x => ‖F (x * c)‖ₑ := by
    funext x
    simp only [hFdef, mul_assoc, hcc, mul_one]
  -- Right-translation invariance of `mixedMulHaar` substitutes `x ↦ x·c`.
  have hmap := mixedMulHaar_map_mul_right (K := K) hcne
  have hsub : ∫⁻ x, ‖F (x * c)‖ₑ ∂(mixedMulHaar K)
      = ∫⁻ y, ‖F y‖ₑ ∂(mixedMulHaar K) := by
    rw [← MeasureTheory.lintegral_map hFmeas (measurable_mul_right_mixedSpace K c), hmap]
  -- Pointwise factorization of the constant `N(c)^{-Re t}` out of the `enorm`.
  have hptw : ∀ y, ‖F y‖ₑ
      = ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ
          * ENNReal.ofReal (mixedEmbedding.norm c ^ (-t.re)) := by
    intro y
    rw [hFdef]
    simp only
    rw [map_mul mixedEmbedding.norm y c⁻¹, hNcinv,
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg y)
        (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c)) t,
      ← mul_assoc, enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hcinvpos,
      Real.inv_rpow (mixedEmbedding.norm_nonneg c),
      ← Real.rpow_neg (mixedEmbedding.norm_nonneg c)]
  calc
    ∫⁻ x, ‖(Theta.mixedGaussian K (x * c) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K)
        = ∫⁻ x, ‖F (x * c)‖ₑ ∂(mixedMulHaar K) := by rw [hrw]
      _ = ∫⁻ y, ‖F y‖ₑ ∂(mixedMulHaar K) := hsub
      _ = ∫⁻ y, ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ
              * ENNReal.ofReal (mixedEmbedding.norm c ^ (-t.re)) ∂(mixedMulHaar K) :=
          MeasureTheory.lintegral_congr hptw
      _ = (∫⁻ y, ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ
              ∂(mixedMulHaar K))
            * ENNReal.ofReal (mixedEmbedding.norm c ^ (-t.re)) :=
          MeasureTheory.lintegral_mul_const _ hgmeas
      _ = ENNReal.ofReal (mixedEmbedding.norm c ^ (-t.re))
            * ∫⁻ y, ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ
              ∂(mixedMulHaar K) := by rw [mul_comm]
end DedekindZeta
