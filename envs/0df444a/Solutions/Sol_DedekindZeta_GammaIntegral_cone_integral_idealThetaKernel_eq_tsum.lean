-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.cone_integral_idealThetaKernel_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:58.423169+00:00
-- url     : https://prove2.me/submissions/535befaf-38b7-40f8-b918-2ac480e09fd9

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_measurable_mixedGaussian_comp_mul_norm_cpow
import Theorems.Thm_DedekindZeta_GammaIntegral_tsum_lintegral_enorm_cone_mixedGaussian_ne_top
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∫ x, (mixedEmbedding.fundamentalCone K).indicator
            (fun x => Theta.idealThetaKernel K a x * (mixedEmbedding.norm x : ℂ) ^ s) x
          ∂(mixedMulHaar K)
      = ∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K) := by
  classical
  haveI : Countable (RingOfIntegers K) := by
    let b := Module.Free.chooseBasis ℤ (RingOfIntegers K)
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  set C := mixedEmbedding.fundamentalCone K with hC
  set μ := mixedMulHaar K with hμ
  -- The per-element indicator integrand `F a'`.
  set F : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0}
      → mixedEmbedding.mixedSpace K → ℂ :=
    fun a' x => C.indicator
      (fun x => (mixedGaussian K
          (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
        * (mixedEmbedding.norm x : ℂ) ^ s) x with hF
  -- Each `F a'` is `AEStronglyMeasurable` (Borel indicator of a Borel function).
  have hmeas : ∀ a', AEStronglyMeasurable (F a') μ := by
    intro a'
    exact ((measurable_mixedGaussian_comp_mul_norm_cpow s
      (mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))).aestronglyMeasurable).indicator
      (measurableSet_fundamentalCone K)
  -- The `lintegral`-norm series is finite, so `integral_tsum` applies.
  have hfin : (∑' a', ∫⁻ x, ‖F a' x‖ₑ ∂μ) ≠ ∞ :=
    tsum_lintegral_enorm_cone_mixedGaussian_ne_top s hs ha
  have key := integral_tsum (μ := μ) (f := F) hmeas hfin
  -- Pointwise, the indicator of the kernel × norm-power equals `∑' a', F a' x`.
  have hpt : (fun x => C.indicator
        (fun x => Theta.idealThetaKernel K a x * (mixedEmbedding.norm x : ℂ) ^ s) x)
      = (fun x => ∑' a', F a' x) := by
    funext x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      have hFx : ∀ a', F a' x
          = (mixedGaussian K
              (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s := by
        intro a'; rw [hF]; simp only [Set.indicator_of_mem hx]
      simp only [hFx]
      rw [Theta.idealThetaKernel, ← tsum_mul_right]
    · rw [Set.indicator_of_notMem hx]
      have hFx : ∀ a', F a' x = 0 := by
        intro a'; rw [hF]; simp only [Set.indicator_of_notMem hx]
      simp only [hFx, tsum_zero]
  rw [hpt, key]
end DedekindZeta.GammaIntegral
