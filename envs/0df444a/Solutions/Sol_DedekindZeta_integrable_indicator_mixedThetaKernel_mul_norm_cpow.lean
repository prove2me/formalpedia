-- Prove2me | solution 1 for DedekindZeta.integrable_indicator_mixedThetaKernel_mul_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:44.647802+00:00
-- url     : https://prove2.me/submissions/2f1496a0-2371-4b6c-b516-4c21f8b5e8df

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_aestronglyMeasurable_mixedThetaKernel_mul_norm_cpow
import Theorems.Thm_DedekindZeta_tsum_lintegral_enorm_cone_mixedThetaKernel_summand_ne_top
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
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) (ht : 1 < t.re) :
    MeasureTheory.Integrable
      ((mixedEmbedding.fundamentalCone K).indicator
        (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t))
      (mixedMulHaar K) := by
  classical
  -- `K` is countable, hence so is the index set of the theta `∑'`; needed for
  -- `lintegral_tsum` below.
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  -- Measurability is already available; only `HasFiniteIntegral` remains.
  refine ⟨(aestronglyMeasurable_mixedThetaKernel_mul_norm_cpow K I t).indicator
    (mixedEmbedding.measurableSet_fundamentalCone K), ?_⟩
  -- Per-element cone-indicator integrand `F a`.
  set F : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}
      → mixedEmbedding.mixedSpace K → ℂ :=
    fun a x => (mixedEmbedding.fundamentalCone K).indicator
      (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
        * (mixedEmbedding.norm y : ℂ) ^ t) x with hF
  -- Each `x ↦ ‖F a x‖ₑ` is measurable (enorm of a Borel indicator).
  have hFmeas : ∀ a, Measurable (fun x => ‖F a x‖ₑ) := by
    intro a
    refine Measurable.enorm ?_
    refine Measurable.indicator ?_ (mixedEmbedding.measurableSet_fundamentalCone K)
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp ?_
      unfold Theta.mixedGaussian; fun_prop
    · exact (Complex.measurable_ofReal.comp
        (mixedEmbedding.continuous_norm K).measurable).pow_const t
  -- Pointwise: the enorm of the kernel-integrand cone indicator is dominated by
  -- the `∑'` of the per-element enorms (triangle inequality for `∑'`).
  have hbound : ∀ x,
      ‖(mixedEmbedding.fundamentalCone K).indicator
          (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ
        ≤ ∑' a, ‖F a x‖ₑ := by
    intro x
    by_cases hx : x ∈ mixedEmbedding.fundamentalCone K
    · rw [Set.indicator_of_mem hx, Theta.mixedThetaKernel, ← tsum_mul_right]
      refine le_trans enorm_tsum_le_tsum_enorm (le_of_eq (tsum_congr (fun a => ?_)))
      simp only [hF, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; simp
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
          (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ
            ∂(mixedMulHaar K)
      ≤ ∫⁻ x, ∑' a, ‖F a x‖ₑ ∂(mixedMulHaar K) := MeasureTheory.lintegral_mono hbound
    _ = ∑' a, ∫⁻ x, ‖F a x‖ₑ ∂(mixedMulHaar K) :=
        MeasureTheory.lintegral_tsum (fun a => (hFmeas a).aemeasurable)
    _ < ∞ := (tsum_lintegral_enorm_cone_mixedThetaKernel_summand_ne_top K I t ht).lt_top
end DedekindZeta
