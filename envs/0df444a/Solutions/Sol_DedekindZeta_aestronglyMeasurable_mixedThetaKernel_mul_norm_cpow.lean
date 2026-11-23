-- Prove2me | solution 1 for DedekindZeta.aestronglyMeasurable_mixedThetaKernel_mul_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:19:54.336798+00:00
-- url     : https://prove2.me/submissions/83333846-a73f-43e8-87c5-4b649699173e

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
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
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t)
      (mixedMulHaar K) := by
  -- `K` is countable (finite-dimensional over the countable field `ℚ`), hence so
  -- is the index set of the theta `∑'`; this gives `IsCountablyGenerated` for the
  -- unconditional summation filter consumed by `AEStronglyMeasurable.tsum`.
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hker : MeasureTheory.AEStronglyMeasurable
      (fun y => Theta.mixedThetaKernel K I y) (mixedMulHaar K) := by
    simp only [Theta.mixedThetaKernel]
    apply MeasureTheory.AEStronglyMeasurable.tsum
    intro a
    apply Measurable.aestronglyMeasurable
    refine Complex.measurable_ofReal.comp ?_
    unfold Theta.mixedGaussian
    fun_prop
  have hpow : MeasureTheory.AEStronglyMeasurable
      (fun y => (mixedEmbedding.norm y : ℂ) ^ t) (mixedMulHaar K) := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp
      (mixedEmbedding.continuous_norm K).measurable).pow_const t
  exact hker.mul hpow
end DedekindZeta
