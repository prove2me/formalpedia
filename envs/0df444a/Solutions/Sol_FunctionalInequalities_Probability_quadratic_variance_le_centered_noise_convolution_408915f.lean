-- Prove2me | solution 1 for FunctionalInequalities.Probability.quadratic_variance_le_centered_noise_convolution_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:39:29.56411+00:00
-- url     : https://prove2.me/submissions/265da305-db2d-40fb-97ae-cf31612ddaa0

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Theorems.Thm_FunctionalInequalities_Probability_memLp_quadratic_of_memLp_four_408915f
import Theorems.Thm_FunctionalInequalities_ProductVariance_decomposition_408915f

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
set_option maxHeartbeats 500000 in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (mu nu : ProbabilityMeasure E)
    (hmu4 : MemLp (id : E → E) 4 (mu : Measure E))
    (hnu4 : MemLp (id : E → E) 4 (nu : Measure E))
    (hmean : (∫ z, z ∂(nu : Measure E)) = 0) (A : E →L[ℝ] E) :
    variance (fun x : E => ⟪A x, x⟫) (mu : Measure E) ≤
      variance (fun x : E => ⟪A x, x⟫) ((mu : Measure E).conv (nu : Measure E)) := by
  let q : E → ℝ := fun x => ⟪A x, x⟫
  let f : E × E → ℝ := fun p => q (p.1 + p.2)
  have hsum4 : MemLp (fun p : E × E => p.1 + p.2) 4
      ((mu : Measure E).prod (nu : Measure E)) :=
    (hmu4.comp_fst (nu : Measure E)).add (hnu4.comp_snd (mu : Measure E))
  have hf : MemLp f 2 ((mu : Measure E).prod (nu : Measure E)) :=
    FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_408915f hsum4 A
  have hqnu : MemLp q 2 (nu : Measure E) := FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_408915f hnu4 A
  have hnu1 : Integrable (id : E → E) (nu : Measure E) :=
    (hnu4.mono_exponent (by norm_num : (1 : ENNReal) ≤ 4)).integrable le_rfl
  have hnoise (x : E) : (∫ z, f (x,z) ∂(nu : Measure E)) =
      q x + ∫ z, q z ∂(nu : Measure E) := by
    have h1 : Integrable (fun z : E => ⟪A x, z⟫) (nu : Measure E) := hnu1.const_inner (A x)
    have h2 : Integrable (fun z : E => ⟪x, A z⟫) (nu : Measure E) :=
      (A.integrable_comp hnu1).const_inner x
    have hexp (z : E) : f (x,z) = q x + ⟪A x,z⟫ + ⟪x,A z⟫ + q z := by
      simp only [f,q,map_add,inner_add_left,inner_add_right]
      rw [real_inner_comm (A z) x]
      ring
    have hi1 : (∫ z : E, ⟪A x,z⟫ ∂(nu : Measure E)) = 0 := by
      simpa only [id_eq,hmean,inner_zero_right] using (integral_inner (𝕜 := ℝ) hnu1 (A x))
    have hAz : (∫ z : E, A z ∂(nu : Measure E)) = 0 := by
      simpa only [id_eq,hmean,map_zero] using (A.integral_comp_comm hnu1)
    have hi2 : (∫ z : E, ⟪x,A z⟫ ∂(nu : Measure E)) = 0 := by
      simpa only [id_eq,hAz,inner_zero_right] using
        (integral_inner (𝕜 := ℝ) (A.integrable_comp hnu1) x)
    calc
      _ = ∫ z, q x + ⟪A x,z⟫ + ⟪x,A z⟫ + q z ∂(nu : Measure E) :=
        integral_congr_ae (ae_of_all _ hexp)
      _ = _ := by
        have hs0 := integral_add (((integrable_const (q x)).add h1).add h2) (hqnu.integrable one_le_two)
        have hs1 := integral_add ((integrable_const (q x)).add h1) h2
        have hs2 := integral_add (integrable_const (q x)) h1
        simp only [Pi.add_apply] at hs0 hs1 hs2
        rw [hs0, hs1, hs2, integral_const,hi1,hi2]
        simp
  have hdec := FunctionalInequalities.ProductVariance.decomposition_408915f hf
  have hnonneg : 0 ≤ ∫ x, variance (fun z => f (x,z)) (nu : Measure E) ∂(mu : Measure E) :=
    integral_nonneg fun x => variance_nonneg _ _
  have havg : variance (fun x => ∫ z, f (x,z) ∂(nu : Measure E)) (mu : Measure E) =
      variance q (mu : Measure E) := by
    simp_rw [hnoise]
    exact variance_add_const (by fun_prop : AEStronglyMeasurable q (mu : Measure E)) _
  have hprod : variance q (mu : Measure E) ≤
      variance f ((mu : Measure E).prod (nu : Measure E)) := by
    rw [havg] at hdec
    linarith
  have hmap : variance q ((mu : Measure E).conv (nu : Measure E)) =
      variance f ((mu : Measure E).prod (nu : Measure E)) := by
    unfold Measure.conv
    rw [variance_map (by fun_prop : AEMeasurable q _)
      (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)]
    rfl
  exact hmap.symm ▸ hprod
