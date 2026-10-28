-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.meanGradSq_eq_norm_taylorField_one_genField_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:28:35.679993+00:00
-- url     : https://prove2.me/submissions/5ebad522-021a-44ea-832f-5e2de05da277

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorTensor_gen_apply_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The Taylor tensor of degree `0` is the mean: `T_0 u = ∫ u dν`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_zero_Lp (u : Lp ℝ 2 (ν : Measure V)) (v : Fin 0 → V) :
    taylorTensor (ν : Measure V) (⇑u) 0 v = L2.mean ν u := by
  simp [taylorTensor, tiltAverage, expTilt, L2.mean_eq_integral]
end Generic
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
variable {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
include hνU hU hexp in
/-- **BKL (49)** for tensor fields in `D(A)`: `|∫ ∇h|² = |T₁(-L h)|²`, i.e. the squared means of the
components of `∇h` sum to the squared Hilbert–Schmidt norm of `T₁` of `-L h`. -/
theorem solution {k : ℕ} (h : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k)
    (hh : ∀ I, h I ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.meanGradSq T̄ h = ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField 1 (FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField T̄ h)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, FunctionalInequalities.KLS.LogConcave.PoissonIterate.meanGradSq]
  let e : (Fin (k + 1) → Fin (Module.finrank ℝ V)) ≃ (Fin (1 + k) → Fin (Module.finrank ℝ V)) :=
    (Fin.consEquiv fun _ => Fin (Module.finrank ℝ V)).symm.trans
      (((Equiv.funUnique (Fin 1) _).symm.prodCongr (Equiv.refl _)).trans (Fin.appendEquiv 1 k))
  refine Fintype.sum_equiv e _ _ fun K => ?_
  have h1 : (fun p : Fin k => e K (Fin.natAdd 1 p)) = Fin.tail K := by
    funext p
    simp [e, Fin.consEquiv]
  have h2 : (fun p : Fin 1 => stdOrthonormalBasis ℝ V (e K (Fin.castAdd k p))) =
      fun p => stdOrthonormalBasis ℝ V ((fun _ : Fin 1 => K 0) p) := by
    funext p
    simp [e, Fin.consEquiv]
  simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField, PiLp.toLp_apply, FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField, Real.norm_eq_abs, sq_abs]
  rw [h1, h2, FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_gen_apply_readable m hν hi hνU hU hexp (hh _) 0]
  simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_zero_Lp, FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField]
