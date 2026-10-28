-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:36.60584+00:00
-- url     : https://prove2.me/submissions/46f0313a-ab3e-4a4b-882b-24636d88c991

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_mul_fderiv_eq_neg_integral_mul_inner_readable

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
/-- **Zero closed gradient gives zero weak gradient**: if `T̄ h = 0`, then
`∫ h ∂_w φ dm = 0` for every `φ ∈ C_c^∞` and every `w`. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m = 0 := by
  rw [FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_readable m hν hi hνU hU h hφ hφc w, h0,
    neg_eq_zero]
  have hInt : Integrable (fun x => Real.exp (-U x)) m :=
    FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable hνU
  have hac : m ≪ (ν : Measure V) := by
    rw [hνU]
    exact absolutelyContinuous_tilted hInt
  apply integral_eq_zero_of_ae
  filter_upwards [
    hac.ae_le (Lp.coeFn_zero (E := V) (p := 2) (μ := (ν : Measure V)))
  ] with x _
  simp
