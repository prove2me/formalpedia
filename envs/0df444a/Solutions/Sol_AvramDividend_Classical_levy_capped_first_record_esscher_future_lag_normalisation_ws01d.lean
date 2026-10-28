-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_first_record_esscher_future_lag_normalisation_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:27:44.189888+00:00
-- url     : https://prove2.me/submissions/42fd3c3e-ce41-41d8-aa60-a9f1d1420285

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

/-- Every fixed future-lag Esscher exponential has unit conditional
normalisation at an uncensored capped first upper record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N u : ℝ≥0)
    (phi q : ℝ) (hphi : 0 ≤ phi) (hroot : X.ψ phi = q)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       ENNReal.ofReal (Real.exp
         (phi * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
            (u : ℝ) * q))
       else 0 ∂P) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P)) := by
  let R : (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun f => ENNReal.ofReal (Real.exp (phi * f u - (u : ℝ) * q))
  have hEval : Measurable (fun f : ℝ≥0 → ℝ => f u) :=
    measurable_pi_apply u
  have hR : Measurable R := by
    dsimp [R]
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul hEval).sub measurable_const))
  have hRealFun :
      (fun ω : Ω => Real.exp (phi * X.X u ω - (u : ℝ) * q)) =
      (fun ω : Ω => Real.exp (-(u : ℝ) * q) *
        Real.exp (phi * X.X u ω)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hInt :
      Integrable (fun ω : Ω =>
        Real.exp (phi * X.X u ω - (u : ℝ) * q)) P := by
    rw [hRealFun]
    exact (X.laplace u phi hphi).1.const_mul _
  have hMoment :
      (∫⁻ ω, R (fun t : ℝ≥0 => X.X t ω) ∂P) = 1 := by
    change (∫⁻ ω, ENNReal.ofReal
      (Real.exp (phi * X.X u ω - (u : ℝ) * q)) ∂P) = 1
    calc
      _ = ENNReal.ofReal
          (∫ ω, Real.exp (phi * X.X u ω - (u : ℝ) * q) ∂P) := by
        exact (ofReal_integral_eq_lintegral_ofReal hInt
          (Filter.Eventually.of_forall
            (fun ω => le_of_lt (Real.exp_pos _)))).symm
      _ = ENNReal.ofReal (1 : ℝ) := by
        congr 1
        rw [hRealFun, integral_const_mul, (X.laplace u phi hphi).2]
        change Real.exp (-(u : ℝ) * q) *
          Real.exp ((u : ℝ) * X.ψ phi) = 1
        rw [hroot, ← Real.exp_add]
        have hz : -(u : ℝ) * q + (u : ℝ) * q = 0 := by ring
        rw [hz, Real.exp_zero]
      _ = 1 := by norm_num
  have hFactor :=
    avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor
      X b N discount hd R hR
  simpa only [hMoment, mul_one, R] using hFactor
