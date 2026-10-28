-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_zero_eq_iInf_reciprocal_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:29:31.393866+00:00
-- url     : https://prove2.me/submissions/97e3e6de-8e6d-487f-abf7-d1a1c5200ca5

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_eq_iInf_reciprocal
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_runningSup_discountedReward_antitone_reciprocal
import Theorems.Thm_AvramDividend_Classical_runningSup_discountedReward_iInf_stopped_of_finite
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_reward_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite positive-barrier rewards yield zero-barrier convergence of expected rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hfinite : barrierSupValue X 1 q ≠ ⊤)
    (hpath : ∀ ω : Ω,
      (∫⁻ t in paymentTimes (barrierRuinTime X 1 ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω)) ≠ ⊤) :
    barrierSupValue X 0 q =
      ⨅ n : ℕ, barrierSupValue X (1 / ((n : ℝ) + 1)) q := by
  classical
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let R : ℝ → Ω → ℝ≥0∞ := fun a ω =>
    ∫⁻ t in paymentTimes (barrierRuinTime X a ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (runningSup X) ω)
  have hmeasR (a : ℝ) : Measurable (R a) := by
    have h := runningSup_stopped_full_reward_measurable X a q
    have heq : R a = fun ω : Ω =>
        ∫⁻ t,
          if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω) := by
      funext ω
      exact (lintegral_indicator
        (paymentTimes_measurable (barrierRuinTime X a ω))
        (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))).symm
    rw [heq]
    exact h
  have hmono : Antitone (fun n : ℕ => R (r n)) := by
    intro i j hij ω
    exact runningSup_discountedReward_antitone_reciprocal X ω q hij
  have hσ (ω : Ω) :
      Antitone (fun n : ℕ => barrierRuinTime X (r n) ω) := by
    intro i j hij
    have hbar : r j ≤ r i := by
      dsimp [r]
      apply one_div_le_one_div_of_le (by positivity)
      have hreal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      exact add_le_add_left hreal 1
    exact barrierRuinTime_mono_barrier X (r j) (r i) hbar ω
  have hlimit (ω : Ω) : R 0 ω = ⨅ n, R (r n) ω := by
    have hi := runningSup_discountedReward_iInf_stopped_of_finite
      X ω (fun n => barrierRuinTime X (r n) ω)
      (hσ ω) q (by simpa [r] using hpath ω)
    dsimp only [R]
    rw [barrierRuinTime_zero_eq_iInf_reciprocal X ω]
    simpa [R, r] using hi
  have hfiniteR : (∫⁻ ω, R (r 0) ω ∂P) ≠ ⊤ := by
    simpa [R, r, barrierSupValue] using hfinite
  have hMCT := lintegral_iInf (fun n => hmeasR (r n))
    hmono hfiniteR
  have hout : (∫⁻ ω, R 0 ω ∂P) =
      ⨅ n, (∫⁻ ω, R (r n) ω ∂P) := by
    calc
      (∫⁻ ω, R 0 ω ∂P) =
          ∫⁻ ω, ⨅ n, R (r n) ω ∂P := by
        congr 1
        funext ω
        exact hlimit ω
      _ = ⨅ n, ∫⁻ ω, R (r n) ω ∂P := hMCT
  simpa [R, r, barrierSupValue] using hout
