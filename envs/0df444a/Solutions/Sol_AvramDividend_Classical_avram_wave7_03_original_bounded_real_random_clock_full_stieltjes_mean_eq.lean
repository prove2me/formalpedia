-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_bounded_real_random_clock_full_stieltjes_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:26:33.271952+00:00
-- url     : https://prove2.me/submissions/7f1746e0-532a-447c-a3ca-9f0d209569f3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact source full ruin-stopped real/ENNReal mean identity when the
    bounded measurable random clock is supplied as a nonnegative real path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ)
    (hτNonneg : ∀ ω, 0 ≤ τ ω)
    (hτBound : ∀ ω, τ ω ≤ (T : ℝ))
    (hτMeas : Measurable τ) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let θ : Ω → ℝ≥0 := fun ω => (τ ω).toNNReal
  have hCast (ω : Ω) : (θ ω : ℝ) = τ ω := by
    exact Real.coe_toNNReal (τ ω) (hτNonneg ω)
  have hBoundNN (ω : Ω) : θ ω ≤ T := by
    have hReal : (θ ω : ℝ) ≤ (T : ℝ) := by
      rw [hCast ω]
      exact hτBound ω
    exact_mod_cast hReal
  have hMeasNN : Measurable (fun ω => (θ ω : ℝ)) := by
    have hFun : (fun ω => (θ ω : ℝ)) = τ := funext hCast
    rw [hFun]
    exact hτMeas
  have hBridge :=
    avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
      X x C D hD q hq T θ hBoundNN hMeasNN
  simpa only [hCast] using hBridge
