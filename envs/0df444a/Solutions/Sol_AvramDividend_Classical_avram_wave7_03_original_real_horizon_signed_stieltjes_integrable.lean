-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_stieltjes_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:26:54.63472+00:00
-- url     : https://prove2.me/submissions/6c385162-f3ef-4c68-9197-67d8d95a4fe0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The real signed discounted Stieltjes cash on the exact original
    ruin-stopped payment set is P-integrable at every finite real horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hFInt : Integrable (fun ω => (F ω).toReal) P := by
    simpa only [F] using
      (avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
        X x C D hD T hT q)
  have hPath (ω : Ω) : F ω = ENNReal.ofReal (g ω) := by
    have h := avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
      X x D hDiv ω T.toNNReal q hq
    rw [Real.coe_toNNReal T hT] at h
    simpa only [F, g] using h
  have hNonneg (ω : Ω) : 0 ≤ g ω := by
    change 0 ≤ ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hEq : (fun ω => (F ω).toReal) =ᵐ[P] g := by
    apply Filter.Eventually.of_forall
    intro ω
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal (hPath ω)
      _ = g ω := ENNReal.toReal_ofReal (hNonneg ω)
  exact hFInt.congr hEq
