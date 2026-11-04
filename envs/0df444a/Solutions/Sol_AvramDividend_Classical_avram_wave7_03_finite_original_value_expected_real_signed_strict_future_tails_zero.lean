-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_value_expected_real_signed_strict_future_tails_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.860555+00:00
-- url     : https://prove2.me/submissions/ec80f82e-3804-4be5-b41d-7e0a9d19ee2c

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_expected_strict_future_ennreal_tails_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_random_strict_future_signed_L1_exact_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite original value forces genuine expected real signed
    Stieltjes cash strictly after a deterministic horizon to vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let F : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P
  let G : ℕ → ℝ := fun n =>
    ∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P
  have hTail : Tendsto F atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [F] using
      (avram_wave7_03_finite_value_expected_strict_future_ennreal_tails_tendsto_zero
        X x D hD q hFinite)
  have hEq (n : ℕ) : F n = ENNReal.ofReal (G n) := by
    simpa only [F, G] using
      (avram_wave7_03_finite_original_value_random_strict_future_signed_L1_exact_mean
        X x D hD q (fun _ => (n : ℝ)) measurable_const hFinite).2
  have hGPos (n : ℕ) : 0 ≤ G n := by
    dsimp [G]
    apply integral_nonneg
    intro ω
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hGToReal (n : ℕ) : G n = (F n).toReal := by
    calc
      G n = (ENNReal.ofReal (G n)).toReal :=
        (ENNReal.toReal_ofReal (hGPos n)).symm
      _ = (F n).toReal := congrArg ENNReal.toReal (hEq n).symm
  have hToReal : Tendsto (fun n => (F n).toReal) atTop (𝓝 (0 : ℝ)) :=
    (ENNReal.tendsto_toReal (show (0 : ℝ≥0∞) ≠ ⊤ by simp)).comp hTail
  have hFunEq : G = (fun n => (F n).toReal) := funext hGToReal
  change Tendsto G atTop (𝓝 (0 : ℝ))
  rw [hFunEq]
  exact hToReal
