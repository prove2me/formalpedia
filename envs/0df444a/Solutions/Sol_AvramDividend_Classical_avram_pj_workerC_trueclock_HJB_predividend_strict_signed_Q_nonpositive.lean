-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_trueclock_HJB_predividend_strict_signed_Q_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:10:39.346675+00:00
-- url     : https://prove2.me/submissions/add1a129-8d5e-482c-a690-38e321ee5ac8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_grid_dividend_points_pre_ruin
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_physical_HJB_B_plus_finite_rightpayment_Q_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (u v δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (huv : u + δ < v) (hvCap : v < C.toReal)
    (T : ℝ≥0) (τ ρ : Ω → ℝ≥0)
    (n : ℕ) (hn : 0 < n)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (A : Ω → Finset ℝ≥0)
    (hStrict : ∀ ω t, t ∈ A ω → t = 0 ∨ t < ρ ω) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
          (if Y p ∈ Icc (u + δ) v then
            X.generator w (Y p) - q * w (Y p) else 0))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let B : Ω → ℝ := fun ω =>
      ∫ t : ℝ≥0, if t ≤ ρ ω then R (t, ω) else 0 ∂μT
    let Q : Ω → ℝ := fun ω => B ω +
      ∑ t ∈ A ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) -
          (w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω))))
    ∀ ω, Q ω ≤ 0 := by
  intro Y R μT B Q ω
  have hPre :=
    AvramDividend.Classical.avram_pj_workerC_strict_grid_dividend_points_pre_ruin
      X x C D hD n hn τ ρ hτeq hρle A hStrict
  exact
    AvramDividend.Classical.avram_pj_workerC_original_physical_HJB_B_plus_finite_rightpayment_Q_nonpositive
      X q w C hCfinite hw_gen x D hjump
      u v δ hu hδ huv hvCap T ρ A hPre ω

