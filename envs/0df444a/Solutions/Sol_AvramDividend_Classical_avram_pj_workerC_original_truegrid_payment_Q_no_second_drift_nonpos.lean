-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_truegrid_payment_Q_no_second_drift_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:54:34.120212+00:00
-- url     : https://prove2.me/submissions/e8173172-b96b-49da-a895-c5ec677b2719

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_grid_dividend_points_pre_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (k : ℕ) (ω : Ω) :
    let mesh : Finset ℝ≥0 :=
      ((Finset.range (k + 1)).image
        (fun i : ℕ => min
          ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
          (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
    (∑ t ∈ mesh, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
      (w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
        (rightLimit D t ω - D t ω))))) ≤ 0 := by 
  let grid : Ω → Finset ℝ≥0 := fun ζ =>
    ((Finset.range (k + 1)).image (fun i : ℕ => min
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
      (ρ ζ))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ζ)
  have hgrid : ∀ ζ t, t ∈ grid ζ → t = 0 ∨ t < ρ ζ := by
    intro ζ t ht
    exact (Finset.mem_filter.mp ht).2
  have hpre :=
    avram_pj_workerC_strict_grid_dividend_points_pre_ruin
      X x C D hD n hn τ ρ hτeq hρle grid hgrid
  change (∑ t ∈ grid ω, Real.exp (-(q * (t : ℝ))) *
    ((rightLimit D t ω - D t ω) -
      (w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))))) ≤ 0
  apply Finset.sum_nonpos
  intro t ht
  have hdrop := hjump ω t (hpre ω t ht)
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
    (sub_nonpos.mpr hdrop)
