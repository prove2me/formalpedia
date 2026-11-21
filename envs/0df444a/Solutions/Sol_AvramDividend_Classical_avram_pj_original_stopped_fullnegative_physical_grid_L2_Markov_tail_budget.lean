-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_stopped_fullnegative_physical_grid_L2_Markov_tail_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T17:38:11.286498+00:00
-- url     : https://prove2.me/submissions/52abeee4-24d7-4c24-afd7-afec18b09a76

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_stopped_clipped_physical_grid_martingale_uniform_L2_no_extra_hypotheses
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hn : 0 < n) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    Integrable (fun ω =>
      (∑ i ∈ Finset.range m, Z i ω)^2) P →
    ∀ threshold : ℝ,
    threshold^2 * P.real {ω | threshold^2 ≤
      (∑ i ∈ Finset.range m, Z i ω)^2} ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
  intro Δ grid N r H Z hSquare threshold
  have hNonneg :
      0 ≤ᵐ[P] (fun ω => (∑ i ∈ Finset.range m, Z i ω)^2) :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hTrueMarkovBound := mul_meas_ge_le_integral_of_nonneg
    (μ := P) hNonneg hSquare (threshold^2)
  have hEnergy :=
    avram_pj_original_fullnegative_stopped_clipped_physical_grid_martingale_uniform_L2_no_extra_hypotheses
      X x D hD w q K hK cut ρ hρstop n m hn
  exact hTrueMarkovBound.trans hEnergy
