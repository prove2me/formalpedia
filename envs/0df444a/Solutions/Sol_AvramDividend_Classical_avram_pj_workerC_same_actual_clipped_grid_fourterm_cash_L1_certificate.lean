-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_same_actual_clipped_grid_fourterm_cash_L1_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:37:06.770453+00:00
-- url     : https://prove2.me/submissions/4386bbc1-2d9d-421a-9c3e-c021c186160d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_trueclip_original_discount_cash_abs_mesh_eventual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n)
    (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (w : ℝ → ℝ) (m : ℕ) (ω : Ω) :
    (let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    u (m + 1) = ρ ω ∧
    E (u (m + 1)) * w (Y (u (m + 1))) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω)))) ∧
    (let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, |E m ω| ∂P) ≤ ε) := by
  have hClock :=
    avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ ρ hτeq hρle
  constructor
  · exact avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
      X x q D hD.1.1 w ρ n m hClock.1 ω
  · exact avram_pj_workerC_trueclip_original_discount_cash_abs_mesh_eventual
      X hX x C D hD q hq n hn τ ρ hτeq hρstop hρle
