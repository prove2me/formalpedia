-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_original_discounted_final_contact_constant_DCT
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:04:56.817536+00:00
-- url     : https://prove2.me/submissions/4dbd5eb3-fd5e-4f3e-97c4-61de50d1854b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual nonnegative physical stopped times give discount factors in
[0,1], preserving a.e. and L1 positive-error convergence without circularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (K : ℝ) (hK : 0 ≤ K)
    (Raw Disc : ℕ → Ω → ℝ)
    (hRawAE : ∀ᵐ ω ∂P, Tendsto (fun m => Raw m ω) atTop (nhds (0 : ℝ)))
    (hRawDom : ∀ m, ∀ᵐ ω ∂P, ‖Raw m ω‖ ≤ K)
    (hDiscSource : ∀ m ω, Disc m ω =
      Real.exp (-(q * (u m (k m ω - 1) : ℝ))) * Raw m ω)
    (hDiscMeas : ∀ m, AEStronglyMeasurable (Disc m) P) :
    (∀ m, Integrable (fun ω => max (Disc m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Disc m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hfactor (m : ℕ) (ω : Ω) :
      0 ≤ Real.exp (-(q * (u m (k m ω - 1) : ℝ))) ∧
      Real.exp (-(q * (u m (k m ω - 1) : ℝ))) ≤ 1 := by
    constructor
    · exact (Real.exp_nonneg _)
    · apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (mul_nonneg hq (u m (k m ω - 1)).property)
  have hnorm (m : ℕ) (ω : Ω) : ‖Disc m ω‖ ≤ ‖Raw m ω‖ := by
    rw [hDiscSource m ω]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfactor m ω).1]
    calc
      Real.exp (-(q * (u m (k m ω - 1) : ℝ))) * |Raw m ω| ≤
        1 * |Raw m ω| := mul_le_mul_of_nonneg_right (hfactor m ω).2 (abs_nonneg _)
      _ = |Raw m ω| := one_mul _
  have hDiscAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => Disc m ω) atTop (nhds (0 : ℝ)) := by
    filter_upwards [hRawAE] with ω hω
    apply (Metric.tendsto_atTop).2
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).1 hω ε hε
    refine ⟨N, ?_⟩
    intro m hm
    have hsmall : ‖Raw m ω‖ < ε := by
      simpa [Real.dist_eq, Real.norm_eq_abs] using hN m hm
    have hb := lt_of_le_of_lt (hnorm m ω) hsmall
    simpa [Real.dist_eq, Real.norm_eq_abs] using hb
  have hDiscDom : ∀ m, ∀ᵐ ω ∂P, ‖Disc m ω‖ ≤ K := by
    intro m
    filter_upwards [hRawDom m] with ω hω
    exact (hnorm m ω).trans hω
  exact avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT
    X hX K hK Disc hDiscMeas hDiscAE hDiscDom
