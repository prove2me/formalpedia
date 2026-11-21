-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_subordinate_stop_fullmark_physical_true_Stieltjes_right_payment_Q_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T17:40:23.463311+00:00
-- url     : https://prove2.me/submissions/8459a676-5b09-45ef-b503-279e61647b2a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_exact_ruinbounded_truegrid_zero_mask_filtered_right_payment_Q_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original stopped and filtered physical dividend-payment
correction is nonpositive at every refinement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω) :
    let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      ((Finset.range (k + 1)).image
        (fun i : ℕ => min
          ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
          (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      if ρ ω = 0 then 0 else ∑ t ∈ A k ω,
        Real.exp (-(q * (t : ℝ))) *
          ((rightLimit D t ω - D t ω) -
            (w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω))))
    ∀ k ω, Q k ω ≤ 0 := by
  have hρruin :=
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ ρ hτeq hρle).2
  exact avram_pj_original_exact_ruinbounded_truegrid_zero_mask_filtered_right_payment_Q_nonpositive
    X x D q w hjump n ρ hρruin
