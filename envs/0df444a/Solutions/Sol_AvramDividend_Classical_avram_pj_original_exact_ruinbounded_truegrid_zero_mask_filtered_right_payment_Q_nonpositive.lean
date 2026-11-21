-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_exact_ruinbounded_truegrid_zero_mask_filtered_right_payment_Q_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:53:15.375269+00:00
-- url     : https://prove2.me/submissions/88b59af6-1105-43ad-9a48-55719b42b90c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_discounted_all_pre_ruin_right_dividend_payment_jump_corrections_nonpositive
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact randomly clipped, filtered original physical-grid
right-payment correction is nonpositive, including its initial atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      ((Finset.range (k + 1)).image
        (fun i : ℕ => min
          ((i : ℝ≥0) * ((n : ℝ≥0) /
            ((k + 1 : ℕ) : ℝ≥0))) (ρ ω))).filter
          (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      if ρ ω = 0 then 0 else ∑ t ∈ A k ω,
        Real.exp (-(q * (t : ℝ))) *
          ((rightLimit D t ω - D t ω) -
            (w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω))))
    ∀ k ω, Q k ω ≤ 0 := by
  intro A Q k ω
  by_cases hz : ρ ω = 0
  · simp [Q, hz]
  · simp only [Q, if_neg hz]
    apply avram_b24_original_discounted_all_pre_ruin_right_dividend_payment_jump_corrections_nonpositive
      X x D q w hjump ω (A k ω)
    intro t ht
    rcases (Finset.mem_filter.mp ht).2 with hZero | hStrict
    · exact Or.inl hZero
    · exact Or.inr ((ENNReal.coe_lt_coe.mpr hStrict).trans_le (hρruin ω))
