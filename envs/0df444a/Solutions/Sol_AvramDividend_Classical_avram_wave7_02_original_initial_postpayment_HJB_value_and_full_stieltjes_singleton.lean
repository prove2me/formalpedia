-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:58:12.741441+00:00
-- url     : https://prove2.me/submissions/738536e7-4cdc-4573-b76b-1aff8cfa6713

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The physical original time-zero lump sum satisfies its HJB value-drop
budget, even if ruin is instantaneous; the atom is exactly the Stieltjes
singleton and the postpayment state is retained at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) :
    w (x - rightLimit D 0 ω) + rightLimit D 0 ω ≤ w x ∧
    dividendMeasure D ω {(0 : ℝ)} =
      ENNReal.ofReal (rightLimit D 0 ω) ∧
    0 ≤ rightLimit D 0 ω := by
  have hJump := hjump ω 0 (Or.inl rfl)
  change rightLimit D 0 ω - D 0 ω ≤
    w (x + X.X 0 ω - D 0 ω) -
    w ((x + X.X 0 ω - D 0 ω) -
      (rightLimit D 0 ω - D 0 ω)) at hJump
  rw [X.X_zero ω, hD.1 ω] at hJump
  simp only [add_zero, sub_zero] at hJump
  have hMass : dividendMeasure D ω {(0 : ℝ)} =
      ENNReal.ofReal (rightLimit D 0 ω) := by
    simpa [hD.1 ω] using
      (dividendMeasure_singleton_eq_rightLimit_sub D hD ω (0 : ℝ≥0))
  have hPositive : 0 ≤ rightLimit D 0 ω := by
    have hlim := dividendStrategy_le_rightLimit D hD ω 0
    rw [hD.1 ω] at hlim
    exact hlim
  exact ⟨by linarith only [hJump], hMass, hPositive⟩
