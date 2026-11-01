-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_right_atom_hjump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:34:19.556416+00:00
-- url     : https://prove2.me/submissions/cb1ad363-2a5c-4f9c-a6ff-22d62775de07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option maxHeartbeats 1000000 in
/-- The actual chronological payment-jump secant bounds any weighted right-atom sum
on a finite horizon, assuming hjump only where the payoff weight is nonzero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞)
    (hjump : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∀ A : Set ℝ,
      (∑' s : A, μ {(s : ℝ)} * f (s : ℝ)) ≤
      (∑' s : A,
        ENNReal.ofReal
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
            w (riskProcess X x D (s : ℝ).toNNReal ω -
              (rightLimit D (s : ℝ).toNNReal ω -
                D (s : ℝ).toNNReal ω))) * f (s : ℝ)) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  intro A
  apply ENNReal.tsum_le_tsum
  intro s
  by_cases hs : (s : ℝ) ∈ Icc (0 : ℝ) (T : ℝ)
  · by_cases hf : f (s : ℝ) = 0
    · simp [hf]
    · have hcoe : ((s : ℝ).toNNReal : ℝ) = (s : ℝ) :=
        Real.coe_toNNReal (s : ℝ) hs.1
      have ht : (s : ℝ).toNNReal ≤ T := by
        exact_mod_cast (show (((s : ℝ).toNNReal : ℝ) ≤ (T : ℝ)) from by
          simpa only [hcoe] using hs.2)
      have hmass :
          μ {(s : ℝ)} =
            ENNReal.ofReal (rightLimit D (s : ℝ).toNNReal ω -
              D (s : ℝ).toNNReal ω) := by
        calc
          μ {(s : ℝ)} = (dividendMeasure D ω) {(s : ℝ)} := by
            simp [μ, hs]
          _ = ENNReal.ofReal (rightLimit D (s : ℝ).toNNReal ω -
                D (s : ℝ).toNNReal ω) := by
            simpa only [hcoe] using
              (dividendMeasure_singleton_eq_rightLimit_sub
                D hD ω (s : ℝ).toNNReal)
      have hle :
          μ {(s : ℝ)} ≤
            ENNReal.ofReal
              (w (riskProcess X x D (s : ℝ).toNNReal ω) -
               w (riskProcess X x D (s : ℝ).toNNReal ω -
                 (rightLimit D (s : ℝ).toNNReal ω -
                   D (s : ℝ).toNNReal ω))) := by
        rw [hmass]
        exact ENNReal.ofReal_le_ofReal
          (hjump (s : ℝ).toNNReal ht (by simpa only [hcoe] using hf))
      exact mul_le_mul_of_nonneg_right hle (by positivity)
  · have hzero : μ {(s : ℝ)} = 0 := by
      simp [μ, hs]
    change μ {(s : ℝ)} * f (s : ℝ) ≤ _
    simp [hzero]
