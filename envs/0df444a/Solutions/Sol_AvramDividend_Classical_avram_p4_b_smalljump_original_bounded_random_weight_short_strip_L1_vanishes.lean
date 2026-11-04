-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_random_weight_short_strip_L1_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:21:02.139991+00:00
-- url     : https://prove2.me/submissions/e6151430-8246-4c0e-971c-d5252ff3fe63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_bounded_random_weight_short_strip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal

/-- Genuine random bounded coefficients on the original marked Lévy jumps
have vanishing L¹ cost over shrinking source time strips, conditional on
the actual source first-moment rate from P2. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (r : ℕ → ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (A : Set Ω)
    (H : ℕ → Ω → ℝ≥0∞) (K : ℝ≥0∞)
    (hBound : ∀ n ω, H n ω ≤ K)
    (hFinite : X.ν B ≠ ⊤) (hKFinite : K ≠ ⊤)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hRate : ∀ n, (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s (r n) ×ˢ B) ∂P) =
       ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    Tendsto (fun n => (∫⁻ ω in A, H n ω *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s (r n) ×ˢ B) ∂P)) atTop (𝓝 0) := by
  let J (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
     (fun u : ℝ≥0 => (u,
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     (Ioc s (r n) ×ˢ B)
  change Tendsto (fun n => (∫⁻ ω in A, H n ω * J n ω ∂P)) atTop (𝓝 0)
  have hCoe : Tendsto (fun n => ((r n - s : ℝ≥0) : ℝ≥0∞))
      atTop (𝓝 0) := (ENNReal.continuous_coe.tendsto 0).comp hShort
  have hSource : Tendsto
      (fun n => ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (ENNReal.Tendsto.mul_const hCoe (Or.inr hFinite))
  have hUpper : Tendsto
      (fun n => K * (((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B))
      atTop (𝓝 0) := by
    have h₁ : Tendsto
        (fun n => (((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B) * K)
        atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (ENNReal.Tendsto.mul_const hSource (Or.inr hKFinite))
    simpa only [mul_comm K] using h₁
  have hUpperBound (n : ℕ) :
      (∫⁻ ω in A, H n ω * J n ω ∂P) ≤
        K * (((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :=
    avram_p4_b_smalljump_original_marked_bounded_random_weight_short_strip
      X s (r n) B hB A (H n) K (hBound n) (hRate n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hUpper
    (fun n => (zero_le : (0 : ℝ≥0∞) ≤ (∫⁻ ω in A, H n ω * J n ω ∂P)))
    hUpperBound
