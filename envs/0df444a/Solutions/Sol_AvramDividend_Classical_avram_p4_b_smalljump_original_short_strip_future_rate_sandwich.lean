-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_short_strip_future_rate_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:47:53.938533+00:00
-- url     : https://prove2.me/submissions/f2c2a4ff-2b03-4a9a-8d3b-3f68f3d1d61a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_event_interval_lintegral_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

/-- A sharp eventwise sandwich for original-source intrinsic Lévy jump
counts: the only discrepancy between the full window and a later raw
predictable window is the negligible-in-L1 initial marked strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r t : ℝ≥0) (hsr : s ≤ r) (hrt : r ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω = ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hRate : (∫⁻ ω, J s r ω ∂P) =
      ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hFuture : (∫⁻ ω in A, J r t ω ∂P) =
      P A * ((t - r : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    P A * ((t - r : ℝ≥0) : ℝ≥0∞) * X.ν B ≤
      (∫⁻ ω in A, J s t ω ∂P) ∧
    (∫⁻ ω in A, J s t ω ∂P) ≤
      ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B +
        P A * ((t - r : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hSplit :
      (∫⁻ ω in A, J s t ω ∂P) =
        (∫⁻ ω in A, J s r ω ∂P) +
          (∫⁻ ω in A, J r t ω ∂P) := by
    simp_rw [hJsource]
    exact avram_p4_b_smalljump_original_marked_event_interval_lintegral_split
      X s r t hsr hrt B hB A
  have hSmall :
      (∫⁻ ω in A, J s r ω ∂P) ≤
        ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    calc
      (∫⁻ ω in A, J s r ω ∂P) ≤
          (∫⁻ ω, J s r ω ∂P) := by
        simpa using
          (lintegral_mono_set (Set.subset_univ A) :
            (∫⁻ ω in A, J s r ω ∂P) ≤
              (∫⁻ ω in Set.univ, J s r ω ∂P))
      _ = ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B := hRate
  constructor
  · rw [hSplit, hFuture]
    exact le_add_of_nonneg_left (zero_le : (0 : ℝ≥0∞) ≤ (∫⁻ ω in A, J s r ω ∂P))
  · rw [hSplit, hFuture]
    exact add_le_add hSmall le_rfl
