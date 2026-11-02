-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:24:21.10133+00:00
-- url     : https://prove2.me/submissions/e1e41ad0-3dd3-410c-9c06-28bf4a2705c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Weighted BV source-remainder partition sums are bounded directly
by the actual source drift-minus-process increment, with no residual
remaining on the right-hand side; useful for moment envelopes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
        (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ i : ℕ, |a i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i)))| ≤
          M * (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (u n) ω - X.X (u 0) ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound
      X hBV,
      avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV] with ω hweighted hsource
  obtain ⟨R, hRdef, hRmono, hbound⟩ := hweighted
  obtain ⟨Q, hQdef, hQmono, hinterval⟩ := hsource
  have hRQ : R = Q := by
    funext t
    exact (hRdef t).trans (hQdef t).symm
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro u hu n a M hM ha
  have htimes : u 0 ≤ u n := hu (Nat.zero_le n)
  have hsourceEq := hinterval (u 0) (u n) htimes
  rw [← hRQ] at hsourceEq
  have hjump :
      0 ≤ (∑' (v : ℝ≥0),
        if u 0 < v ∧ v ≤ u n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal :=
    ENNReal.toReal_nonneg
  calc
    |(Finset.range n).sum (fun i =>
        a i * (R (u (i + 1)) - R (u i)))| ≤
        M * (R (u n) - R (u 0)) :=
          hbound u hu n a M hM ha
    _ ≤ M * (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
        (X.X (u n) ω - X.X (u 0) ω)) := by
          apply mul_le_mul_of_nonneg_left _ hM
          linarith only [hsourceEq, hjump]
