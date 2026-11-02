-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_joint_source_reserve_partition_variation_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:40:02.293025+00:00
-- url     : https://prove2.me/submissions/9f15c33c-7de5-4c18-9233-cb61510f6bd7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_partition_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Source-residual plus true controlled-reserve variation is bounded by
observable original-source drift and increments and chronological dividends;
the event is uniform over every finite ordered partition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (Finset.range n).sum (fun i =>
          |R (u (i + 1)) - R (u i)|) +
        (Finset.range n).sum (fun i =>
          |riskProcess X x D (u (i + 1)) ω -
            riskProcess X x D (u i) ω|) ≤
        (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
          (X.X (u n) ω - X.X (u 0) ω)) +
        (2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
          (X.X (u n) ω - X.X (u 0) ω) +
          (D (u n) ω - D (u 0) ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
      X hBV,
      avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV,
      avram_wave3_03_bv_controlled_reserve_partition_variation
      X hX hBV x D hD] with ω hvariation hsource hcontrolled
  obtain ⟨R, hRdef, hRmono, hvar⟩ := hvariation
  obtain ⟨Q, hQdef, hQmono, hinterval⟩ := hsource
  have hRQ : R = Q := by
    funext t
    exact (hRdef t).trans (hQdef t).symm
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro u hu n
  have htimes : u 0 ≤ u n := hu (Nat.zero_le n)
  have hsourceEq := hinterval (u 0) (u n) htimes
  rw [← hRQ] at hsourceEq
  have hjump :
      0 ≤ (∑' (v : ℝ≥0),
        if u 0 < v ∧ v ≤ u n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal := ENNReal.toReal_nonneg
  have hvarR := hvar u hu n
  have hvarY := hcontrolled u hu n
  linarith only [hvarR, hvarY, hsourceEq, hjump]
