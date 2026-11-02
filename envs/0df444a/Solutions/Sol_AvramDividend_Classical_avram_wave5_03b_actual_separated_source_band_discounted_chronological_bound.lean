-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_separated_source_band_discounted_chronological_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:49:20.678318+00:00
-- url     : https://prove2.me/submissions/76a72703-0feb-4807-84d6-b57fc173520e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The genuine source/dividend chronological discounted band inequality; the
finite set of original BV/UBV source jumps is constructed pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (u v ζ : ℝ) (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    ∃ S : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ S ↔
        s < r ∧ r ≤ t ∧
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) ∧
      (let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
          (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
       let J : ℝ≥0 → ℝ := fun r =>
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
       let W : ℝ≥0 → ℝ := fun r =>
          if (r : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X r ω - rightLimit D r ω
          else riskProcess X x D r ω
       let cash : ℝ≥0 → ℝ := fun r =>
          if (r : ℝ≥0∞) < ruinTime X x D ω then
            rightLimit D r ω - D r ω else 0
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y r ∈ Icc (u + ζ) v then
           Real.exp (-(q * (r : ℝ))) *
           ((w (W r) - w (Function.leftLim
             (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
          else 0) else 0) ≤
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y r ∈ Icc (u + ζ) v then
           Real.exp (-(q * (r : ℝ))) *
             ((if -1 < J r then J r * deriv w (Y r) else 0) +
              SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
          else 0) else 0)) := by
  let A : Set ℝ≥0 := {r | s < r ∧ r ≤ t ∧
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B}
  have hLarge : {r : ℝ≥0 |
      0 < r ∧ r ≤ t ∧
      ε ≤ dist (X.X r ω -
        Function.leftLim (fun a : ℝ≥0 => X.X a ω) r) 0}.Finite :=
    avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
      X ω t ε hε
  have hA : A.Finite := by
    apply hLarge.subset
    intro r hr
    rcases hr with ⟨hrs, hrt, hrB⟩
    have hrpos : (0 : ℝ≥0) < r :=
      lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hrs
    exact ⟨hrpos, hrt, hBsep _ hrB⟩
  have hS : ∀ r : ℝ≥0, r ∈ hA.toFinset ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B := by
    intro r
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, A]
  refine ⟨hA.toFinset, hS, ?_⟩
  exact avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum
    X x D hD w hjump q u v ζ s t ω B hBneg hA.toFinset hS
