-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:42:12.306232+00:00
-- url     : https://prove2.me/submissions/27c7c46e-0999-4c7a-abf0-04759e94cd90

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The exact source stopped nonlinear band balance, with finite source jump
support constructed for every BV or UBV Lévy path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    ∃ T : Finset ℝ≥0,
      (∀ q : ℝ≥0, q ∈ T ↔
        s < q ∧ q ≤ t ∧
          X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q ∈ B) ∧
      (let Y : ℝ≥0 → ℝ := fun q => Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) q
       let J : ℝ≥0 → ℝ := fun q =>
          X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
       (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y q ∈ Icc (u + δ) v then
           w (riskProcess X x D q ω) -
             w (Function.leftLim
               (fun r : ℝ≥0 => riskProcess X x D r ω) q)
           else 0) else 0) =
       (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if -1 < J q then
           J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
           else 0) +
         (if Y q ∈ Icc (u + δ) v then
           SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
           else 0) else 0)) := by
  let S : Set ℝ≥0 := {q | s < q ∧ q ≤ t ∧
    X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q ∈ B}
  have hAll : {q : ℝ≥0 |
      0 < q ∧ q ≤ t ∧
      ε ≤ dist (X.X q ω -
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) q) 0}.Finite :=
    avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
      X ω t ε hε
  have hFinite : S.Finite := by
    apply hAll.subset
    intro q hq
    rcases hq with ⟨hqs, hqt, hqB⟩
    have hqpos : (0 : ℝ≥0) < q :=
      lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hqs
    exact ⟨hqpos, hqt, hBsep _ hqB⟩
  have hT : ∀ q : ℝ≥0, q ∈ hFinite.toFinset ↔
      s < q ∧ q ≤ t ∧
        X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q ∈ B := by
    intro q
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, S]
  refine ⟨hFinite.toFinset, hT, ?_⟩
  exact avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance
    X x D hD w u v δ s t ω B hBneg hFinite.toFinset hT
