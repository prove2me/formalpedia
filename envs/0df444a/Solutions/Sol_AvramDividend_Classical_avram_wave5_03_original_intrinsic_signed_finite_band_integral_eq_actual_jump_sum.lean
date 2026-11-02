-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:07:16.970208+00:00
-- url     : https://prove2.me/submissions/83350c30-20bc-4998-ad39-81047aba0b2a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (B : Set ℝ) (hBmeas : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔
      s < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B)
    (f : (ℝ≥0 × ℝ) → ℝ) (hf : Measurable f)
    (hfin : Integrable
      (fun p : ℝ≥0 × ℝ =>
        if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then f p else 0)
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    (∫ p, (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then f p else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ u ∈ S, f (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let F : (ℝ≥0 × ℝ) → ℝ := fun p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then f p else 0
  have htimeL : MeasurableSet {p : ℝ≥0 × ℝ | s < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have htimeR : MeasurableSet {p : ℝ≥0 × ℝ | p.1 ≤ t} :=
    measurableSet_le measurable_fst measurable_const
  have hmark : MeasurableSet {p : ℝ≥0 × ℝ | p.2 ∈ B} :=
    hBmeas.preimage measurable_snd
  have hband : MeasurableSet
      {p : ℝ≥0 × ℝ | s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B} :=
    htimeL.inter (htimeR.inter hmark)
  have hF : Measurable F :=
    Measurable.ite hband hf measurable_const
  have hsource :=
    avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
      X ω F hF hfin
  change (∫ p, F p ∂
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u)))) =
    ∑ u ∈ S, f (u, j u)
  rw [hsource]
  have hoff : ∀ u : ℝ≥0, u ∉ S →
      (if 0 < u ∧ j u ≠ 0 then F (u, j u) else 0) = 0 := by
    intro u hu
    by_cases hactual : 0 < u ∧ j u ≠ 0
    · have hnotband : ¬ (s < u ∧ u ≤ t ∧ j u ∈ B) := by
        intro hbandU
        exact hu ((hS u).mpr hbandU)
      simp [F, hactual, hnotband]
    · simp [hactual]
  rw [tsum_eq_sum hoff]
  apply Finset.sum_congr rfl
  intro u hu
  have hbandU : s < u ∧ u ≤ t ∧ j u ∈ B :=
    (hS u).mp hu
  have hpos : 0 < u :=
    lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hbandU.1
  have hjne : j u ≠ 0 := ne_of_lt (hBneg hbandU.2.2)
  have hactual : 0 < u ∧ j u ≠ 0 := ⟨hpos, hjne⟩
  simp [F, hactual, hbandU]
