-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_finite_negative_band_partition_chronological_discounted_merge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:56:02.656454+00:00
-- url     : https://prove2.me/submissions/7f40aba6-4b4e-47f1-9219-d505669aa4cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

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
    (q : ℝ)
    (u v ζ : ℝ) (s t : ℝ≥0) (ω : Ω)
    (I : Finset ℕ) (B : ℕ → Set ℝ)
    (hBneg : ∀ i ∈ I, B i ⊆ Iio (0 : ℝ))
    (hBdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (S : ℕ → Finset ℝ≥0)
    (hS : ∀ i ∈ I, ∀ r : ℝ≥0, r ∈ S i ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B i) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
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
    let A : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        if Y r ∈ Icc (u + ζ) v then
          Real.exp (-(q * (r : ℝ))) *
            ((w (W r) - w (Function.leftLim
              (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
        else 0
      else 0
    let K : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        if Y r ∈ Icc (u + ζ) v then
          Real.exp (-(q * (r : ℝ))) *
            ((if -1 < J r then J r * deriv w (Y r) else 0) +
              SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
        else 0
      else 0
    (∑ r ∈ I.biUnion S, A r) =
        (∑ i ∈ I, ∑ r ∈ S i, A r) ∧
    (∑ r ∈ I.biUnion S, K r) =
        (∑ i ∈ I, ∑ r ∈ S i, K r) ∧
    (∑ r ∈ I.biUnion S, A r) ≤
        ∑ r ∈ I.biUnion S, K r := by
  dsimp only
  let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
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
  let A : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      if Y r ∈ Icc (u + ζ) v then
        Real.exp (-(q * (r : ℝ))) *
          ((w (W r) - w (Function.leftLim
            (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
      else 0
    else 0
  let K : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      if Y r ∈ Icc (u + ζ) v then
        Real.exp (-(q * (r : ℝ))) *
          ((if -1 < J r then J r * deriv w (Y r) else 0) +
            SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
      else 0
    else 0
  let BAll : Set ℝ := {z | ∃ i ∈ I, z ∈ B i}
  have hBAll : BAll ⊆ Iio (0 : ℝ) := by
    intro z hz
    rcases hz with ⟨i, hi, hz⟩
    exact hBneg i hi hz
  have hSdisj : ∀ i ∈ I, ∀ j ∈ I,
      i ≠ j → Disjoint (S i) (S j) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro r hri hrj
    exact Set.disjoint_left.mp (hBdisj i hi j hj hij)
      ((hS i hi r).mp hri).2.2 ((hS j hj r).mp hrj).2.2
  have hSall : ∀ r : ℝ≥0, r ∈ I.biUnion S ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ BAll := by
    intro r
    constructor
    · intro hr
      rcases Finset.mem_biUnion.mp hr with ⟨i, hi, hri⟩
      have h := (hS i hi r).mp hri
      exact ⟨h.1, h.2.1, ⟨i, hi, h.2.2⟩⟩
    · rintro ⟨hr, hrt, ⟨i, hi, hmark⟩⟩
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, (hS i hi r).mpr ⟨hr, hrt, hmark⟩⟩
  have hBound : (∑ r ∈ I.biUnion S, A r) ≤
      (∑ r ∈ I.biUnion S, K r) :=
    avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum
      X x D hD w hjump q u v ζ s t ω BAll hBAll
      (I.biUnion S) hSall
  exact ⟨Finset.sum_biUnion hSdisj,
    Finset.sum_biUnion hSdisj, hBound⟩
