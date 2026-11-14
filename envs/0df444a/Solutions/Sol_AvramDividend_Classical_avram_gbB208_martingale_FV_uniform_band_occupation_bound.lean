-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB208_martingale_FV_uniform_band_occupation_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:09:42.42909+00:00
-- url     : https://prove2.me/submissions/78adf76d-baec-48e0-ad55-e01ab9ddb429
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB227_martingale_FV_locally_bounded_spatial_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Small-ball rate from a pathwise uniform open-interval occupation bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (Xsrc : ℝ≥0 → Ω → ℝ) (c σ : ℝ) (hσ : 0 < σ)
    (hM : Martingale (fun t ω =>
      Xsrc t ω - (t : ℝ) * c) 𝓕 P)
    (hQ : Martingale (fun t ω =>
      (Xsrc t ω - (t : ℝ) * c) ^ 2 -
      (t : ℝ) * σ ^ 2) 𝓕 P)
    (hContinuous : ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ≥0 => Xsrc t ω))
    (Dsrc : ℝ≥0 → Ω → ℝ)
    (hFV : ∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => Dsrc t ω) Set.univ)
    (x b : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0, ∀ k : ℕ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + Xsrc (Real.toNNReal t) ω -
          Dsrc (Real.toNNReal t) ω - b) <
          (1 : ℝ) / ((k : ℝ) + 1)} ≤
      ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)) := by
  have hOccupation :=
    avram_gbB227_martingale_FV_locally_bounded_spatial_occupation
      Xsrc c σ hσ hM hQ hContinuous Dsrc hFV x n ρ
  filter_upwards [hOccupation] with ω hω
  obtain ⟨L, hL⟩ := hω
  refine ⟨2 * L, ?_⟩
  intro k
  let ε : ℝ := (1 : ℝ) / ((k : ℝ) + 1)
  let f : ℝ → ℝ := fun t =>
    x + Xsrc (Real.toNNReal t) ω - Dsrc (Real.toNNReal t) ω
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hSet :
      {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        |f t - b| < ε} =
      {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        f t ∈ Set.Ioo (b - ε) (b + ε)} := by
    ext t
    constructor
    · rintro ⟨ht0, htn, htr, hab⟩
      obtain ⟨hl, hr⟩ := abs_lt.mp hab
      refine ⟨ht0, htn, htr, ?_⟩
      change b - ε < f t ∧ f t < b + ε
      constructor <;> linarith
    · rintro ⟨ht0, htn, htr, hab⟩
      obtain ⟨hl, hr⟩ := hab
      refine ⟨ht0, htn, htr, abs_lt.mpr ?_⟩
      constructor <;> linarith
  have hReal :
      (L : ℝ) * ((b + ε) - (b - ε)) =
        (((2 * L : ℝ≥0) : ℝ) / ((k : ℝ) + 1)) := by
    dsimp [ε]
    push_cast
    ring
  change
    volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
      |f t - b| < ε} ≤
    ENNReal.ofReal (((2 * L : ℝ≥0) : ℝ) / ((k : ℝ) + 1))
  calc
    volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
      |f t - b| < ε} =
        volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          f t ∈ Set.Ioo (b - ε) (b + ε)} :=
          congrArg volume hSet
    _ ≤ ENNReal.ofReal ((L : ℝ) * ((b + ε) - (b - ε))) := by
      simpa only [f] using hL (b - ε) (b + ε)
    _ = _ := congrArg ENNReal.ofReal hReal
