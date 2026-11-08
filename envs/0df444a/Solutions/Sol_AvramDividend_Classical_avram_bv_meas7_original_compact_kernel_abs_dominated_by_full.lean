-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_compact_kernel_abs_dominated_by_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:05:39.369503+00:00
-- url     : https://prove2.me/submissions/62800691-5209-4e02-9b66-a534c4dc906d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (w : ℝ → ℝ) (q : ℝ) (S : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun r =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
    ∀ (p : ℝ≥0 × Ω) (z : ℝ),
      |(if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Z p ∈ Icc a b ∧ z < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
        else 0)| ≤
      |(if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C ∧ z < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
        else 0)| := by
  classical
  dsimp only
  intro p z
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
  let Z : ℝ≥0 × Ω → ℝ := fun r =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
  change
    |(if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Z p ∈ Icc a b ∧ z < 0 then
      Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
      else 0)| ≤
    |(if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      0 < Z p ∧ ENNReal.ofReal (Z p) < C ∧ z < 0 then
      Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
      else 0)|
  by_cases hCompact : (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Z p ∈ Icc a b ∧ z < 0
  · rcases hCompact with ⟨hClock, hReserve, hMark⟩
    have hHalf : a / 2 ≤ a := by linarith [ha]
    obtain ⟨hPos, hCap⟩ := hBand
      (show Z p ∈ Icc (a / 2) b from
        ⟨le_trans hHalf hReserve.1, hReserve.2⟩)
    have hCompactAgain :
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Z p ∈ Icc a b ∧ z < 0 :=
      ⟨hClock, hReserve, hMark⟩
    have hFull : (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C ∧ z < 0 :=
      ⟨hClock, hPos, hCap, hMark⟩
    simp only [if_pos hCompactAgain, if_pos hFull, le_refl]
  · simp only [if_neg hCompact, abs_zero]
    exact abs_nonneg _
