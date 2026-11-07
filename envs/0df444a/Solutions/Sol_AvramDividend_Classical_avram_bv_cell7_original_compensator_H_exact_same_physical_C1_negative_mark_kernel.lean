-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:54:28.942708+00:00
-- url     : https://prove2.me/submissions/5d57ee4a-8a9c-4573-a659-a2d4c19c9450

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensated_H_kernel_eq_physical_C1_marked_source

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact H kernel inside the original P3 compensated-source theorem
    agrees pointwise on each sample path with the original physical C1 source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : Ω → ℝ≥0 := fun η =>
      (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Eω : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    ∀ p : ℝ≥0 × ℝ,
      H ((p.1, ω), p.2) =
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ Eω then K p else 0) := by
  let τ : Ω → ℝ≥0 := fun η =>
    (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
  let E : Set (ℝ≥0 × Ω) := {p |
    (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
          p.1.1 + p.2) -
         w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
          p.1.1))
    else 0
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
  let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let Eω : Set (ℝ≥0 × ℝ) :=
    {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
  have hComp : ∀ p : ℝ≥0 × ℝ,
      H ((p.1, ω), p.2) =
      (if p ∈ Eω then Real.exp (-(q * (p.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1)) else 0) := by
    intro p
    change
      (if (p.1 : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) then
        (if ((p.1, ω) ∈ E ∧ p.2 < 0) then
          Real.exp (-(q * (p.1 : ℝ))) *
            (w (Y p.1 + p.2) - w (Y p.1)) else 0)
        else 0) =
      (if p ∈ Eω then Real.exp (-(q * (p.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1)) else 0)
    have hequiv : ((p.1, ω) ∈ E ∧ p.2 < 0) ↔ p ∈ Eω := by
      change (((p.1 : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) ∧
        Y p.1 ∈ Icc a b) ∧ p.2 < 0) ↔
        (p.1 ≤ τ ω ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0)
      constructor
      · rintro ⟨⟨ht, hb⟩, hz⟩
        have hnn : p.1 ≤ τ ω := by exact_mod_cast ht
        exact ⟨hnn, hb, hz⟩
      · rintro ⟨ht, hb, hz⟩
        have henn : (p.1 : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by
          exact_mod_cast ht
        exact ⟨⟨henn, hb⟩, hz⟩
    by_cases hp : p ∈ Eω
    · have ht : (p.1 : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by
        exact_mod_cast hp.1
      have hPair : ((p.1, ω) ∈ E ∧ p.2 < 0) := hequiv.mpr hp
      simp only [if_pos ht, if_pos hPair, if_pos hp]
    · by_cases ht : (p.1 : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞)
      · have hPair : ¬((p.1, ω) ∈ E ∧ p.2 < 0) :=
          fun h => hp (hequiv.mp h)
        simp only [if_pos ht, if_neg hPair, if_neg hp]
      · simp only [if_neg ht, if_neg hp]
  have hClip : ∀ p : ℝ≥0 × ℝ,
      (if p ∈ Eω then Real.exp (-(q * (p.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1)) else 0) =
      Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ Eω then K p else 0) := by
    simpa only [τ, Y, Eω, K] using
      (AvramDividend.Classical.avram_bv_cell7_original_compensated_H_kernel_eq_physical_C1_marked_source
        X x D w q a b T ω)
  exact fun p => (hComp p).trans (hClip p)
