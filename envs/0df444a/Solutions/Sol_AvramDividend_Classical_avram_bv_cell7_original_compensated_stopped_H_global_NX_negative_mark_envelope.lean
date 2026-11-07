-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_compensated_stopped_H_global_NX_negative_mark_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:06:18.847828+00:00
-- url     : https://prove2.me/submissions/63f00f9f-675a-4129-9f08-dd747a3f688b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original indexed compensated H source is dominated pointwise
    by the magnitude of that same negative Lévy mark. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q a b L R : ℝ) (hq : 0 ≤ q) (ha : 0 < a)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (T : ℝ≥0) (ω : Ω) :
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
    ∀ p : ℝ≥0 × ℝ,
      |H ((p.1, ω), p.2)| ≤ (L + 4 * R / a) * max (-p.2) 0 := by
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
  have hExact : ∀ p : ℝ≥0 × ℝ,
      H ((p.1, ω), p.2) =
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ Eω then K p else 0) :=
    AvramDividend.Classical.avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
      X x D w q a b T ω
  have hCoeff : 0 ≤ L + 4 * R / a := by
    exact add_nonneg hL (div_nonneg (by nlinarith [hR]) (le_of_lt ha))
  change ∀ p : ℝ≥0 × ℝ,
    |H ((p.1, ω), p.2)| ≤ (L + 4 * R / a) * max (-p.2) 0
  intro p
  rw [hExact p]
  by_cases hp : p ∈ Eω
  · have hstate : Y p.1 ∈ Icc a b := hp.2.1
    have hmark : p.2 < 0 := hp.2.2
    have htime : p.1 ≤ T := by
      have hτ : τ ω ≤ T := by
        have hrfinite : min (ruinTime X x D ω) (T : ℝ≥0∞) < ⊤ :=
          lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top
        have hco : (((τ ω : ℝ≥0) : ℝ≥0∞)) =
            min (ruinTime X x D ω) (T : ℝ≥0∞) :=
          ENNReal.coe_toNNReal (ne_of_lt hrfinite)
        have hle : (τ ω : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
          rw [hco]
          exact min_le_right _ _
        exact_mod_cast hle
      exact hp.1.trans hτ
    simp only [if_pos hp, K, if_pos htime, max_eq_left (le_of_lt (neg_pos.mpr hmark))]
    exact AvramDividend.Classical.avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope
      w a b L R ha hab hL hR hLip hWbound q hq p.1 (Y p.1) p.2 hstate hmark
  · simp only [if_neg hp, mul_zero, abs_zero]
    exact mul_nonneg hCoeff (le_max_right _ _)
