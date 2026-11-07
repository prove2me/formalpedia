-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_compensated_H_signed_NX_integral_eq_physical_stopped_jump_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:00:55.950143+00:00
-- url     : https://prove2.me/submissions/e5c05189-7ada-48e8-aaa7-3d113a16a696

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_C1_signed_global_NX_real_eq_stopped_jump_series

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual P3 compensated H jump integral is the original stopped signed
    jump series, assuming precisely the original H source integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
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
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then K p else 0)
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    Integrable (fun p => H ((p.1, ω), p.2)) NX →
      (∫ p, H ((p.1, ω), p.2) ∂NX) =
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 (min T (τ ω)) then
            ENNReal.ofReal (J (v, Δ v)) else 0).toReal -
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 (min T (τ ω)) then
            ENNReal.ofReal (-J (v, Δ v)) else 0).toReal := by
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
  let J : ℝ≥0 × ℝ → ℝ := fun p =>
    (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
      (if p ∈ Eω then K p else 0)
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
      (fun v : ℝ≥0 => (v, Δ v)))
  have hEq : (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) = J := by
    funext p
    have hp :=
      (AvramDividend.Classical.avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
        X x D w q a b T ω p)
    simpa only [τ, E, G, H, Y, Eω, K, J, one_mul] using hp
  change Integrable (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) NX → _
  intro hInt
  have hIntJ : Integrable J NX := by simpa only [hEq] using hInt
  have hSeries :=
    (AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_signed_global_NX_real_eq_stopped_jump_series
      X x C D hD w hw_cont hw_neg q (1 : ℝ) a b T ω hIntJ)
  rw [hEq]
  simpa only [τ, Y, Eω, K, J, Δ, NX] using hSeries
