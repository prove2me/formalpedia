-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_integrable_signed_C1_NX_eq_finite_physical_cell_jump_parts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:00:51.916201+00:00
-- url     : https://prove2.me/submissions/0a2a6564-b5df-4a88-b09e-1498c8a91bb2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_unmasked_global_C1_signed_parts_eq_stopped_physical_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual integrable original global signed C1 jump term is a real
    difference of the two genuine finite stopped-grid nonlinear jump sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q c a b : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      c * Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
    let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (G p)
    let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal ((-c) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ E then K p else 0))
    Integrable G NX →
      (∫ p, G p ∂NX) =
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fp (v, Δ v) else 0).toReal -
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fm (v, Δ v) else 0).toReal := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
      (fun v : ℝ≥0 => (v, Δ v)))
  let E : Set (ℝ≥0 × ℝ) :=
    {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
  let G : ℝ≥0 × ℝ → ℝ := fun p =>
    c * Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
  let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (G p)
  let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((-c) * Real.exp (-(q * (p.1 : ℝ))) *
      (if p ∈ E then K p else 0))
  obtain ⟨_, _, _, hPlus⟩ :=
    (AvramDividend.Classical.avram_bv_cell7_original_unmasked_global_C1_signed_parts_eq_stopped_physical_grid
      X x C D hD w hw_cont hw_neg q c a b T m ω)
  obtain ⟨_, _, _, hMinus⟩ :=
    (AvramDividend.Classical.avram_bv_cell7_original_unmasked_global_C1_signed_parts_eq_stopped_physical_grid
      X x C D hD w hw_cont hw_neg q (-c) a b T m ω)
  have hGridP :
      (∫⁻ p, Fp p ∂NX) =
      ∑ i ∈ Finset.range (m + 1),
        ∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
            Fp (v, Δ v) else 0 := by
    simpa only [τ, u, Y, Δ, NX, E, K, Fp, G] using hPlus
  have hGridM :
      (∫⁻ p, Fm p ∂NX) =
      ∑ i ∈ Finset.range (m + 1),
        ∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
            Fm (v, Δ v) else 0 := by
    simpa only [τ, u, Y, Δ, NX, E, K, Fm] using hMinus
  have hNeg : (fun p : ℝ≥0 × ℝ => ENNReal.ofReal (-G p)) = Fm := by
    funext p
    change ENNReal.ofReal (-(c * Real.exp (-(q * (p.1 : ℝ))) *
      (if p ∈ E then K p else 0))) =
      ENNReal.ofReal ((-c) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ E then K p else 0))
    congr 1
    ring
  change Integrable G NX → _
  intro hInt
  have hIntegralNeg :
      (∫⁻ p, ENNReal.ofReal (-G p) ∂NX) = (∫⁻ p, Fm p ∂NX) :=
    congrArg (fun f : (ℝ≥0 × ℝ) → ℝ≥0∞ => ∫⁻ p, f p ∂NX) hNeg
  calc
    (∫ p, G p ∂NX) =
        (∫⁻ p, ENNReal.ofReal (G p) ∂NX).toReal -
        (∫⁻ p, ENNReal.ofReal (-G p) ∂NX).toReal :=
          MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt
    _ = (∫⁻ p, Fp p ∂NX).toReal - (∫⁻ p, Fm p ∂NX).toReal := by
      rw [hIntegralNeg]
    _ = _ := by rw [hGridP, hGridM]
