-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_lipschitz_C1_exact_stopped_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:49:02.596149+00:00
-- url     : https://prove2.me/submissions/c88e3e11-a28c-415d-a98c-d7386cf8c5fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_compact_C1_global_NX_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_integrable_signed_C1_NX_eq_finite_physical_cell_jump_parts

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- All indexed original BV physical C1 signed jump sources agree with the
    genuine finite stopped grid on one common full-measure path event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
    (hLip : ∀ n, ∀ u ∈ Icc (a n / 2) (b n),
      ∀ v ∈ Icc (a n / 2) (b n),
      |w u - w v| ≤ L n * |u - v|)
    (hWbound : ∀ n, ∀ v : ℝ, v ≤ b n → |w v| ≤ R n) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ (T : ℝ≥0) (m : ℕ),
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
        {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
      let K : ℝ≥0 × ℝ → ℝ := fun p =>
        if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
      let G : ℝ≥0 × ℝ → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (G p)
      let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
        ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
          (if p ∈ E then K p else 0))
      (∫ p, G p ∂NX) =
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fp (v, Δ v) else 0).toReal -
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fm (v, Δ v) else 0).toReal := by
  apply MeasureTheory.ae_all_iff.mpr
  intro n
  filter_upwards
    [AvramDividend.Classical.avram_bv_cell7_original_BV_physical_compact_C1_global_NX_integrable
      X hBV x C D hD w hw_cont hw_neg q (a n) (b n) (L n) (R n)
        hq (ha n) (hab n) (hL n) (hR n) (hLip n) (hWbound n)]
    with ω hω
  intro T m
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
    {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
  let G : ℝ≥0 × ℝ → ℝ := fun p =>
    Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
  let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (G p)
  let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
      (if p ∈ E then K p else 0))
  have hInt : Integrable
      (fun p : ℝ≥0 × ℝ =>
        (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
          (if p ∈ E then K p else 0)) NX := by
    simpa only [one_mul] using (hω T)
  have hGrid :=
    AvramDividend.Classical.avram_bv_cell7_original_integrable_signed_C1_NX_eq_finite_physical_cell_jump_parts
      X x C D hD w hw_cont hw_neg q (1 : ℝ) (a n) (b n) T m ω hInt
  simpa only [τ, u, Y, Δ, NX, E, K, G, Fp, Fm, one_mul] using hGrid
