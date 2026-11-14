-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_compensated_bounded_simple_mark_ae_limit_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:15:27.981258+00:00
-- url     : https://prove2.me/submissions/8c20ec9a-2b67-4788-983e-11df6fdf8018

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_simple_integral_L2_domination_convergence
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_Borel_mark_first_second_integral_limits
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Physical bounded finite-range marked integrals and their actual source
compensators converge together on the original probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (v : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1)
    (hLimit : ∀ z ∈ S, Tendsto (fun k => f k z) atTop (𝓝 (v z))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)))
    let Z : ℕ → Ω → ℝ := fun k ω =>
      (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, f k z ∂X.ν)
    let C : Ω → ℝ := fun ω =>
      (∫ p in (Ioc 0 T ×ˢ S), v p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, v z ∂X.ν)
    ∀ᵐ ω ∂P, Tendsto (fun k => Z k ω) atTop (𝓝 (C ω)) := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)))
  let Z : ℕ → Ω → ℝ := fun k ω =>
    (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
      (T : ℝ) * (∫ z in S, f k z ∂X.ν)
  let C : Ω → ℝ := fun ω =>
    (∫ p in (Ioc 0 T ×ˢ S), v p.2 ∂NX ω) -
      (T : ℝ) * (∫ z in S, v z ∂X.ν)
  have hRaw := avram_a21_original_bounded_simple_integral_L2_domination_convergence
    X hFinite T S hS hNeg v f hBound hLimit
  have hRawLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => ∫ p in (Ioc 0 T ×ˢ S),
        f k p.2 ∂NX ω) atTop
        (𝓝 (∫ p in (Ioc 0 T ×ˢ S), v p.2 ∂NX ω)) :=
    hRaw.2.2.2
  have hMass : X.ν S < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg)
      (lt_top_iff_ne_top.mpr hFinite)
  have hMean := avram_a20_bounded_Borel_mark_first_second_integral_limits
    X.ν S hS hMass v f hBound hLimit
  have hMeanLim : Tendsto
      (fun k => (T : ℝ) * (∫ z in S, f k z ∂X.ν)) atTop
      (𝓝 ((T : ℝ) * (∫ z in S, v z ∂X.ν))) :=
    tendsto_const_nhds.mul hMean.1
  filter_upwards [hRawLim] with ω hω
  change Tendsto
    (fun k => (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
      (T : ℝ) * (∫ z in S, f k z ∂X.ν)) atTop
    (𝓝 ((∫ p in (Ioc 0 T ×ˢ S), v p.2 ∂NX ω) -
      (T : ℝ) * (∫ z in S, v z ∂X.ν)))
  exact hω.sub hMeanLim
