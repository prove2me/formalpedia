-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_local_simple_mark_fibre_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:13:32.77172+00:00
-- url     : https://prove2.me/submissions/59d8c34b-4f7c-47a7-8735-a672a07ab638

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_real_simple_mark_integral_partition_exact
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSep : S ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    ∀ ω, (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) =
      ∑ y ∈ g.range, y *
        (NX ω (Ioc 0 T ×ˢ B y)).toReal  := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
  change ∀ ω, (∫ p in Ioc 0 T ×ˢ S, g p.2 ∂NX ω) =
    ∑ y ∈ g.range, y * (NX ω (Ioc 0 T ×ˢ B y)).toReal
  intro ω
  have hSub : Ioc (0 : ℝ≥0) T ×ˢ S ⊆
      Ioc (0 : ℝ≥0) T ×ˢ Iic (-(1 / ((n : ℝ) + 1))) :=
    Set.prod_mono Subset.rfl hSep
  have hCount :=
    avram_wave7_06_original_separated_negative_band_count_finite_every_path
      X ω T n
  have hMass : NX ω (Ioc 0 T ×ˢ S) < ⊤ :=
    lt_of_le_of_lt (measure_mono hSub) (by simpa only [NX] using hCount)
  have hInt :=
    (avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
      (NX ω) T S hS (fun z => g z) g.measurable hMass hBound).1
  simpa only [B] using
    (avram_a20_real_simple_mark_integral_partition_exact
      (NX ω) T S hS g hInt)
