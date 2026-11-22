-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_variable_negative_simplemark_interval_compensated_L1_allactivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:20:57.274631+00:00
-- url     : https://prove2.me/submissions/23fea0f3-696f-48c7-9335-85a5cc136809

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤)
    (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    Integrable (fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal)) P  := by
  classical
  intro NX B
  apply integrable_finset_sum
  intro y hy
  have hBm : MeasurableSet (B y) :=
    hS.inter (g.measurable (measurableSet_singleton y))
  have hBn : B y ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact hNeg hz.1
  have hBν : X.ν (B y) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hν
  have hCell :=
    avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
      X s t hst (B y) hBm hBν hBn
  simpa only [NX, B] using hCell.1.const_mul y
