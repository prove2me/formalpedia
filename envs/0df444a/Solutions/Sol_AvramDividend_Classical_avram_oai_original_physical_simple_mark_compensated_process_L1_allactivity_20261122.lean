-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_simple_mark_compensated_process_L1_allactivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:02:28.257388+00:00
-- url     : https://prove2.me/submissions/78fdd5be-9ca9-4ce7-9ee5-563bf2093ed9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S)
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
        ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
          (((t : ℝ≥0∞) * X.ν (B y))).toReal)) P  := by
  classical
  intro NX B
  apply integrable_finset_sum
  intro y hy
  have hBm : MeasurableSet (B y) :=
    hS.inter (g.measurable (measurableSet_singleton y))
  have hBν : X.ν (B y) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hν
  have hBn : B y ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact hNeg hz.1
  have hI :=
    avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
      X 0 t (by exact zero_le) (B y) hBm hBν hBn
  simpa only [NX, B, tsub_zero] using hI.1.const_mul y
