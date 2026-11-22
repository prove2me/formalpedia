-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_simple_signed_mark_predictable_weight_condExp_zero_allactivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:58:57.955939+00:00
-- url     : https://prove2.me/submissions/57d18760-e0b8-4c36-abc1-c4443260539a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s < t)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤) (g : SimpleFunc ℝ ℝ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let G : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal)
    Integrable (fun ω => H ω * G ω) P →
      (P[(fun ω => H ω * G ω) | 𝓕.rightCont s] =ᵐ[P]
        (fun _ => (0 : ℝ)))  := by
  classical
  intro NX B G hHI
  have hGI : Integrable G P := by
    change Integrable (fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal)) P
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
        X s t hst.le (B y) hBm hBν hBn
    simpa only [NX, B] using hCell.1.const_mul y
  have hZero :=
    avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
      X s t hst S hS hν g
  have hPull : (P[(fun ω => H ω * G ω) | 𝓕.rightCont s] =ᵐ[P]
      (fun ω => H ω * (P[G | 𝓕.rightCont s]) ω)) :=
    condExp_mul_of_stronglyMeasurable_left hH hHI hGI
  filter_upwards [hPull, hZero] with ω hP hZ
  change (P[(fun ω => H ω * G ω) | 𝓕.rightCont s]) ω = 0
  rw [hP]
  have hZ' : (P[G | 𝓕.rightCont s]) ω = 0 := hZ
  rw [hZ']
  simp
