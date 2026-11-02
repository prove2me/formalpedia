-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_future_marked_event_measure_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:16:17.845967+00:00
-- url     : https://prove2.me/submissions/7cff7f19-3195-45b2-a2c2-cca7e55efc61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_jump_count_is_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ Q : Measure Ω,
      Q Set.univ < ⊤ ∧
      ∀ A : Set Ω, MeasurableSet A →
        Q A = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hC : MeasurableSet (Ioc s t ×ˢ B) :=
    measurableSet_Ioc.prod hB
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_event_weighted_jump_count_is_measure
      X (Ioc s t ×ˢ B) hC
  have hSub :
      (Ioc s t ×ˢ B) ⊆
        (Ioc s t ×ˢ (Set.univ : Set ℝ)) := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  have hBound :
      (∫⁻ ω, NX ω (Ioc s t ×ˢ B) ∂P) ≤
        (∫⁻ ω, NX ω (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) := by
    apply lintegral_mono
    intro ω
    exact measure_mono hSub
  have hRate :
      (∫⁻ ω, NX ω (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) :=
    avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
      X hBV hFinite s t hst
  have hMass : Q Set.univ < ⊤ := by
    have hh := hQ Set.univ MeasurableSet.univ
    change Q Set.univ =
      ∫⁻ ω in Set.univ, NX ω (Ioc s t ×ˢ B) ∂P at hh
    simp only [Measure.restrict_univ] at hh
    rw [hh]
    exact lt_of_le_of_lt (hBound.trans_eq hRate)
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hFinite)
  refine ⟨Q, hMass, ?_⟩
  intro A hA
  exact hQ A hA
