-- Prove2me | solution 1 for AvramDividend.Classical.avram_a83_original_fullnegative_void_measure_limit_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:16:36.729317+00:00
-- url     : https://prove2.me/submissions/8e127370-fa27-4973-8081-1c14e3aa5f45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_zero_count_law
import Theorems.Thm_AvramDividend_Classical_avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0})
      atTop (𝓝 (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0})) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let B : ℕ → Set ℝ := fun n => Iic (-(1 / ((n : ℝ) + 1)))
  let E : ℕ → Set Ω := fun n => {ω | NX ω (Ioc 0 T ×ˢ B n) = 0}
  let A : Set Ω := {ω | NX ω (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0}
  have hBm (n : ℕ) : MeasurableSet (B n) := measurableSet_Iic
  have hBmono : Monotone B := by
    intro n m hnm
    apply Iic_subset_Iic.mpr
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hh : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact neg_le_neg (one_div_le_one_div_of_le hn hh)
  have hBunion : (⋃ n : ℕ, B n) = Iio (0 : ℝ) := by
    simpa only [B] using
      avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks
  have hBsub (n : ℕ) : B n ⊆ Iio (0 : ℝ) :=
    hBunion ▸ subset_iUnion B n
  have hEm (n : ℕ) : MeasurableSet (E n) := by
    have hCount :=
      avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X 0 T (by positivity : 0 ≤ T) (B n) (hBm n)
    exact (measurableSet_singleton (0 : ℝ≥0∞)).preimage hCount
  have hEanti : Antitone E := by
    intro n m hnm ω hω
    have hs : Ioc 0 T ×ˢ B n ⊆ Ioc 0 T ×ˢ B m :=
      Set.prod_mono Subset.rfl (hBmono hnm)
    have h := measure_mono hs (μ := NX ω)
    exact le_zero_iff.mp (h.trans_eq hω)
  have hEeq : A = ⋂ n : ℕ, E n := by
    ext ω
    constructor
    · intro hw
      apply mem_iInter.mpr
      intro n
      have hs : Ioc 0 T ×ˢ B n ⊆ Ioc 0 T ×ˢ Iio (0 : ℝ) :=
        Set.prod_mono Subset.rfl (hBsub n)
      exact le_zero_iff.mp
        ((measure_mono hs (μ := NX ω)).trans_eq hw)
    · intro hall
      have hlim :=
        avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
          (NX ω) T
      have he : (fun n : ℕ => NX ω (Ioc 0 T ×ˢ B n)) =
          (fun _ => (0 : ℝ≥0∞)) := by
        funext n
        exact (mem_iInter.mp hall) n
      exact tendsto_nhds_unique hlim (by
        rw [he]
        exact tendsto_const_nhds)
  have hPlim : Tendsto (fun n : ℕ => P (E n)) atTop (𝓝 (P A)) := by
    have h :=
      tendsto_measure_iInter_atTop (μ := P) (s := E)
        (fun n => (hEm n).nullMeasurableSet) hEanti
        ⟨0, measure_ne_top _ _⟩
    rw [← hEeq] at h
    simpa only [Function.comp_def] using h
  simpa only [E, A, B, NX] using hPlim
