-- Prove2me | solution 1 for AvramDividend.Classical.avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:15:52.801633+00:00
-- url     : https://prove2.me/submissions/1a8d9789-397b-4a74-ac4d-00a4b057a86a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_zero_count_law
import Theorems.Thm_AvramDividend_Classical_avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_a83_original_fullnegative_void_measure_limit_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T : ℝ≥0) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by
  have hProb :=
    avram_a83_original_fullnegative_void_measure_limit_20261114 X T
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
  have hνlim : Tendsto (fun n : ℕ => X.ν (B n))
      atTop (𝓝 (X.ν (Iio (0 : ℝ)))) := by
    have h :=
      tendsto_measure_iUnion_atTop (μ := X.ν) hBmono
    rw [hBunion] at h
    simpa only [Function.comp_def] using h
  have hRlim : Tendsto (fun n : ℕ => (X.ν (B n)).toReal)
      atTop (𝓝 ((X.ν (Iio (0 : ℝ))).toReal)) :=
    (ENNReal.tendsto_toReal hFinite).comp hνlim
  have hCont : Continuous
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-((T : ℝ) * x)))) := by
    exact ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (by fun_prop))
  have hExplim : Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (B n)).toReal))))
      atTop (𝓝 (ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))))) :=
    (hCont.tendsto _).comp hRlim
  have hKnown (n : ℕ) : P (E n) = ENNReal.ofReal
      (Real.exp (-((T : ℝ) * (X.ν (B n)).toReal))) := by
    simpa only [E, NX, B] using
      avram_wave7_06_original_intrinsic_negative_band_zero_count_law
        X T n
  have hRepl : (fun n : ℕ => P (E n)) =
      (fun n : ℕ => ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (B n)).toReal)))) := by
    funext n
    exact hKnown n
  change Tendsto (fun n : ℕ => P (E n))
      atTop (𝓝 (P A)) at hProb
  rw [hRepl] at hProb
  have hFinal := tendsto_nhds_unique hProb hExplim
  simpa only [A, NX] using hFinal
