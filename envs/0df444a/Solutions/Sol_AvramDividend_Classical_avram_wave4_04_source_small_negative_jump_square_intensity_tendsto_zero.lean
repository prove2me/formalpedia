-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_source_small_negative_jump_square_intensity_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:11:03.877105+00:00
-- url     : https://prove2.me/submissions/995c4b05-3d20-4142-920b-e863cf636726

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
open AvramDividend.Classical

/-- The square-energy of vanishing small negative source jumps tends to zero.
This is an intensity limit, not an assertion about the random jump measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Tendsto (fun n : ℕ =>
      ∫⁻ z in Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ENNReal.ofReal (z ^ 2) ∂(X.ν.map (fun y : ℝ => -y)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    calc
      (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) ≤
          (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) := by
        simpa using (lintegral_mono_set
          (Set.subset_univ (Iio (0 : ℝ))) :
          (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) ≤
            ∫⁻ y in Set.univ, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν)
      _ < ⊤ := X.ν_integrable
  let ν := X.ν.map (fun y : ℝ => -y)
  have hν2 : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) < ⊤ :=
    gaussian_levy_square_integrable_neg_pushforward X.ν hlevy
  have hsmall_sq : (∫⁻ z in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (z ^ 2) ∂ν) < ⊤ := by
    calc
      (∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (z ^ 2) ∂ν) =
          ∫⁻ z in Ioi (0 : ℝ), (Ioo (0 : ℝ) 1).indicator
            (fun z : ℝ => ENNReal.ofReal (z ^ 2)) z ∂ν := by
        rw [lintegral_indicator measurableSet_Ioo]
        have hs : Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo 0 1 :=
          Set.inter_eq_left.mpr (fun z hz => hz.1)
        simp [hs]
      _ ≤ (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ Ioo (0 : ℝ) 1
        · simp only [Set.indicator_of_mem hz]
          have hz2 : z ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
          simp [min_eq_right hz2]
        · simp [Set.indicator_of_notMem hz]
      _ < ⊤ := hν2
  let F (n : ℕ) (z : ℝ) : ℝ≥0∞ :=
    (Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))).indicator
      (fun z : ℝ => ENNReal.ofReal (z ^ 2)) z
  let bound (z : ℝ) : ℝ≥0∞ :=
    (Ioo (0 : ℝ) 1).indicator (fun z : ℝ => ENNReal.ofReal (z ^ 2)) z
  have hcut (n : ℕ) : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hmeas (n : ℕ) : Measurable (F n) := by
    dsimp [F]
    exact (show Measurable (fun z : ℝ => ENNReal.ofReal (z ^ 2)) from
      by fun_prop).indicator measurableSet_Ioo
  have hdom (n : ℕ) : F n ≤ᵐ[ν] bound := by
    filter_upwards [] with z
    by_cases hz : z ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))
    · have hz1 : z ∈ Ioo (0 : ℝ) 1 :=
        ⟨hz.1, lt_of_lt_of_le hz.2 (hcut n)⟩
      have hz' : z ∈ Ioo (0 : ℝ) (((n : ℝ) + 1)⁻¹) := by
        simpa only [one_div] using hz
      simpa only [F, bound, one_div,
        Set.indicator_of_mem hz', Set.indicator_of_mem hz1] using
        (le_refl (ENNReal.ofReal (z ^ 2)))
    · have hz' : z ∉ Ioo (0 : ℝ) (((n : ℝ) + 1)⁻¹) := by
        simpa only [one_div] using hz
      simp only [F, bound, one_div, Set.indicator_of_notMem hz']
      exact bot_le
  have hbound : (∫⁻ z, bound z ∂ν) ≠ ⊤ := by
    dsimp [bound]
    rw [lintegral_indicator measurableSet_Ioo]
    exact ne_of_lt hsmall_sq
  have hcutlim : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpoint : ∀ᵐ z ∂ν, Tendsto (fun n => F n z)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [] with z
    have hzero : (fun n => F n z) =ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) := by
      by_cases hz : 0 < z
      · have hev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 1) < z :=
          hcutlim.eventually (eventually_lt_nhds hz)
        filter_upwards [hev] with n hn
        have hnot : z ∉ Ioo (0 : ℝ) (((n : ℝ) + 1)⁻¹) := by
          intro hz'
          exact (not_lt_of_ge (le_of_lt hn))
            (by simpa only [one_div] using hz'.2)
        simpa only [F, one_div, Set.indicator_of_notMem hnot]
      · filter_upwards [] with n
        have hnot : z ∉ Ioo (0 : ℝ) (((n : ℝ) + 1)⁻¹) := by
          intro hz'
          exact hz hz'.1
        simpa only [F, one_div, Set.indicator_of_notMem hnot]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞))
      atTop (𝓝 0)).congr' hzero.symm
  have hlimit := tendsto_lintegral_of_dominated_convergence bound
    hmeas hdom hbound hpoint
  simpa [F, lintegral_indicator measurableSet_Ioo] using hlimit
