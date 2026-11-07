-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux13_source_levy_cutoff_exponent_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T11:21:53.446795+00:00
-- url     : https://prove2.me/submissions/203e6606-e864-4ea1-bf85-25ae4d25ee0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ n : ℕ,
      Tendsto (fun k : ℕ =>
        Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν)))) atTop (𝓝
        (Real.exp (-((n : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν))))) := by
  intro n
  let s : ℕ → Set ℝ := fun k => Iio (-(1 / ((k : ℝ) + 1)))
  have hmono : Monotone s := by
    intro i j hij y hy
    change y < -(1 / ((i : ℝ) + 1)) at hy
    change y < -(1 / ((j : ℝ) + 1))
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hij_real : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 :=
      by linarith
    exact lt_of_lt_of_le hy (neg_le_neg (one_div_le_one_div_of_le hi hij'))
  have hUn : (⋃ k, s k) = Iio (0 : ℝ) := by
    apply Set.ext
    intro y
    simp only [Set.mem_iUnion, s, mem_Iio]
    constructor
    · rintro ⟨k, hk⟩
      have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · intro hy
      have hneg : 0 < -y := by linarith
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / (-y))
      have hki : 1 < (k : ℝ) * (-y) := (div_lt_iff₀ hneg).mp hk
      have hden : 0 < (k : ℝ) + 1 := by positivity
      have hcut : 1 / ((k : ℝ) + 1) < -y :=
        (div_lt_iff₀ hden).mpr (by nlinarith [hki, hneg])
      exact ⟨k, by linarith⟩
  have hSourceInt : IntegrableOn (fun y : ℝ => 1 - Real.exp y) (Iio (0 : ℝ)) X.ν := by
    have hbase : Integrable (fun y : ℝ => min (1 : ℝ) |y|) (X.ν.restrict (Iio (0 : ℝ))) :=
      boundedVariation_min_one_abs_integrable X hBV
    apply Integrable.mono' hbase
    · exact (continuous_const.sub Real.continuous_exp).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Iio).mono ?_
      intro y hy
      have hy0 : y < (0 : ℝ) := hy
      have hexp : Real.exp y ≤ 1 := by
        simpa using (Real.exp_le_exp.mpr hy0.le : Real.exp y ≤ Real.exp 0)
      have hb : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
      have hpos : 0 ≤ 1 - Real.exp y := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      apply le_min
      · linarith [Real.exp_pos y]
      · rw [abs_of_nonpos hy0.le]
        linarith
  have hmeas : ∀ k, MeasurableSet (s k) := by
    intro k
    exact measurableSet_Iio
  have hI :
      Tendsto (fun k : ℕ =>
        ∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν) atTop
        (𝓝 (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν)) := by
    have hsource : IntegrableOn (fun y : ℝ => 1 - Real.exp y) (⋃ k, s k) X.ν := by
      simpa only [hUn] using hSourceInt
    have hlim :=
      tendsto_setIntegral_of_monotone
        (f := fun y : ℝ => 1 - Real.exp y) (μ := X.ν)
        (s := s) hmeas hmono hsource
    rw [hUn] at hlim
    simpa only [s] using hlim
  exact Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds.mul hI).neg)
