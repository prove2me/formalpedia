-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:57:50.357915+00:00
-- url     : https://prove2.me/submissions/b03c3ad0-f447-4c29-877c-d6909290e5e6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
/-- The original Lévy squared-mark small-negative-jump tail vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    Tendsto (fun n : ℕ => ∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
      ENNReal.ofReal (z ^ 2) ∂X.ν) atTop (𝓝 0) := by
  let C : ℕ → Set ℝ := fun n => Ioc (-(1 / ((n : ℝ) + 1))) 0
  let g : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (z ^ 2)
  let F : ℕ → ℝ → ℝ≥0∞ := fun n z => (C n).indicator g z
  let bound : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    have hg : Measurable g := by dsimp [g]; fun_prop
    exact hg.indicator (by dsimp [C]; exact measurableSet_Ioc)
  have hFbound : ∀ n, F n ≤ᵐ[X.ν] bound := by
    intro n; apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ C n
    · have hδpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have hδle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
        (div_le_iff₀ hδpos).2 (by nlinarith [hnnonneg])
      have hzlow : -1 ≤ z := by
        have h := hz.1
        dsimp [C] at hz
        linarith
      have hzhigh : z ≤ 0 := hz.2
      have hmul : 0 ≤ (z + 1) * (-z) := mul_nonneg (by linarith) (by linarith)
      have hsq : z ^ 2 ≤ (1 : ℝ) := by nlinarith [hmul]
      dsimp [F, bound, g]
      rw [Set.indicator_of_mem hz, min_eq_right hsq]
    · dsimp [F, bound]
      simp [Set.indicator_of_notMem hz]
  have hFin : (∫⁻ z, bound z ∂X.ν) ≠ ⊤ := ne_of_lt X.ν_integrable
  have hZero : ∀ z : ℝ, Tendsto (fun n => F n z) atTop (𝓝 (0 : ℝ≥0∞)) := by
    intro z
    by_cases hzneg : z < 0
    · have hδevent : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 1) < -z :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
          (Iio_mem_nhds (by linarith))
      have hEq : (fun n : ℕ => F n z) =ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) := by
        filter_upwards [hδevent] with n hn
        have hnot : z ∉ C n := by
          intro hzC
          have h := hzC.1
          dsimp [C] at hzC
          linarith
        simp [F, Set.indicator_of_notMem hnot]
      exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
    · have hz0 : 0 ≤ z := le_of_not_gt hzneg
      have hEq (n : ℕ) : F n z = 0 := by
        by_cases heq : z = 0
        · subst z
          simp [F, C, g]
        · have hzpos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm heq)
          have hnot : z ∉ C n := by
            intro hc
            exact (not_le.mpr hzpos) hc.2
          simp [F, Set.indicator_of_notMem hnot]
      simpa only [hEq] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hDom : Tendsto (fun n => ∫⁻ z, F n z ∂X.ν)
      atTop (𝓝 (∫⁻ z, (0 : ℝ≥0∞) ∂X.ν)) :=
    tendsto_lintegral_of_dominated_convergence bound hFmeas
      hFbound hFin (Filter.Eventually.of_forall hZero)
  have hIntegralEq (n : ℕ) : (∫⁻ z, F n z ∂X.ν) =
      ∫⁻ z in C n, g z ∂X.ν :=
    lintegral_indicator (by simp [C] : MeasurableSet (C n)) g
  have hFunEq : (fun n => ∫⁻ z, F n z ∂X.ν) =
      (fun n => ∫⁻ z in C n, g z ∂X.ν) := funext hIntegralEq
  rw [hFunEq] at hDom
  simpa only [C, g, lintegral_zero] using hDom
