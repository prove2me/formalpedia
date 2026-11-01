-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_original_source_rightDyadic_fullStieltjes_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:46:54.387219+00:00
-- url     : https://prove2.me/submissions/08493d32-1b02-42c0-95e9-e72cdcd8892f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (ω : Ω) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then ENNReal.ofReal (Real.exp
      (θ * (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * q)) else 0 ∂dividendMeasure D ω) ≤
    Filter.liminf (fun n : ℕ => ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        ENNReal.ofReal (Real.exp (θ * (x + X.X u ω - rightLimit D u ω) -
          (u : ℝ) * q)) else 0 ∂dividendMeasure D ω) atTop := by
  classical
  let μ : Measure ℝ := dividendMeasure D ω
  let u : ℕ → ℝ → ℝ≥0 := fun n s =>
    let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
    ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
  let f : ℕ → ℝ → ℝ≥0∞ := fun n s =>
    if s ∈ Ioc (0 : ℝ) (T : ℝ) then ENNReal.ofReal (Real.exp
      (θ * (x + X.X (u n s) ω - rightLimit D (u n s) ω) - (u n s : ℝ) * q)) else 0
  let g : ℝ → ℝ≥0∞ := fun s =>
    if s ∈ Ioc (0 : ℝ) (T : ℝ) then ENNReal.ofReal (Real.exp
      (θ * (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * q)) else 0
  have hu : ∀ n, Measurable (u n) := by
    intro n
    dsimp [u]; fun_prop
  have hjoint := avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable X x D hD θ q
  have hf : ∀ n, Measurable (f n) := by
    intro n
    have hh : Measurable (fun s : ℝ =>
        Real.exp
          (θ * (x + X.X (u n s) ω - rightLimit D (u n s) ω) -
            (u n s : ℝ) * q)) :=
      hjoint.comp ((hu n).prodMk measurable_const)
    exact Measurable.ite measurableSet_Ioc
      (ENNReal.measurable_ofReal.comp hh) measurable_const
  have hlim : ∀ s : ℝ, Tendsto (fun n : ℕ => f n s) atTop (𝓝 (g s)) := by
    intro s
    by_cases hs : s ∈ Ioc (0 : ℝ) (T : ℝ)
    · have hsT : s.toNNReal ≤ T := by
        simpa using (Real.toNNReal_mono hs.2)
      have hreal : Tendsto (fun n : ℕ =>
          Real.exp (θ * (x + X.X (u n s) ω - rightLimit D (u n s) ω) -
            (u n s : ℝ) * q)) atTop
          (𝓝 (Real.exp (θ * (x + X.X s.toNNReal ω -
            rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * q))) := by
        simpa only [u] using
          (avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
            X x D hD θ q ω s.toNNReal T hT hsT)
      simp only [f, g, if_pos hs]
      exact (ENNReal.continuous_ofReal.tendsto _).comp hreal
    · have hzero : (fun n : ℕ => f n s) = fun _ => (0 : ℝ≥0∞) := by
        funext n; simp only [f, if_neg hs]
      simpa only [hzero, g, if_neg hs] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have heq : (fun s : ℝ => g s) =
      (fun s : ℝ => Filter.liminf (fun n : ℕ => f n s) atTop) := by
    funext s
    exact (hlim s).liminf_eq.symm
  change (∫⁻ s, g s ∂μ) ≤
    Filter.liminf (fun n : ℕ => ∫⁻ s, f n s ∂μ) atTop
  rw [heq]
  exact lintegral_liminf_le hf
