-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:52:46.16384+00:00
-- url     : https://prove2.me/submissions/acc93052-2d6f-49b4-9d17-b86c8ee8d7e8

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_rightDyadic_fullStieltjes_fatou
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (Real.exp (θ * (x + X.X s.toNNReal ω -
        rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * q))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    Filter.liminf (fun n : ℕ => ∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        ENNReal.ofReal (Real.exp (θ * (x + X.X u ω -
          rightLimit D u ω) - (u : ℝ) * q))
      else 0 ∂dividendMeasure D ω ∂P) atTop := by
  classical
  let u : ℕ → ℝ → ℝ≥0 := fun n s =>
    let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
    ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
  let R : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then ENNReal.ofReal (Real.exp
      (θ * (x + X.X (u n s) ω - rightLimit D (u n s) ω) - (u n s : ℝ) * q))
      else 0 ∂dividendMeasure D ω
  let L : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then ENNReal.ofReal (Real.exp
      (θ * (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * q))
      else 0 ∂dividendMeasure D ω
  obtain ⟨κ, hsf, hκ⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hsf
  have hjoint := avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable X x D hD θ q
  have hu (n : ℕ) : Measurable (u n) := by
    dsimp [u]
    fun_prop
  have hRm : ∀ n, Measurable (R n) := by
    intro n
    let Fn : ℝ × Ω → ℝ≥0∞ := fun z =>
      if z.1 ∈ Ioc (0 : ℝ) (T : ℝ) then
        ENNReal.ofReal (Real.exp (θ * (x + X.X (u n z.1) z.2 -
          rightLimit D (u n z.1) z.2) - (u n z.1 : ℝ) * q))
      else 0
    have hφ : Measurable (fun z : ℝ × Ω => (u n z.1, z.2)) :=
      ((hu n).comp measurable_fst).prodMk measurable_snd
    have hvalue : Measurable (fun z : ℝ × Ω => Real.exp
        (θ * (x + X.X (u n z.1) z.2 - rightLimit D (u n z.1) z.2) -
          (u n z.1 : ℝ) * q)) := hjoint.comp hφ
    have hFn : Measurable Fn :=
      Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
        (ENNReal.measurable_ofReal.comp hvalue) measurable_const
    have hFn' : Measurable (Function.uncurry (fun (s : ℝ) (ω : Ω) => Fn (s, ω))) := by
      change Measurable Fn; exact hFn
    have hm := Measurable.lintegral_kernel_prod_left
      (κ := κ) (f := fun (s : ℝ) (ω : Ω) => Fn (s, ω)) hFn'
    change Measurable (fun ω => ∫⁻ s : ℝ, Fn (s, ω) ∂dividendMeasure D ω)
    simpa only [hκ] using hm
  have hpoint : ∀ ω, L ω ≤ Filter.liminf (fun n => R n ω) atTop := by
    intro ω
    simpa only [L, R, u] using
      (avram_wave4_03_original_source_rightDyadic_fullStieltjes_fatou X x D hD θ q ω T hT)
  change (∫⁻ ω, L ω ∂P) ≤
    Filter.liminf (fun n => ∫⁻ ω, R n ω ∂P) atTop
  calc
    (∫⁻ ω, L ω ∂P) ≤
      (∫⁻ ω, Filter.liminf (fun n => R n ω) atTop ∂P) :=
      lintegral_mono hpoint
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, R n ω ∂P) atTop :=
      lintegral_liminf_le hRm
