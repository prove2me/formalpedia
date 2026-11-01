-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_discounted_actual_ruin_stopped_full_jump_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:14:38.458843+00:00
-- url     : https://prove2.me/submissions/808e93ef-b9b7-4bbc-942b-a91dfabe5aff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_controlled_predictable_jump_energy_contraction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite-clock discounted inclusive ruin stopping preserves the actual source full negative-mark predictable square energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if p.1.1 ≤ T then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
            (1 : ℝ) else 0)
        else 0) * J p
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  dsimp only
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then
      Real.exp (-(q * (p.1 : ℝ))) *
        (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then
          (1 : ℝ) else 0)
      else 0
  let K : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => ρ p.1
  change Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p => K p * J p) ∧
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((K (p, z) * J (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤
  have hder (r : ℝ) : deriv (fun y : ℝ => y) r = 1 :=
    (hasDerivAt_id r).deriv
  have hρsp : IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        if t ≤ T then
          Real.exp (-(q * (t : ℝ))) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then
              (1 : ℝ) else 0)
        else 0) := by
    simpa only [hder, mul_one] using
      (avram_wave3_04_source_stopped_discounted_deriv_predictable
        X x D hD (fun y : ℝ => y) q T)
  change StronglyMeasurable[𝓕.rightCont.predictable] ρ at hρsp
  have hρm : Measurable[𝓕.rightCont.predictable] ρ :=
    hρsp.measurable
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  have hKm : Measurable K :=
    hρm.comp measurable_fst
  have hρbound (p : ℝ≥0 × Ω) : |ρ p| ≤ 1 := by
    by_cases ht : p.1 ≤ T
    · by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
      · have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
        have hqtime : 0 ≤ q * (p.1 : ℝ) := mul_nonneg hq ht0
        have he : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
          calc
            Real.exp (-(q * (p.1 : ℝ))) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by linarith)
            _ = 1 := Real.exp_zero
        simpa [ρ, ht, hs, abs_of_pos (Real.exp_pos _)] using he
      · simp [ρ, ht, hs]
    · simp [ρ, ht]
  have hKb : ∀ p : ((ℝ≥0 × Ω) × ℝ), |K p| ≤ 1 :=
    fun p => hρbound p.1
  exact avram_wave5_03_controlled_predictable_jump_energy_contraction
    X x D hD w a b u v δ hw hw_cont hw_neg
    hau huv hvb hu0 hδ hδone hband μ hμ K hKm hKb
