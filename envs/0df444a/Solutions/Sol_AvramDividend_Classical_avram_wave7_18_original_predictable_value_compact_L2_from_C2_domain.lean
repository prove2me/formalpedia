-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_predictable_value_compact_L2_from_C2_domain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:19:06.210458+00:00
-- url     : https://prove2.me/submissions/be6b913a-977d-4996-9c68-47af41aba43a

import Mathlib
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u v : ℝ)
    (ha : 0 < a) (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hband : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let V : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then w (Y p) else 0
    Measurable[𝓕.rightCont.predictable] V ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((V p) ^ 2) ∂μ) < ⊤ := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  have hp := avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω => Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1) at hp
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hY : Measurable Y := hp.measurable
  have hsmooth : ContDiffOn ℝ 2 w (Ioo a b) :=
    hw_smooth.mono (by
      intro y hy
      exact ⟨lt_trans ha hy.1, hband y hy⟩)
  have hcontinuous : ContinuousOn w (Ioo a b) := hsmooth.continuousOn
  have hext : Measurable (fun y : ℝ =>
      if y ∈ Ioo a b then w y else 0) := by
    change Measurable ((Ioo a b).piecewise w (fun _ => (0 : ℝ)))
    exact hcontinuous.measurable_piecewise continuous_const.continuousOn
      isOpen_Ioo.measurableSet
  have hinside : Measurable (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Ioo a b then w (Y p) else 0) := hext.comp hY
  have hbandset : MeasurableSet {p : ℝ≥0 × Ω | Y p ∈ Icc u v} :=
    measurableSet_Icc.preimage hY
  have hV : Measurable (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Icc u v then w (Y p) else 0) := by
    have heq : (fun p : ℝ≥0 × Ω => if Y p ∈ Icc u v then w (Y p) else 0) =
        (fun p : ℝ≥0 × Ω => if Y p ∈ Icc u v then
          (if Y p ∈ Ioo a b then w (Y p) else 0) else 0) := by
      funext p
      by_cases hp : Y p ∈ Icc u v
      · have hp' : Y p ∈ Ioo a b :=
          ⟨lt_of_lt_of_le hau hp.1, lt_of_le_of_lt hp.2 hvb⟩
        simp [hp, hp']
      · simp [hp]
    rw [heq]
    exact hinside.ite hbandset measurable_const
  have hcompact : ContinuousOn w (Icc u v) :=
    hcontinuous.mono (by
      intro y hy
      exact ⟨lt_of_lt_of_le hau hy.1, lt_of_le_of_lt hy.2 hvb⟩)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcompact
  have hMpos : 0 ≤ M := le_trans (abs_nonneg (w u)) (by
    simpa only [Real.norm_eq_abs] using hM u ⟨le_refl u, huv⟩)
  have hbound (p : ℝ≥0 × Ω) :
      ((if Y p ∈ Icc u v then w (Y p) else 0) ^ 2) ≤ M ^ 2 := by
    by_cases hp : Y p ∈ Icc u v
    · have hAbs : |w (Y p)| ≤ M := by
        simpa only [Real.norm_eq_abs] using hM (Y p) hp
      have hlo := (abs_le.mp hAbs).1
      have hhi := (abs_le.mp hAbs).2
      have hnonneg1 : 0 ≤ M - w (Y p) := by linarith
      have hnonneg2 : 0 ≤ M + w (Y p) := by linarith
      simp only [if_pos hp]
      nlinarith [mul_nonneg hnonneg1 hnonneg2]
    · simp [hp, sq_nonneg M]
  constructor
  · exact hV
  · have hfinite : μ Set.univ * ENNReal.ofReal (M ^ 2) < ⊤ :=
      ENNReal.mul_lt_top hμ ENNReal.ofReal_lt_top
    calc
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal
        ((if Y p ∈ Icc u v then w (Y p) else 0) ^ 2) ∂μ) ≤
          ∫⁻ _ : ℝ≥0 × Ω, ENNReal.ofReal (M ^ 2) ∂μ := by
            apply lintegral_mono
            intro p
            exact ENNReal.ofReal_le_ofReal (hbound p)
      _ = μ Set.univ * ENNReal.ofReal (M ^ 2) := by simp [mul_comm]
      _ < ⊤ := hfinite
