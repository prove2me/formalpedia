-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:24:31.694412+00:00
-- url     : https://prove2.me/submissions/45600d05-ab98-41d0-9b69-5a7a5be0783e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_mark_thinning_drift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Arbitrary predictable thinning preserves finite negative-mark L1 and
L2 energy of the genuine stopped source C² Taylor correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal (|(S.indicator HS) (p,z)|) ∂X.ν ∂μ) < ⊤ ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((S.indicator HS (p,z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  classical
  intro Y H HS
  have hBase :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  have hMeas :=
    avram_wave7_07_original_stopped_C2_joint_predictable_mark_thinning_drift
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv S hS
  have hAbsPoint (p : ℝ≥0 × Ω) (z : ℝ) :
      ENNReal.ofReal (|(S.indicator HS) (p,z)|) ≤
        ENNReal.ofReal (|HS (p,z)|) := by
    by_cases hs : (p,z) ∈ S
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hSqPoint (p : ℝ≥0 × Ω) (z : ℝ) :
      ENNReal.ofReal ((S.indicator HS (p,z)) ^ 2) ≤
        ENNReal.ofReal ((HS (p,z)) ^ 2) := by
    by_cases hs : (p,z) ∈ S
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hL1Bound :
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal (|(S.indicator HS) (p,z)|) ∂X.ν ∂μ) ≤
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) := by
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    exact hAbsPoint p z
  have hL2Bound :
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((S.indicator HS (p,z)) ^ 2) ∂X.ν ∂μ) ≤
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) := by
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    exact hSqPoint p z
  exact ⟨hMeas, lt_of_le_of_lt hL1Bound hBase.2.2,
    lt_of_le_of_lt hL2Bound hBase.2.1⟩
