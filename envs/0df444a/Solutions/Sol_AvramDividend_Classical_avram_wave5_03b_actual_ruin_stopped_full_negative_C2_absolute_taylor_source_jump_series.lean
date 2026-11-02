-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_absolute_taylor_source_jump_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:44:41.101253+00:00
-- url     : https://prove2.me/submissions/c23665ac-b678-4499-9a58-11f4aa02c0a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual-source nonlinear Taylor absolute jump reward: intrinsic same-path
jump measure versus the literal time-indexed (possibly infinite) series. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) :
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
    let J : ℝ≥0 → Ω → ℝ := fun q ω =>
      X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {q : ℝ≥0 | 0 < q ∧ J q ω ≠ 0}).map
        (fun q : ℝ≥0 => (q, J q ω)))
    ∀ (s t : ℝ≥0) (ω : Ω),
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) =
      ∑' q : ℝ≥0,
        if 0 < q ∧ J q ω ≠ 0 then
          (if s < q ∧ q ≤ t ∧ J q ω < 0 then
            ENNReal.ofReal (|HS ((q,ω),J q ω)|) else 0)
        else 0 := by
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
  let J : ℝ≥0 → Ω → ℝ := fun q ω =>
    X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {q : ℝ≥0 | 0 < q ∧ J q ω ≠ 0}).map
      (fun q : ℝ≥0 => (q, J q ω)))
  change ∀ (s t : ℝ≥0) (ω : Ω),
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) =
      ∑' q : ℝ≥0,
        if 0 < q ∧ J q ω ≠ 0 then
          (if s < q ∧ q ≤ t ∧ J q ω < 0 then
            ENNReal.ofReal (|HS ((q,ω),J q ω)|) else 0)
        else 0
  have hzero :
      (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) Set.univ < ⊤ := by
    simp
  have hHmeas :
      Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)] HS := by
    simpa [HS, H, Y] using
      (avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
        X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
        (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) hzero).1
  have hAbsMeas :
      Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
        (fun p => ENNReal.ofReal (|HS p|)) := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
    exact ENNReal.measurable_ofReal.comp hHmeas.abs
  obtain ⟨Xrc, hPath, _, _, _⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  intro s t ω
  have hBase :=
    avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
      Xrc s t (fun _ => t) (Iio (0 : ℝ)) measurableSet_Iio
      (fun p => ENNReal.ofReal (|HS p|)) hAbsMeas ω
  rw [hPath] at hBase
  simpa [NX, J, Set.mem_Iio, and_assoc] using hBase
