-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps13_original_random_clock_Taylor_kernel_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:51:34.540307+00:00
-- url     : https://prove2.me/submissions/6d1c4a55-3363-4081-a800-e2c7497ca141

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_zero_negative_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_inclusive_stopped_discounted_truncated_compensation_taylor_joint_predictable_mark_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Exact original source predictability of the compact stopped Taylor mark kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let GWσ : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1.1 ≤ σ p.1.2 then GW p else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] GWσ := by
  intro a Y H HS GW GWσ
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let A : Set ((ℝ≥0 × Ω) × ℝ) :=
    {p | Y p.1 ∈ Icc (u + δ) v}
  let B : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
  let Cstop : Set ((ℝ≥0 × Ω) × ℝ) :=
    {p | p.1.1 ≤ σ p.1.2}
  have hA : MeasurableSet A := by
    convert (avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
      X x D hD (u + δ) v).prod
      (show MeasurableSet (Set.univ : Set ℝ) from MeasurableSet.univ) using 1
    ext p
    simp [A]
    rfl
  have hB : MeasurableSet B :=
    avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable 𝓕 T
  have hCstop : MeasurableSet Cstop := by
    convert (avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask
      𝓕.rightCont σ hσ).prod
      (show MeasurableSet (Set.univ : Set ℝ) from MeasurableSet.univ) using 1
    ext p
    simp [Cstop]
  let base : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    ((if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      Real.exp (-(q * (p.1.1 : ℝ)))) *
      ((fun y : ℝ => w (y + p.2) - w y -
        (if -1 < p.2 then p.2 * deriv w y else 0)) (Y p.1))
  have hbase : Measurable base :=
    avram_p4_s3_interval_i_original_inclusive_stopped_discounted_truncated_compensation_taylor_joint_predictable_mark_measurable
      X x D hD w (avram_p3_bv_original_zero_negative_measurable w hw_cont hw_neg)
      q (ruinTime X x D) (ruinTime_stopping_rightCont_filtration X x D hD)
  have hid : GWσ = (A ∩ B ∩ Cstop).indicator base := by
    funext p
    by_cases ha : Y p.1 ∈ Icc (u + δ) v
    all_goals by_cases hb : p.1.1 ≤ T
    all_goals by_cases hc : p.1.1 ≤ σ p.1.2
    all_goals by_cases hr : (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
    all_goals by_cases hm : -1 < p.2
    all_goals dsimp only [GWσ, GW, a, HS, H, base]
    all_goals simp only [Set.mem_Icc] at ha
    all_goals simp [A, B, Cstop, Set.indicator, ha, hb, hc, hr, hm,
      Set.mem_Icc] <;> ring
  rw [hid]
  exact hbase.indicator ((hA.inter hB).inter hCstop)
