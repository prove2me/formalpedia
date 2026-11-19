-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward71_original_compact_gradient_mark_predictable_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:07:08.375513+00:00
-- url     : https://prove2.me/submissions/a198454b-2d59-4454-bf06-dec23a1d389b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
set_option pp.universes true

set_option pp.explicit true
set_option pp.fullNames true
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 × Ω → ℝ)
    (hY : Measurable[𝓕.rightCont.predictable] Y)
    (w : ℝ → ℝ) (Cband u v δ η : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hleft : 0 < u + δ) (huv : u + δ < v)
    (hv : v < Cband)
    (q : ℝ) (T : ℝ≥0) :
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        if p.1.1 ≤ T ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
          Real.exp (-(q * (p.1.1 : ℝ))) *
          (if Y p.1 ∈ Icc (u + δ) v then
            deriv w (Y p.1) * p.2 else 0) else 0) := by
  classical
  let g : ℝ → ℝ := fun y => if y ∈ Icc (u + δ) v then deriv w y else 0
  have hg : Measurable g :=
    (measurable_deriv w).ite measurableSet_Icc measurable_const
  have hExp : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ)))) :=
    avram_wave7_07_original_predictable_time_exponential_discount_measurable
      (𝓕 := 𝓕) q
  have hT := avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable 𝓕 T
  let Z : Set ℝ := Ioo (-1 : ℝ) (-η)
  have hZ : MeasurableSet Z := measurableSet_Ioo
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hP : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      Real.exp (-(q * (p.1.1 : ℝ))) * (g (Y p.1) * p.2)) :=
    (hExp.comp measurable_fst).mul
      (((hg.comp hY).comp measurable_fst).mul measurable_snd)
  have hMask : MeasurableSet {p : ((ℝ≥0 × Ω) × ℝ) |
      p.1.1 ≤ T ∧ p.2 ∈ Z} :=
    hT.inter (hZ.preimage measurable_snd)
  have hAux : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      if p.1.1 ≤ T ∧ p.2 ∈ Z then
        Real.exp (-(q * (p.1.1 : ℝ))) * (g (Y p.1) * p.2) else 0) :=
    hP.ite hMask measurable_const
  simpa only [g, Z, ite_mul, zero_mul] using hAux
