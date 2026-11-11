-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys40_original_finite_activity_bounded_predictable_mark_kernel_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:03:53.386595+00:00
-- url     : https://prove2.me/submissions/45d8ca22-3b70-4889-85eb-c74a3cce38e4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys44_original_cap_reward_bounded_below_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_prejump_marked_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The marked negative-jump kernel is integrable under finite clock and mark mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (c : ℝ) (hc : 0 ≤ c)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ≤ c) :
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0
  change Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))
  have hwMeas : Measurable w :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w w ⊤ hw_cont hw_neg (by intro _ y; rfl)
      (by intro h; exact (h rfl).elim)
  have hRaw := avram_wave4_03_original_controlled_prejump_marked_kernel_measurable
    X x D hD w hwMeas
  have hDiscount :=
    avram_wave7_07_original_predictable_time_exponential_discount_measurable
      (𝓕 := 𝓕) q
  have hEvent : MeasurableSet
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1 ∈ E ∧ p.2 < 0} := by
    exact (hEm.preimage measurable_fst).inter
      (measurableSet_Iio.preimage measurable_snd)
  have hHmeas : Measurable H := by
    dsimp [H]
    exact Measurable.ite hEvent
      ((hDiscount.comp measurable_fst).mul hRaw) measurable_const
  obtain ⟨R, hR0, hR⟩ :=
    avram_bvb_phys44_original_cap_reward_bounded_below_cap
      w hw_cont hw_neg c hc
  have hHbound : ∀ p, ‖H p‖ ≤ 2 * R := by
    intro p
    by_cases hp : p.1 ∈ E ∧ p.2 < 0
    · have hpre := hEregion p.1 hp.1
      let y : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
      have hy : y ≤ c := hpre
      have hyz : y + p.2 ≤ c := by linarith [hp.2]
      have hw1 : |w y| ≤ R := hR y hy
      have hw2 : |w (y + p.2)| ≤ R := hR (y + p.2) hyz
      have htime : 0 ≤ q * (p.1.1 : ℝ) :=
        mul_nonneg hq (by exact_mod_cast p.1.1.property)
      have hExp0 : 0 ≤ Real.exp (-(q * (p.1.1 : ℝ))) :=
        (Real.exp_pos _).le
      have hExp1 : Real.exp (-(q * (p.1.1 : ℝ))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        linarith
      change |H p| ≤ 2 * R
      rw [show H p = Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (y + p.2) - w y) from by simp only [H, if_pos hp, y]]
      rw [abs_mul, abs_of_nonneg hExp0]
      calc
        Real.exp (-(q * (p.1.1 : ℝ))) * |w (y + p.2) - w y|
            ≤ 1 * |w (y + p.2) - w y| :=
              mul_le_mul_of_nonneg_right hExp1 (abs_nonneg _)
        _ ≤ 1 * (|w (y + p.2)| + |w y|) := by
          have htri : |w (y + p.2) - w y| ≤
              |w (y + p.2)| + |w y| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le (w (y + p.2)) (-(w y)))
          exact mul_le_mul_of_nonneg_left htri (by norm_num)
        _ ≤ 2 * R := by nlinarith
    · change |H p| ≤ 2 * R
      simp only [H, if_neg hp, abs_zero]
      linarith
  haveI : IsFiniteMeasure μ := ⟨hμ⟩
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) :=
    ⟨by simpa using hActivity⟩
  have hConstant : Integrable
      (fun _ : ((ℝ≥0 × Ω) × ℝ) => (2 * R : ℝ))
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := integrable_const _
  refine hConstant.mono' hHmeas.aestronglyMeasurable ?_
  filter_upwards [] with p
  have h2R : 0 ≤ (2 : ℝ) * R := mul_nonneg (by norm_num) hR0
  simpa only [Real.norm_eq_abs, abs_of_nonneg h2R]
    using hHbound p
