-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_moving_signed_predictable_unit_contraction_L1_tail_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:02:50.599385+00:00
-- url     : https://prove2.me/submissions/309c4051-acdd-43cf-9f17-c03d0dc90052

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_adaptive_predictable_mark_L1_tail_vanishes
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Moving signed predictable unit contractions preserve original negative Taylor
small-jump L1 energy convergence at adaptive jointly predictable cutoffs. -/
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
    (S : ℕ → Set ((ℝ≥0 × Ω) × ℝ))
    (hSm : ∀ n, MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (S n))
    (hSanti : Antitone S) (hSempty : (⋂ n, S n) = ∅)
    (a : ℕ → ℝ≥0 × Ω → ℝ)
    (ham : ∀ n, Measurable[𝓕.rightCont.predictable] (a n))
    (ha : ∀ n p, |a n p| ≤ 1) :
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
    Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r =>
          ENNReal.ofReal (|a n r.1 * HS r|)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by
  classical
  intro Y H HS
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  let M := μ.prod (X.ν.restrict (Iio (0 : ℝ)))
  let F : ((ℝ≥0 × Ω) × ℝ) → ENNReal := fun p => ENNReal.ofReal (|HS p|)
  let G : ℕ → ENNReal := fun n =>
    ∫⁻ p : ((ℝ≥0 × Ω) × ℝ), (S n).indicator F p ∂M
  let K : ℕ → ENNReal := fun n =>
    ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
      (S n).indicator (fun r => ENNReal.ofReal (|a n r.1 * HS r|)) p ∂M
  have hOne : ∀ p : ℝ≥0 × Ω, 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 := by
    intro p
    constructor <;> norm_num
  have hFull : Tendsto G atTop (𝓝 0) := by
    have h := avram_wave7_07_original_adaptive_predictable_mark_L1_tail_vanishes
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ S hSm hSanti hSempty (fun _ => 1) measurable_const hOne
    simpa only [one_mul] using h
  have hBound (n : ℕ) : K n ≤ G n := by
    apply lintegral_mono
    intro p
    by_cases hp : p ∈ S n
    · simp only [Set.indicator_of_mem hp]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_mul]
      nlinarith [mul_nonneg (sub_nonneg.mpr (ha n p.1))
        (abs_nonneg (HS p))]
    · simp only [Set.indicator_of_notMem hp]
      exact le_refl _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hFull (fun n => bot_le) hBound
