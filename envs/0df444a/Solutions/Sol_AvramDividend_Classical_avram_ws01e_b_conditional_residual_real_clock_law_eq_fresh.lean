-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:57:29.346903+00:00
-- url     : https://prove2.me/submissions/22a03779-c882-42f4-a3e7-be71f4745362

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_tail

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal


theorem solution
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (hZero : discount 0 = 1)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    Measure.map (fun z : Ω × Θ =>
      (e z.2 : ℝ) - (τ z.1 : ℝ))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) =
    Measure.map (fun η : Θ => (e η : ℝ)) Q := by
  set C := {z : Ω × Θ | τ z.1 < e z.2} with hCdef
  have hC : MeasurableSet C :=
    measurableSet_lt (hτ.comp measurable_fst) (he.comp measurable_snd)
  haveI : IsProbabilityMeasure ((P.prod Q)[|C]) := cond_isProbabilityMeasure hPos
  have hf : Measurable (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ)) :=
    (measurable_coe_nnreal_real.comp (he.comp measurable_snd)).sub
      (measurable_coe_nnreal_real.comp (hτ.comp measurable_fst))
  have hg : Measurable (fun η : Θ => (e η : ℝ)) := measurable_coe_nnreal_real.comp he
  haveI : IsProbabilityMeasure (Measure.map (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      ((P.prod Q)[|C])) := Measure.isProbabilityMeasure_map hf.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map (fun η : Θ => (e η : ℝ)) Q) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  have hIoi : ∀ a : ℝ, Measure.map (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      ((P.prod Q)[|C]) (Set.Ioi a) = Measure.map (fun η : Θ => (e η : ℝ)) Q (Set.Ioi a) := by
    intro a
    rw [Measure.map_apply hf measurableSet_Ioi, Measure.map_apply hg measurableSet_Ioi]
    rcases lt_or_ge a 0 with ha | ha
    · have hS : MeasurableSet ((fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ)) ⁻¹' Set.Ioi a) :=
        hf measurableSet_Ioi
      have h1 : ((P.prod Q)[|C]) ((fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ)) ⁻¹' Set.Ioi a) = 1 := by
        apply (prob_compl_eq_zero_iff hS).mp
        have hae := (ae_cond_mem hC (μ := P.prod Q))
        have : ∀ᵐ z ∂((P.prod Q)[|C]),
            z ∈ ((fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ)) ⁻¹' Set.Ioi a) := by
          filter_upwards [hae] with z hz
          simp only [Set.mem_preimage, Set.mem_Ioi]
          have : (τ z.1 : ℝ) < (e z.2 : ℝ) := hz
          linarith
        exact ae_iff.mp this
      have h2 : Q ((fun η : Θ => (e η : ℝ)) ⁻¹' Set.Ioi a) = 1 := by
        have : (fun η : Θ => (e η : ℝ)) ⁻¹' Set.Ioi a = Set.univ := by
          ext η; simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
          exact lt_of_lt_of_le ha (e η).2
        rw [this, measure_univ]
      rw [h1, h2]
    · set t : ℝ≥0 := a.toNNReal
      have hta : (t : ℝ) = a := Real.coe_toNNReal a ha
      have h := (AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_tail P Q τ hτ Y hY
        hInd e he discount hd hTail factor hShift hPos t Set.univ MeasurableSet.univ).1
      have hset : (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ)) ⁻¹' Set.Ioi a =
          {z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ Set.univ} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, Set.mem_univ, and_true]
        rw [← NNReal.coe_lt_coe, NNReal.coe_add, hta]
        constructor <;> intro h <;> linarith
      have hsetQ : (fun η : Θ => (e η : ℝ)) ⁻¹' Set.Ioi a = {η : Θ | t < e η} := by
        ext η
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq]
        rw [← NNReal.coe_lt_coe, hta]
      rw [hset, h, Set.preimage_univ, measure_univ, mul_one, hsetQ, hTail]
      have := hShift 0 t
      rw [zero_add, hZero, mul_one] at this
      exact this.symm
  apply Measure.ext_of_Iic
  intro a
  rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    prob_compl_eq_one_sub measurableSet_Ioi, hIoi a]
