-- Prove2me | solution 1 for FBMSP.singlePrice_attains
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:15:36.927022+00:00
-- url     : https://prove2.me/submissions/ab7063f1-fb6a-48ad-be6c-579effa576a9

import Definitions.Def_FBMSP_Model

open MeasureTheory Set Filter FBMSP
open scoped Topology

private lemma att_survival_antitone (η : Measure ℝ) [IsProbabilityMeasure η] :
    Antitone (survival η) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
    (measure_mono (Ici_subset_Ici.mpr hab))

private lemma att_survival_left (η : Measure ℝ) [IsProbabilityMeasure η] (a : ℝ) :
    ContinuousWithinAt (survival η) (Iic a) a := by
  have hi : Integrable (fun _ : ℝ => (1 : ℝ)) η := integrable_const 1
  have hc := (hi.integrableOn (s := Iio a)).continuousWithinAt_Iic_primitive_Iio
  have heq (t : ℝ) :
      survival η t = η.real univ - ∫ _ in Iio t, (1 : ℝ) ∂η := by
    simpa only [survival, setIntegral_const, smul_eq_mul, mul_one, compl_Iio, Measure.real]
      using (measureReal_compl (μ := η) (s := Iio t) measurableSet_Iio)
  have hfun : survival η = fun t => η.real univ - ∫ _ in Iio t, (1 : ℝ) ∂η :=
    funext heq
  rw [hfun]
  exact continuousWithinAt_const.sub hc

/-- Inclusive tails give a continuous upper bound locally at every price, including atoms. -/
private lemma att_upperSemicontinuous (η : Measure ℝ) [IsProbabilityMeasure η] (x : ℝ) :
    UpperSemicontinuous (fun p : ℝ => max p 0 * survival η (p - x)) := by
  intro p
  have hc : ContinuousAt (fun q : ℝ => min q p - x) p := by fun_prop
  have hmaps : MapsTo (fun q : ℝ => min q p - x) univ (Iic (p - x)) := by
    intro q hq
    exact sub_le_sub_right (min_le_right q p) x
  have hg : ContinuousAt (fun q : ℝ => survival η (min q p - x)) p := by
    have h := (att_survival_left η (p - x)).comp_of_eq
      hc.continuousWithinAt hmaps (by simp)
    simpa only [Function.comp_def, continuousWithinAt_univ] using h
  have hmajor : ContinuousAt (fun q : ℝ => max q 0 * survival η (min q p - x)) p :=
    (by fun_prop : ContinuousAt (fun q : ℝ => max q 0) p).mul hg
  intro b hb
  have hb' : max p 0 * survival η (min p p - x) < b := by simpa using hb
  filter_upwards [hmajor.eventually (Iio_mem_nhds hb')] with q hq
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left
      (att_survival_antitone η (sub_le_sub_right (min_le_left q p) x))
      (le_max_right q 0)) hq

private lemma att_posted_upperSemicontinuousOn (η : Measure ℝ)
    [IsProbabilityMeasure η] (x : ℝ) :
    UpperSemicontinuousOn (postedRevenue η x) (Ici 0) := by
  intro p hp
  refine ((att_upperSemicontinuous η x).upperSemicontinuousWithinAt (Ici 0) p).congr_of_eventuallyEq hp ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [postedRevenue, max_eq_left (show 0 ≤ q from hq)]

private lemma att_revenue_le_tail (η : Measure ℝ) [IsProbabilityMeasure η]
    (hi : Integrable (fun e : ℝ => e) η) (x p : ℝ) :
    postedRevenue η x p ≤ ∫ e in Ici (p - x), e + x ∂η := by
  have hc : Integrable (fun _ : ℝ => p) η := integrable_const p
  have hv : Integrable (fun e : ℝ => e + x) η := hi.add (integrable_const x)
  have h := setIntegral_mono_on hc.integrableOn hv.integrableOn measurableSet_Ici
    (fun e (he : e ∈ Ici (p - x)) => by change p - x ≤ e at he; linarith)
  simpa only [setIntegral_const, smul_eq_mul, postedRevenue, survival, Measure.real, mul_comm] using h

private lemma att_revenue_tendsto (η : Measure ℝ) [IsProbabilityMeasure η]
    (hi : Integrable (fun e : ℝ => e) η) (x : ℝ) :
    Tendsto (postedRevenue η x) atTop (𝓝 0) := by
  have hshift : Tendsto (fun p : ℝ => p - x) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b + x)] with p hp
    linarith
  have htail : Tendsto (fun p : ℝ => ∫ e in Ici (p - x), e + x ∂η) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero hshift
  apply squeeze_zero' ?_ (Eventually.of_forall (att_revenue_le_tail η hi x)) htail
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with p hp
  exact mul_nonneg hp ENNReal.toReal_nonneg

private lemma att_exists_optimal (η : Measure ℝ) [IsProbabilityMeasure η]
    (hi : Integrable (fun e : ℝ => e) η) (x : ℝ) :
    ∃ p, IsOptimalPrice η x p := by
  by_cases hz : ∀ p : ℝ, 0 ≤ p → postedRevenue η x p ≤ 0
  · refine ⟨0, le_rfl, ?_⟩
    simpa only [postedRevenue, zero_mul] using hz
  push Not at hz
  obtain ⟨p₀, hp₀, hr₀⟩ := hz
  have ht : ∀ᶠ p in atTop, postedRevenue η x p < postedRevenue η x p₀ :=
    (att_revenue_tendsto η hi x).eventually (Iio_mem_nhds hr₀)
  obtain ⟨B, hB⟩ := eventually_atTop.1 ht
  let C := max (max B p₀) 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hBC : B ≤ C := (le_max_left B p₀).trans (le_max_left _ _)
  have hpC : p₀ ≤ C := (le_max_right B p₀).trans (le_max_left _ _)
  have hsc : UpperSemicontinuousOn (postedRevenue η x) (Icc 0 C) :=
    (att_posted_upperSemicontinuousOn η x).mono (fun q hq => hq.1)
  obtain ⟨p, hp, hmax⟩ := hsc.exists_isMaxOn (nonempty_Icc.2 hC0) isCompact_Icc
  refine ⟨p, hp.1, fun q hq => ?_⟩
  by_cases hqC : q ≤ C
  · exact hmax ⟨hq, hqC⟩
  · exact (hB q (hBC.trans (le_of_not_ge hqC))).le.trans (hmax ⟨hp₀, hpC⟩)

theorem solution (η : MeasureTheory.Measure ℝ)
    (hnoise : ValidNoise η) (x : ℝ) (hx : 0 ≤ x) :
    IsLeastOptimalPrice η x (singlePrice η x) ∧
      postedRevenue η x (singlePrice η x) = singleRevenue η x := by
  letI : IsProbabilityMeasure η := hnoise.1
  obtain ⟨p₀, hp₀⟩ := att_exists_optimal η hnoise.2.1 x
  have hset : {p | IsOptimalPrice η x p} =
      Ici 0 ∩ (fun p : ℝ => max p 0 * survival η (p - x)) ⁻¹'
        Ici (postedRevenue η x p₀) := by
    ext p
    constructor
    · intro hp
      refine ⟨hp.1, ?_⟩
      simpa only [mem_preimage, mem_Ici, max_eq_left hp.1, postedRevenue]
        using hp.2 p₀ hp₀.1
    · rintro ⟨hp, hr⟩
      change 0 ≤ p at hp
      have hr' : postedRevenue η x p₀ ≤ postedRevenue η x p := by
        simpa only [mem_preimage, mem_Ici, max_eq_left hp, postedRevenue] using hr
      exact ⟨hp, fun q hq => (hp₀.2 q hq).trans hr'⟩
  have hc : IsClosed {p | IsOptimalPrice η x p} := by
    rw [hset]
    exact isClosed_Ici.inter ((att_upperSemicontinuous η x).isClosed_preimage _)
  have hne : ({p | IsOptimalPrice η x p} : Set ℝ).Nonempty := ⟨p₀, hp₀⟩
  have hbd : BddBelow {p | IsOptimalPrice η x p} := ⟨0, fun p hp => hp.1⟩
  have hleast : IsLeast {p | IsOptimalPrice η x p} (singlePrice η x) :=
    hc.isLeast_csInf hne hbd
  refine ⟨⟨hleast.1, hleast.2⟩, ?_⟩
  have hgreat : IsGreatest
      {r : ℝ | ∃ p : ℝ, 0 ≤ p ∧ r = postedRevenue η x p}
      (postedRevenue η x (singlePrice η x)) := by
    refine ⟨⟨singlePrice η x, hleast.1.1, rfl⟩, ?_⟩
    rintro r ⟨p, hp, rfl⟩
    exact hleast.1.2 p hp
  exact hgreat.csSup_eq.symm
