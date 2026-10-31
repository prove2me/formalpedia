-- Prove2me | solution 1 for FBMSP.corollary1_segment_price_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:22:46.637273+00:00
-- url     : https://prove2.me/submissions/3c6a1465-6187-4353-a7af-0f8cda7d8f80

import Theorems.Thm_FBMSP_singlePrice_attains

open MeasureTheory Set Filter FBMSP
open scoped Topology BigOperators

private lemma seg_survival_antitone (η : Measure ℝ) [IsProbabilityMeasure η] :
    Antitone (survival η) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
    (measure_mono (Ici_subset_Ici.mpr hab))

private lemma seg_survival_left (η : Measure ℝ) [IsProbabilityMeasure η] (a : ℝ) :
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
private lemma seg_upperSemicontinuous (η : Measure ℝ) [IsProbabilityMeasure η] (x : ℝ) :
    UpperSemicontinuous (fun p : ℝ => max p 0 * survival η (p - x)) := by
  intro p
  have hc : ContinuousAt (fun q : ℝ => min q p - x) p := by fun_prop
  have hmaps : MapsTo (fun q : ℝ => min q p - x) univ (Iic (p - x)) := by
    intro q hq
    exact sub_le_sub_right (min_le_right q p) x
  have hg : ContinuousAt (fun q : ℝ => survival η (min q p - x)) p := by
    have h := (seg_survival_left η (p - x)).comp_of_eq
      hc.continuousWithinAt hmaps (by simp)
    simpa only [Function.comp_def, continuousWithinAt_univ] using h
  have hmajor : ContinuousAt (fun q : ℝ => max q 0 * survival η (min q p - x)) p :=
    (by fun_prop : ContinuousAt (fun q : ℝ => max q 0) p).mul hg
  intro b hb
  have hb' : max p 0 * survival η (min p p - x) < b := by simpa using hb
  filter_upwards [hmajor.eventually (Iio_mem_nhds hb')] with q hq
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left
      (seg_survival_antitone η (sub_le_sub_right (min_le_left q p) x))
      (le_max_right q 0)) hq

private lemma seg_posted_upperSemicontinuousOn (η : Measure ℝ)
    [IsProbabilityMeasure η] (x : ℝ) :
    UpperSemicontinuousOn (postedRevenue η x) (Ici 0) := by
  intro p hp
  refine ((seg_upperSemicontinuous η x).upperSemicontinuousWithinAt (Ici 0) p).congr_of_eventuallyEq hp ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [postedRevenue, max_eq_left (show 0 ≤ q from hq)]

/-- Log-concave survival makes price revenue quasiconcave, including zero tails. -/
private lemma seg_revenue_three_point (η : Measure ℝ) [IsProbabilityMeasure η]
    (hmhr : HasMHR η) (x a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    min (postedRevenue η x a) (postedRevenue η x c) ≤ postedRevenue η x b := by
  have hs0 (t : ℝ) : 0 ≤ survival η t := ENNReal.toReal_nonneg
  by_cases hm : min (postedRevenue η x a) (postedRevenue η x c) ≤ 0
  · exact hm.trans (mul_nonneg (ha.trans hab) (hs0 _))
  have hmpos := lt_of_not_ge hm
  have hrapos := (lt_min_iff.mp hmpos).1
  have hrcpos := (lt_min_iff.mp hmpos).2
  have hapos : 0 < a := pos_of_mul_pos_left hrapos (hs0 _)
  have hcpos : 0 < c := hapos.trans_le (hab.trans hbc)
  have hbpos : 0 < b := hapos.trans_le hab
  have hsa : 0 < survival η (a - x) := pos_of_mul_pos_right hrapos ha
  have hsc : 0 < survival η (c - x) :=
    pos_of_mul_pos_right hrcpos (le_of_lt hcpos)
  have hsb : 0 < survival η (b - x) :=
    hsc.trans_le (seg_survival_antitone η (sub_le_sub_right hbc x))
  by_cases hac : a = c
  · have hba : b = a := le_antisymm (hbc.trans hac.symm.le) hab
    simp [hac, hba]
  have hac' : a < c := lt_of_le_of_ne (hab.trans hbc) hac
  have hden : 0 < c - a := sub_pos.mpr hac'
  let u := (c - b) / (c - a)
  let v := (b - a) / (c - a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hbc) hden.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hab) hden.le
  have huv : u + v = 1 := by
    dsimp [u, v]
    field_simp [ne_of_gt hden]
    <;> ring
  have hbary : u * a + v * c = b := by
    dsimp [u, v]
    field_simp [ne_of_gt hden]
    <;> ring
  have hshift : u * (a - x) + v * (c - x) = b - x := by
    calc
      u * (a - x) + v * (c - x) = (u * a + v * c) - (u + v) * x := by ring
      _ = b - x := by rw [hbary, huv, one_mul]
  have hlogP := strictConcaveOn_log_Ioi.concaveOn.2 hapos hcpos hu hv huv
  simp only [smul_eq_mul, hbary] at hlogP
  have hlogS := hmhr.2.2 hsa hsc hu hv huv
  simp only [smul_eq_mul, hshift] at hlogS
  have hlogRa : Real.log (postedRevenue η x a) =
      Real.log a + Real.log (survival η (a - x)) :=
    Real.log_mul (ne_of_gt hapos) (ne_of_gt hsa)
  have hlogRb : Real.log (postedRevenue η x b) =
      Real.log b + Real.log (survival η (b - x)) :=
    Real.log_mul (ne_of_gt hbpos) (ne_of_gt hsb)
  have hlogRc : Real.log (postedRevenue η x c) =
      Real.log c + Real.log (survival η (c - x)) :=
    Real.log_mul (ne_of_gt hcpos) (ne_of_gt hsc)
  have hlogR : u * Real.log (postedRevenue η x a) +
      v * Real.log (postedRevenue η x c) ≤ Real.log (postedRevenue η x b) := by
    rw [hlogRa, hlogRc, hlogRb]
    nlinarith only [hlogP, hlogS]
  have hma := Real.log_le_log hmpos (min_le_left (postedRevenue η x a) (postedRevenue η x c))
  have hmc := Real.log_le_log hmpos (min_le_right (postedRevenue η x a) (postedRevenue η x c))
  apply (Real.log_le_log_iff hmpos (mul_pos hbpos hsb)).mp
  calc
    Real.log (min (postedRevenue η x a) (postedRevenue η x c)) =
        u * Real.log (min (postedRevenue η x a) (postedRevenue η x c)) +
        v * Real.log (min (postedRevenue η x a) (postedRevenue η x c)) := by
          rw [← add_mul, huv, one_mul]
    _ ≤ u * Real.log (postedRevenue η x a) + v * Real.log (postedRevenue η x c) :=
      add_le_add (mul_le_mul_of_nonneg_left hma hu) (mul_le_mul_of_nonneg_left hmc hv)
    _ ≤ Real.log (postedRevenue η x b) := hlogR

private lemma seg_block_upperSemicontinuousOn {n : ℕ} (η : Measure ℝ)
    [IsProbabilityMeasure η] (μ w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    UpperSemicontinuousOn (blockRevenue η μ w 0 n) (Ici 0) := by
  unfold blockRevenue
  apply upperSemicontinuousOn_sum
  intro i hi
  have hc : Continuous (fun r : ℝ => w i * r) := by fun_prop
  have hm : Monotone (fun r : ℝ => w i * r) :=
    fun a b hab => mul_le_mul_of_nonneg_left hab (hw i)
  exact hc.comp_upperSemicontinuousOn (seg_posted_upperSemicontinuousOn η (μ i)) hm

theorem solution {n : ℕ}
    (η : MeasureTheory.Measure ℝ) (hnoise : ValidNoise η) (hmhr : HasMHR η)
    (μ w : Fin n → ℝ) (hmarket : ValidFiniteMarket μ w)
    (L U : ℝ)
    (hbounds : ∀ i, L ≤ singlePrice η (μ i) ∧ singlePrice η (μ i) ≤ U) :
    ∃ p : ℝ, 0 ≤ p ∧ L ≤ p ∧ p ≤ U ∧
      ∀ q : ℝ, 0 ≤ q →
        blockRevenue η μ w 0 n q ≤ blockRevenue η μ w 0 n p := by
  letI : IsProbabilityMeasure η := hnoise.1
  have hopt (i : Fin n) : IsOptimalPrice η (μ i) (singlePrice η (μ i)) :=
    (singlePrice_attains η hnoise (μ i) (hmarket.2.2.1 i)).1.1
  have hw (i : Fin n) : 0 ≤ w i := (hmarket.2.2.2.1 i).le
  let i₀ : Fin n := ⟨0, hmarket.1⟩
  let A : ℝ := max 0 L
  have hA0 : 0 ≤ A := le_max_left _ _
  have hAL : L ≤ A := le_max_right _ _
  have hApi (i : Fin n) : A ≤ singlePrice η (μ i) :=
    max_le (hopt i).1 (hbounds i).1
  have hAU : A ≤ U := (hApi i₀).trans (hbounds i₀).2
  have hsc : UpperSemicontinuousOn (blockRevenue η μ w 0 n) (Icc A U) :=
    (seg_block_upperSemicontinuousOn η μ w hw).mono (fun q hq => hA0.trans hq.1)
  obtain ⟨p, hp, hmax⟩ := hsc.exists_isMaxOn (nonempty_Icc.mpr hAU) isCompact_Icc
  refine ⟨p, hA0.trans hp.1, hAL.trans hp.1, hp.2, ?_⟩
  intro q hq
  by_cases hqA : q < A
  · have hclip : blockRevenue η μ w 0 n q ≤ blockRevenue η μ w 0 n A := by
      unfold blockRevenue
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have h := seg_revenue_three_point η hmhr (μ i) q A (singlePrice η (μ i))
        hq hqA.le (hApi i)
      simpa only [min_eq_left ((hopt i).2 q hq)] using h
    exact hclip.trans (hmax ⟨le_rfl, hAU⟩)
  by_cases hqU : U < q
  · have hclip : blockRevenue η μ w 0 n q ≤ blockRevenue η μ w 0 n U := by
      unfold blockRevenue
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have h := seg_revenue_three_point η hmhr (μ i) (singlePrice η (μ i)) U q
        (hopt i).1 (hbounds i).2 hqU.le
      simpa only [min_eq_right ((hopt i).2 q hq)] using h
    exact hclip.trans (hmax ⟨hAU, le_rfl⟩)
  exact hmax ⟨le_of_not_gt hqA, le_of_not_gt hqU⟩

