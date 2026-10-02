-- Prove2me | solution 1 for DualSSD.Duality.pQuantile_set_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:04:36.687789+00:00
-- url     : https://prove2.me/submissions/3192f208-4f60-43fe-8ede-9ee776001052

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_secondQuantile

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology in
/-- `P{X < q}` is the left limit of the cdf of the law of `X`. -/
theorem pq1b_lt_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEMeasurable X P) (q : ℝ) :
    P.real {ω | X ω < q} = Function.leftLim (cdf (P.map X)) q := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  have h1 : P.real {ω | X ω < q} = (P.map X).real (Iio q) := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hX measurableSet_Iio]
    rfl
  have hm := StieltjesFunction.measure_Iio (f := cdf (P.map X)) (tendsto_cdf_atBot (P.map X)) q
  rw [measure_cdf] at hm
  rw [h1, measureReal_def, hm, sub_zero]
  apply ENNReal.toReal_ofReal
  exact le_trans (cdf_nonneg (P.map X) (q - 1))
    (Monotone.le_leftLim (monotone_cdf (P.map X)) (by linarith))

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem pq1b_le_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEMeasurable X P) (q : ℝ) :
    P.real {ω | X ω ≤ q} = cdf (P.map X) q := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  rw [cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

open Set Filter Topology in
/-- Pure order-theoretic core: for a monotone, right-continuous `F` with limits `0` and `1`,
the set `{q | leftLim F q ≤ p ≤ F q}` is a closed interval with left end `sInf {p ≤ F}`. -/
theorem pq1b_core (F : ℝ → ℝ) (hmono : Monotone F)
    (hrc : ∀ x, ContinuousWithinAt F (Ici x) x)
    (hbot : Tendsto F atBot (𝓝 0)) (htop : Tendsto F atTop (𝓝 1))
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ b : ℝ, sInf {η : ℝ | p ≤ F η} ≤ b ∧
      {q : ℝ | Function.leftLim F q ≤ p ∧ p ≤ F q} = Icc (sInf {η : ℝ | p ≤ F η}) b := by
  set a := sInf {η : ℝ | p ≤ F η} with ha
  -- the upper set `{p ≤ F}` is `Ici a`
  have hUne : ({η : ℝ | p ≤ F η} : Set ℝ).Nonempty := by
    obtain ⟨x, hx⟩ := (htop.eventually (lt_mem_nhds hp1)).exists
    exact ⟨x, hx.le⟩
  have hUbdd : BddBelow ({η : ℝ | p ≤ F η} : Set ℝ) := by
    have h := hbot.eventually (gt_mem_nhds hp0)
    rw [Filter.eventually_atBot] at h
    obtain ⟨x0, hx0⟩ := h
    refine ⟨x0, fun x hx => ?_⟩
    by_contra hlt
    exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)
  have hpFa : p ≤ F a := by
    have ht : Tendsto F (𝓝[>] a) (𝓝 (F a)) := (hrc a).mono Ioi_subset_Ici_self
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hUne hx
    exact le_trans hs (hmono hsx.le)
  have hA : ∀ x, p ≤ F x ↔ a ≤ x := fun x =>
    ⟨fun h => csInf_le hUbdd h, fun h => le_trans hpFa (hmono h)⟩
  -- left limit bound
  have hL : ∀ q, (∀ r < q, F r ≤ p) → Function.leftLim F q ≤ p := by
    intro q hq
    rw [Monotone.leftLim_eq_sSup hmono]
    apply csSup_le (Set.Nonempty.image _ ⟨q - 1, by simp⟩)
    rintro _ ⟨r, hr, rfl⟩
    exact hq r hr
  set T := {q : ℝ | Function.leftLim F q ≤ p} with hT
  have hTne : T.Nonempty := by
    have h := hbot.eventually (gt_mem_nhds hp0)
    obtain ⟨x, hx⟩ := h.exists
    exact ⟨x, le_trans (Monotone.leftLim_le hmono le_rfl) hx.le⟩
  have hTbdd : BddAbove T := by
    obtain ⟨M, hM⟩ := (htop.eventually (lt_mem_nhds hp1)).exists
    refine ⟨M, fun q hq => ?_⟩
    by_contra hlt
    have : F M ≤ Function.leftLim F q := Monotone.le_leftLim hmono (not_le.mp hlt)
    have hq' : Function.leftLim F q ≤ p := hq
    linarith
  set b := sSup T with hb
  have hB : ∀ q, Function.leftLim F q ≤ p ↔ q ≤ b := by
    intro q
    constructor
    · intro h; exact le_csSup hTbdd h
    · intro h
      apply hL
      intro r hr
      obtain ⟨t, ht, hrt⟩ := exists_lt_of_lt_csSup hTne (lt_of_lt_of_le hr h)
      exact le_trans (Monotone.le_leftLim hmono hrt) ht
  have hab : a ≤ b := by
    rw [← hB]
    apply hL
    intro r hr
    by_contra hc
    exact absurd ((hA r).mp (not_le.mp hc).le) (not_le.mpr hr)
  refine ⟨b, hab, ?_⟩
  ext q
  simp only [mem_ofPred_eq, mem_Icc]
  rw [hA, hB]
  exact And.comm

open MeasureTheory ProbabilityTheory DualSSD DualSSD.Duality in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ b : ℝ, leftQuantile P X p ≤ b ∧
      {q : ℝ | IsPQuantile P X p q} = Set.Icc (leftQuantile P X p) b := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  have hLQ : leftQuantile P X p = sInf {η : ℝ | p ≤ cdf (P.map X) η} := by
    rw [leftQuantile]
    congr 1
    ext η
    simp only [Set.mem_ofPred_eq]
    rw [Shared.distFun, pq1b_le_eq P X hX η]
  have hS : {q : ℝ | IsPQuantile P X p q} =
      {q : ℝ | Function.leftLim (cdf (P.map X)) q ≤ p ∧ p ≤ cdf (P.map X) q} := by
    ext q
    simp only [Set.mem_ofPred_eq, IsPQuantile]
    rw [pq1b_lt_eq P X hX q, pq1b_le_eq P X hX q]
  rw [hLQ, hS]
  exact pq1b_core (cdf (P.map X)) (monotone_cdf (P.map X))
    (fun x => (cdf (P.map X)).right_continuous x)
    (tendsto_cdf_atBot (P.map X)) (tendsto_cdf_atTop (P.map X)) p hp.1 hp.2
